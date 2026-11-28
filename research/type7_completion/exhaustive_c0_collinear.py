#!/usr/bin/env python3
"""Zero-safe C0 boundary implications and one height-order extension.

Usage: python exhaustive_c0_collinear.py OUTPUT_DIRECTORY

All six generated CNFs require independent RUP replay. The companion
combines them with the existing metric turning and height-order lemmas.
"""

import argparse
from itertools import combinations, product
import json
from pathlib import Path

import sympy as sym

import exhaustive_remaining_locus as locus
import solver_remaining_c1_collinear as trit_source
import solver_remaining_c1_geometry as geometry
import solver_remaining_chambers as shared
from solver_chambers import write_cnf
from solver_sat import FastSAT

QUADS = tuple(combinations(range(8), 4))
PAIRS = tuple(combinations(range(2, 8), 2))
CASES = {'3_between_1_2': (3, (1, 2)),
         '1_between_2_3': (1, (2, 3)),
         '1_equals_3': (3, (1,))}


def height_relations():
    u, v = sym.symbols('u v')
    p = [sym.zeros(2, 1), sym.zeros(2, 1)]
    p.extend(sym.Matrix(sym.symbols(f'x{i} y{i}')) for i in range(2, 8))
    z = (0, sym.Rational(1, 2), sym.Rational(1, 2), sym.Rational(1, 2), u, v, 0, 0)
    points = [point.col_join(sym.Matrix([height])) for point, height in zip(p, z)]
    variables = sym.symbols('C0:15')

    def cross(i, j):
        if i == j or min(i, j) < 2:
            return sym.Integer(0)
        return (1 if i < j else -1)*variables[PAIRS.index(tuple(sorted((i, j))))]

    def origin(i, j, k):
        return z[i]*cross(j, k)-z[j]*cross(i, k)+z[k]*cross(i, j)

    def bracket(quad):
        first, *rest = quad
        return sym.Matrix.hstack(*(points[i]-points[first] for i in rest)).det()

    relations = []
    for quad in QUADS:
        i, j, k, l = quad
        expression = sym.expand(origin(j, k, l)-origin(i, k, l)+origin(i, j, l)-origin(i, j, k))
        coefficients = [sym.expand(2*expression.coeff(variable)) for variable in variables]
        assert sym.expand(bracket(quad)-sum(c*bracket((0, 1)+pair) for c, pair in zip(coefficients, PAIRS))) == 0
        if quad[:2] == (0, 1):
            continue  # An anchor expressed in itself adds no information.
        signs = []
        for coefficient in coefficients:
            assert sym.Poly(coefficient, u, v).total_degree() <= 1
            corners = [coefficient.subs({u: a, v: b})
                       for a, b in product((0, sym.Rational(1, 2)), repeat=2)]
            if all(value == 0 for value in corners):
                signs.append(0)
            elif all(value >= 0 for value in corners):
                signs.append(1)
            elif all(value <= 0 for value in corners):
                signs.append(-1)
            else:
                signs.append(None)
        # Nonzero affine forms with one weak sign at all four corners
        # have that strict sign throughout the open height square.
        if None not in signs:
            relations.append((quad, tuple((pair, sign) for pair, sign in zip(PAIRS, signs) if sign)))
    assert len(relations) == 49

    lower_cross = sym.Matrix.hstack(p[6], p[7]).det()
    for vector, first, second in ((p[2], (0, 1, 2, 6), (0, 1, 2, 7)),
                                  (p[3]-p[2], (0, 2, 3, 6), (0, 2, 3, 7)),
                                  (p[3], (0, 1, 3, 6), (0, 1, 3, 7))):
        a, b = sym.Matrix.hstack(vector, p[6]).det(), sym.Matrix.hstack(vector, p[7]).det()
        assert sym.expand(2*bracket(first)-a) == 0
        assert sym.expand(2*bracket(second)-b) == 0
        assert all(sym.expand(value) == 0 for value in a*p[7]-b*p[6]+lower_cross*vector)
    return tuple(relations)


class ActualModel(trit_source.ActualBracketModel):
    def __init__(self, case, orientation, relations):
        assert orientation in (-1, 1)
        middle, parents = CASES[case]
        self.n, base, *_ = shared.base_formula()
        self.clauses = [list(row) for row in base]
        self.trits = {}
        for high in ({1, 2, 3}, {1, 2, 3, 4, 5}):
            for support in combinations(range(8), 5):
                if set(support) <= high or not set(support) & high:
                    continue
                row = [(1 if vertex in high else -1)*(-1)**i
                       *shared.common.lit(support[:i]+support[i+1:])
                       for i, vertex in enumerate(support)]
                self.clauses.extend((row, [-literal for literal in row]))
        for index, quad in enumerate(QUADS):
            positive, negative = self.new_trit()
            self.trits[quad] = positive, negative
            self.clauses.extend(([-positive, index+1], [-negative, -index-1]))
        for support in combinations(range(8), 5):
            self.sumzero([self.bits(support[:i]+support[i+1:], (-1)**i) for i in range(5)])
        for quad in QUADS:
            if middle in quad:
                forms = [self.bits(tuple(parent if vertex == middle else vertex for vertex in quad))
                         for parent in parents]
                self.sumzero(forms+[self.bits(quad, -1)])
        for vertex in range(8):
            if vertex not in (0, 6, 7):
                self.clauses.append([self.bits((0, 6, 7, vertex), orientation)[0]])
        self.add_weak_gp()
        rank_pairs = [((0, 1, 2, 6), (0, 1, 2, 7)),
                      ((0, 2, 3, 6), (0, 2, 3, 7))]
        if case != '1_equals_3':
            rank_pairs.append(((0, 1, 3, 6), (0, 1, 3, 7)))
        for first, second in rank_pairs:
            self.clauses.append(list(self.bits(first))+list(self.bits(second)))
        for quad, terms in relations:
            self.sumzero([self.bits(quad)] + [self.bits((0, 1)+pair, -sign) for pair, sign in terms])


def symmetry_checks():
    u, v = sym.symbols('u v')
    values = (0, sym.Rational(1, 2), sym.Rational(1, 2), sym.Rational(1, 2), 1-u, -v, 0, 0)
    levels = (0, sym.Rational(1, 2), sym.Rational(1, 2), sym.Rational(1, 2), u, v, 0, 0)
    permutation = tuple((1-i) % 8 for i in range(8))
    new_u, new_v = sym.Rational(1, 2)-v, sym.Rational(1, 2)-u
    expected = (0, sym.Rational(1, 2), sym.Rational(1, 2), sym.Rational(1, 2), 1-new_u, -new_v, 0, 0)
    expected_spatial = (0, sym.Rational(1, 2), sym.Rational(1, 2), sym.Rational(1, 2), new_u, new_v, 0, 0)
    weights = tuple((-i) % 8 for i in range(8))
    h = sym.symbols('h0:8')
    original_x = geometry.horizontal_displacements(h)
    new_x = geometry.horizontal_displacements([h[i] for i in weights])
    for mark in (1, 2):
        record = next(row for row in locus.marked_dihedral_gauges(mark)
                      if row['sign'] == -1 and row['rotation'] == 1)
        transformed = [-values[permutation[i]]+values[permutation[0]]+record['gauge'][i][1]
                       for i in range(8)]
        assert all(sym.expand(a-b) == 0 for a, b in zip(transformed, expected))
        for (i, j), value in new_x.items():
            a, b = permutation[i], permutation[j]
            actual = original_x[a, b] if a < b else -original_x[b, a]
            assert sym.expand(value+actual) == 0
    assert all(sym.expand(levels[permutation[0]]-levels[permutation[i]]-expected_spatial[i]) == 0
               for i in range(8))
    assert weights[1] == 7 and weights[2] == 6
    return {'permutation': permutation, 'weight_indices': weights,
            'new_u': str(new_u), 'new_v': str(new_v), 'marked_cocycles_checked': 2}


def build(directory):
    directory.mkdir(parents=True, exist_ok=True)
    trit_source.symbolic_checks()
    relations = height_relations()
    symmetry = symmetry_checks()
    obligations = []

    def export(name, source, clauses, claim):
        with FastSAT(source.n, clauses) as solver:
            assert solver.check() == -1
        write_cnf(directory/name, source.n, clauses)
        obligations.append({'file': name, 'claim': claim, 'variables': source.n, 'clauses': len(clauses)})

    for case in CASES:
        source = ActualModel(case, 1, relations)
        violation = [source.bits(quad)[0] for quad in ((0, 1, 2, 7), (3, 4, 5, 6))]
        export(f'c0_collinear_{case}_positive_signs.cnf', source, source.clauses+[violation],
               'positive067 implies actual0127<=0 and3456<=0')
        if case != '1_equals_3':
            source = ActualModel(case, -1, relations)
            export(f'c0_collinear_{case}_negative_cap.cnf', source, source.clauses,
                   'strict upper line order excludes negative067')
    source = ActualModel('1_between_2_3', 1, relations)
    extra = [[source.bits((2, 3, 6, 7))[0]], [source.bits((1, 2, 6, 7))[1]],
             [-source.bits((0, 2, 3, 7))[1]],
             [source.bits((2, 3, 4, 5))[0], source.bits((4, 5, 6, 7))[0]]]
    export('c0_collinear_1_between_2_3_mixed_signs.cnf', source, source.clauses+extra,
           'actual2367>0,1267<0,0237>=0 imply actual2345<=0 and4567<=0')
    assert len(obligations) == 6
    packet = {'global_open_height_relations': len(relations), 'symmetry': symmetry,
              'unsat_obligations': obligations,
              'boundary_exclusion_after_metric_and_independent_replay':
                  'ray1 0<v<=u<1/2: upper d2=0<d1 with regular067; or lower d6=0<d7 with regular123',
              'whole_one_collinear_boundary_excluded': False}
    (directory/'collinear.json').write_text(json.dumps(packet, indent=2)+'\n')
    return packet


if __name__ == '__main__':
    if not __debug__:
        raise RuntimeError('run with assertions enabled')
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('output', type=Path)
    result = build(parser.parse_args().output)
    print(json.dumps({'height_relations': result['global_open_height_relations'],
                      'unsat_obligations': len(result['unsat_obligations']),
                      'whole_one_collinear_boundary_excluded': False}), flush=True)
