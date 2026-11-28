#!/usr/bin/env python3
"""Exclude all four scalar EB/ED families, including the shrinking edge.

Ten exported UNSAT formulas require independent RUP replay. The
relative short-edge theorem supplies the normalized virtual direction.
"""

import argparse
from itertools import combinations
import json
from pathlib import Path
import time

import sympy as S

import remaining_c1_flat_positive_stretch as positive
import remaining_c1_short_edges as short_edges
import solver_remaining_c1_flat_stretch as old_stretch
import solver_remaining_c1_collinear as trits
import solver_remaining_chambers as shared
from solver_chambers import write_cnf
from solver_sat import FastSAT

A, B, L = positive.A, positive.B, positive.X
HALF = S.Rational(1, 2)
NORMALS, NORMAL_VERTICES = positive.NORMALS, positive.NORMAL_VERTICES
QUADS, QUAD_INDEX = positive.QUADS, positive.QUAD_INDEX


def scalar_families():
    cases = (
        ('B', HALF, L, 1, S.Integer(0), HALF, 1-L),
        ('Dplus', L, HALF-L, -1, HALF-L, (1-2*(1-A)*L)/(2*A), HALF+L),
        ('Dminus', L, HALF-L, -1, HALF, -1/(2*A), HALF),
    )
    names = {('B', 0): 'EB', ('Dplus', 0): 'ED_positive',
             ('Dminus', 2): 'ED_negative_opposite', ('Dminus', 3): 'ED_negative_same'}
    families, rejected = {}, []
    for case, k, ell, lower_direction, h0, p3, outer_sum in cases:
        for kind in range(4):
            h5, h4, rho5 = positive.pair_data(kind, HALF, ell, B)
            difference = S.factor(h4+h5-outer_sum)
            sign = positive.coefficient_sign(difference)
            assert sign is not None
            if sign:
                rejected.append({'anchor_case': case, 'pair_type': kind,
                                 'budget_difference': str(difference), 'strict_sign': sign})
                continue
            assert difference == 0
            radius_sign = -1 if kind in (0, 1) else 1
            relative_direction = 1 if kind in (0, 2) else -1
            epsilon = lower_direction*relative_direction
            weights = [h0, HALF, 0, HALF, h4, h5, ell, k]
            p6 = k-lower_direction*ell
            original = [S.Integer(0), S.Integer(0), p3, p3, p3+epsilon*HALF,
                        B*p3+(1-B)*p6+epsilon*radius_sign*rho5, p6, k]
            assert S.cancel(sum(weights)-S.Rational(5, 2)) == 0
            horizontal = positive.metric.horizontal_displacements(weights)
            residuals = S.Matrix([(original[j]-original[i])**2-horizontal[i, j]**2
                                  for i, j in positive.source_metric.EDGES]+[0]*5)
            stresses = positive.source_metric.closed_c1_rows().subs(
                {positive.source_metric.A: A/2, positive.source_metric.B: -B/2})
            assert all(S.cancel(value) == 0 for value in stresses*residuals)
            families[names[case, kind]] = {'anchor_case': case, 'pair_type': kind,
                                         'weights': weights, 'points': original,
                                         'epsilon': epsilon, 'radius_sign': radius_sign}
    assert len(families) == 4 and len(rejected) == 8
    return families, rejected


def geometry(family):
    original = family['points']
    # P3 has a nonzero limit in each of the four families, so it fixes
    # the normal gauge N0=N1=N3=0 without dividing by a shrinking edge.
    coefficient = S.expand(original[3]).coeff(A, -1)
    levels = (0, A, 1, 1, 1, B, 0, 0)
    x = [S.cancel(2*point-2*coefficient*height/A)
         for point, height in zip(original, levels)]
    assert all(S.denom(value) == 1 and A not in value.free_symbols for value in x)
    transform = S.Matrix([[2, 0, -4*coefficient/A], [0, 1, 0], [0, 0, 2]])
    assert transform.det() == 4
    normals = dict(zip(NORMAL_VERTICES, NORMALS))
    points = [S.Matrix([x[i], normals.get(i, 0), levels[i]]) for i in range(8)]
    rows = []
    for quad in QUADS:
        determinant = S.expand(S.det(S.Matrix.hstack(*(points[i]-points[quad[0]] for i in quad[1:]))))
        row = tuple(determinant.coeff(normal) for normal in NORMALS)
        assert S.expand(determinant-sum(value*normal for value, normal in zip(row, NORMALS))) == 0
        rows.append(row)

    def area(i, j, k):
        return S.expand((x[j]-x[i])*(levels[k]-levels[i])-(x[k]-x[i])*(levels[j]-levels[i]))

    relations = []
    for i, j in combinations(range(8), 2):
        for a, b, c in combinations([v for v in range(8) if v not in (i, j)], 3):
            relation = (((i, j, a, b), area(i, j, c)),
                        ((i, j, a, c), -area(i, j, b)),
                        ((i, j, b, c), area(i, j, a)))
            for column in range(len(NORMALS)):
                assert S.expand(sum(value*old_stretch.parity(quad)
                                    *rows[QUAD_INDEX[tuple(sorted(quad))]][column]
                                    for quad, value in relation)) == 0
            relations.append(relation)
    assert len(rows) == 70 and len(relations) == 560
    return x, rows, relations


class NormalModel(trits.ActualBracketModel):
    def __init__(self, family):
        x, rows, relations = geometry(family)
        self.n, base, *_ = shared.base_formula()
        self.clauses = [list(row) for row in base]
        self.trits = {}
        for high in ({2, 3, 4}, {1, 2, 3, 4, 5}):
            for support in combinations(range(8), 5):
                if set(support) <= high or not set(support) & high:
                    continue
                row = [(1 if vertex in high else -1)*(-1)**i
                       *shared.common.lit(support[:i]+support[i+1:])
                       for i, vertex in enumerate(support)]
                self.clauses.extend((row, [-value for value in row]))
        for index, quad in enumerate(QUADS):
            bits = self.new_trit()
            self.trits[quad] = bits
            self.clauses.extend(([-bits[0], index+1], [-bits[1], -index-1]))
        self.normal_bits = [self.new_trit() for _ in NORMALS]
        self.clauses.append([bit for pair in self.normal_bits for bit in pair])
        for support in combinations(range(8), 5):
            self.sumzero([self.bits(support[:i]+support[i+1:], (-1)**i) for i in range(5)])
        omitted = 0
        for quad, row in zip(QUADS, rows):
            signs = tuple(positive.coefficient_sign(value) for value in row)
            if None in signs:
                omitted += 1
                continue
            self.sumzero([self.bits(quad, -1)]+[
                pair if sign > 0 else pair[::-1]
                for pair, sign in zip(self.normal_bits, signs) if sign])
        for relation in relations:
            signs = tuple(positive.coefficient_sign(value) for _, value in relation)
            if None in signs:
                omitted += 1
                continue
            self.sumzero([self.bits(quad, sign) for (quad, _), sign in zip(relation, signs) if sign])
        self.record = {'transformed_horizontal': list(map(str, x)),
                       'omitted_variable_sign_relations': omitted}


def virtual_model(family, horizontal):
    """Normalize 23 independently of the macro normal width."""
    assert horizontal in (-1, 0, 1)
    model = NormalModel(family)
    # The separately exported macro certificate proves N2=0. Retain
    # that necessary premise explicitly before normalizing the edge.
    model.clauses.extend(([-model.normal_bits[0][0]], [-model.normal_bits[0][1]]))
    x, _, _ = geometry(family)
    levels = (0, A, 1, 1, 1, B, 0, 0)
    normals = dict(zip(NORMAL_VERTICES, NORMALS))
    normals[2] = S.Integer(0)
    points = [S.Matrix([x[i], normals.get(i, 0), levels[i]]) for i in range(8)]
    virtual_y, edge, t, axial = S.symbols('virtual_y edge t axial')
    points[2] = points[3]+edge*S.Matrix([horizontal, virtual_y, t*axial])
    virtual_bits = model.new_trit()
    variables = list(NORMALS)+[virtual_y]
    bits = model.normal_bits+[virtual_bits]
    records = []
    for quad in QUADS:
        if not {2, 3} <= set(quad):
            continue
        divided = S.cancel(S.det(S.Matrix.hstack(*(points[i]-points[quad[0]]
                                                   for i in quad[1:])))/edge)
        assert edge not in divided.free_symbols
        determinant = S.expand(divided.subs(t, 0))
        coefficients = tuple(determinant.coeff(variable) for variable in variables)
        assert S.expand(determinant-sum(value*variable
                                        for value, variable in zip(coefficients, variables))) == 0
        signs = tuple(positive.coefficient_sign(value) for value in coefficients)
        assert None not in signs
        actual = model.new_trit()
        literal = shared.common.lit(quad)
        model.clauses.extend(([-actual[0], literal], [-actual[1], -literal]))
        model.sumzero([actual[::-1]]+[
            pair if sign > 0 else pair[::-1] for pair, sign in zip(bits, signs) if sign])
        records.append({'quad': quad, 'coefficients': list(map(str, coefficients))})
    assert len(records) == 15
    if horizontal == 0:
        model.clauses.append(list(virtual_bits))
    return model, records


def build(directory):
    started = time.monotonic()
    directory.mkdir(parents=True, exist_ok=True)
    pair_checks = positive.scalar_checks()
    relative_checks = short_edges.relative_metric_checks()
    families, rejected = scalar_families()
    records, obligations = [], []
    for name, family in families.items():
        model = NormalModel(family)
        direct = name in ('ED_positive', 'ED_negative_same')
        if direct:
            with FastSAT(model.n, model.clauses) as solver:
                assert solver.check() == -1, name
            filename = f'c1_single_scalar_{name}.cnf'
            write_cnf(directory/filename, model.n, model.clauses)
            obligations.append({'file': filename, 'family': name,
                                'variables': model.n, 'clauses': len(model.clauses)})
        else:
            zero_clauses = model.clauses+[list(model.normal_bits[0])]
            with FastSAT(model.n, zero_clauses) as solver:
                assert solver.check() == -1
            filename = f'c1_single_scalar_{name}_N2_zero.cnf'
            write_cnf(directory/filename, model.n, zero_clauses)
            obligations.append({'file': filename, 'family': name, 'claim': 'N2=0',
                                'variables': model.n, 'clauses': len(zero_clauses)})
            for horizontal in (-1, 0, 1):
                virtual, exact_rows = virtual_model(family, horizontal)
                with FastSAT(virtual.n, virtual.clauses) as solver:
                    assert solver.check() == -1
                filename = f'c1_single_scalar_{name}_virtual_{horizontal}.cnf'
                write_cnf(directory/filename, virtual.n, virtual.clauses)
                obligations.append({'file': filename, 'family': name,
                                    'virtual_horizontal': horizontal,
                                    'variables': virtual.n, 'clauses': len(virtual.clauses),
                                    'exact_virtual_coefficients': exact_rows})
        records.append({'family': name, 'anchor_case': family['anchor_case'],
                        'pair_type': family['pair_type'],
                        'weights': list(map(str, family['weights'])),
                        'points': list(map(str, family['points'])),
                        'normal_stretch_excluded': True, 'direct_normal_exclusion': direct,
                        **model.record})
    packet = {'domain': 'ray2 C1; EB or ED; common line; interior heights and strict lower cap order',
              'pair_scalar_source_checks': pair_checks,
              'relative_short_edge_source': relative_checks, 'scalar_cases': 12,
              'strict_budget_exclusions': rejected, 'four_families': records,
              'source_checks_per_family': {'closed_projected_stresses': 12,
                                           'normal_determinants': 70, 'projected_relations': 560},
              'unsat_obligations': obligations, 'remaining_families': [],
              'relative_rate_assumptions': [], 'seconds': time.monotonic()-started}
    (directory/'c1_single_zero_scalar.json').write_text(json.dumps(packet, indent=2)+'\n')
    return packet


if __name__ == '__main__':
    if not __debug__:
        raise RuntimeError('run with assertions enabled')
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('output', type=Path)
    result = build(parser.parse_args().output)
    print(json.dumps({'scalar_families': 4, 'normal_stretch_exclusions': 4,
                      'remaining_families': result['remaining_families'],
                      'seconds': result['seconds']}))
