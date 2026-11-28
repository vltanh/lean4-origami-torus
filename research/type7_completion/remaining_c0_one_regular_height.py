#!/usr/bin/env python3
"""Exclude ray-1 C0 at u=1/2 when the lower cap is regular.

The regular-upper case is inherited. Five actual-trit obligations and
the closed metric turning inequality exclude every collinear upper cap.
All exported CNFs require independent RUP replay.
"""

import argparse
from itertools import combinations
import json
from pathlib import Path
import time

import sympy as s

import exhaustive_c0_collinear as boundary
import exhaustive_c0_turning as turning
import remaining_c0_height_order as angles
import solver_remaining_c1_geometry as geometry
import solver_remaining_chambers as shared
import solver_remaining_limit as reduction
from solver_remaining_c1_collinear import ActualBracketModel, symbolic_checks as trit_checks
from solver_chambers import write_cnf
from solver_sat import FastSAT

HALF = s.Rational(1, 2)
QUADS = tuple(combinations(range(8), 4))
PAIRS = tuple(combinations(range(2, 8), 2))
CASES = ('strict_stem', 'coincident_stem')


def height_relations():
    beta = s.Symbol('beta')
    levels = (0, 1, 1, 1, 1, beta, 0, 0)
    planar = [s.zeros(2, 1), s.zeros(2, 1)]
    planar += [s.Matrix(s.symbols(f'x{i} y{i}')) for i in range(2, 8)]
    points = [p.col_join(s.Matrix([z])) for p, z in zip(planar, levels)]
    variables = s.symbols('C0:15')

    def cross(i, j):
        if i == j or min(i, j) < 2:
            return s.Integer(0)
        return (1 if i < j else -1) * variables[PAIRS.index(tuple(sorted((i, j))))]

    def origin(i, j, k):
        return levels[i]*cross(j, k)-levels[j]*cross(i, k)+levels[k]*cross(i, j)

    def bracket(q):
        return s.det(s.Matrix.hstack(*(points[i]-points[q[0]] for i in q[1:])))

    rows = []
    for q in QUADS:
        i, j, k, l = q
        expression = s.expand(origin(j, k, l)-origin(i, k, l)
                              +origin(i, j, l)-origin(i, j, k))
        coefficients = [expression.coeff(variable) for variable in variables]
        assert s.expand(bracket(q)-sum(c*bracket((0, 1)+pair)
                        for c, pair in zip(coefficients, PAIRS))) == 0
        signs = []
        for coefficient in coefficients:
            assert s.Poly(coefficient, beta).degree() <= 1
            endpoints = [coefficient.subs(beta, value) for value in (0, 1)]
            assert all(value >= 0 for value in endpoints) or all(value <= 0 for value in endpoints)
            signs.append(1 if any(value > 0 for value in endpoints)
                         else -1 if any(value < 0 for value in endpoints) else 0)
        if q[:2] != (0, 1):
            rows.append((q, tuple((pair, sign) for pair, sign in zip(PAIRS, signs) if sign)))
    assert len(rows) == 55
    return tuple(rows)


class HeightModel(ActualBracketModel):
    def __init__(self, stem, coincident4, relations):
        assert stem in CASES
        self.n, base, *_ = shared.base_formula()
        assert base[0] == [1]
        # The lower cap fixes orientation. The upper cap is collinear;
        # its generic completion is not fixed by its limiting zero area.
        self.clauses = [list(row) for row in base[1:]]
        self.trits = {}
        for high in ({1, 2, 3, 4}, {1, 2, 3, 4, 5}):
            for support in combinations(range(8), 5):
                if set(support) <= high or not set(support) & high:
                    continue
                row = [(1 if vertex in high else -1)*(-1)**i
                       *shared.common.lit(support[:i]+support[i+1:])
                       for i, vertex in enumerate(support)]
                self.clauses.extend((row, [-value for value in row]))
        for index, quad in enumerate(QUADS):
            positive, negative = self.new_trit()
            self.trits[quad] = positive, negative
            self.clauses.extend(([-positive, index+1], [-negative, -index-1]))
        for support in combinations(range(8), 5):
            self.sumzero([self.bits(support[:i]+support[i+1:], (-1)**i)
                          for i in range(5)])
        for vertex in (1, 2, 3, 4, 5):
            self.clauses.append([self.bits((0, 6, 7, vertex))[0]])
        positions = [(1, (3, 4))] if stem == 'strict_stem' else [(3, (1,))]
        positions.append((4, (2,) if coincident4 else (1, 2)))
        for middle, parents in positions:
            for quad in QUADS:
                if middle in quad:
                    self.sumzero([self.bits(tuple(parent if vertex == middle else vertex for vertex in quad))
                                  for parent in parents]+[self.bits(quad, -1)])
        self.add_weak_gp()
        for quad, terms in relations:
            self.sumzero([self.bits(quad, -1)]+[self.bits((0, 1)+pair, sign)
                                             for pair, sign in terms])
        # A nonzero P2 cannot have zero cross product with both independent
        # lower-cap vectors. The exact two-dimensional identity is checked.
        self.clauses.append(list(self.bits((0, 1, 2, 6)))+list(self.bits((0, 1, 2, 7))))


def metric_checks():
    v = s.Symbol('v')
    original = reduction.original_system((HALF, HALF, HALF, HALF, -v, 0))
    rows = []
    for edge in ((0, 6), (0, 7), (1, 2), (1, 3), (2, 3), (3, 4), (6, 7)):
        rows.append([s.Integer(edge == other) for other in reduction.EDGES]+[s.Integer(0)]*5)
    row = [s.Integer(0)]*29
    row[reduction.EDGES.index((2, 4))] = 1-2*v
    row[25] = -1
    rows.append(row)
    rows.append([s.Integer(edge == (0, 1))-s.Integer(edge == (0, 2))
                 -s.Integer(edge == (1, 7))+s.Integer(edge == (2, 7))
                 for edge in reduction.EDGES]+[s.Integer(0)]*5)
    assert not any(s.expand(value) for value in s.Matrix(rows)*original)
    d = list(s.symbols('d0:7'))
    d.append(HALF-sum(d))
    h = [HALF-value for value in d]
    X = geometry.horizontal_displacements(h)
    assert s.expand(X[2, 4]-d[2]-d[3]) == 0
    assert s.expand(h[2]+h[3]+d[2]+d[3]-1) == 0
    assert s.expand(HALF-d[1]-d[3]-sum(d[i] for i in (0, 2, 4, 5, 6, 7))) == 0
    # At the two surviving upper-line orders d2=0. The endpoint P4 is
    # a positive distance to the right of 1, even if d1=0.
    a, b, c = s.symbols('a b c')
    upper_points = {1: s.Matrix((0, 1)), 2: s.Matrix((a, 1)),
                    3: s.Matrix((-b, 1)), 4: s.Matrix((c, 1))}
    assert not any(s.expand(value) for value in
                   c*upper_points[3]+b*upper_points[4]-(b+c)*upper_points[1])
    assert not any(s.expand(value) for value in
                   (a-c)*upper_points[1]+c*upper_points[2]-a*upper_points[4])
    p2, p6, p7 = [s.Matrix(s.symbols(f'x{i} y{i}')) for i in (2, 6, 7)]
    cross = lambda p, q: s.det(s.Matrix.hstack(p, q))
    assert not any(s.expand(value) for value in
                   cross(p2, p6)*p7-cross(p2, p7)*p6+cross(p6, p7)*p2)
    # Bind the limiting section lists to the original face list.
    levels = (0, HALF, HALF, HALF, HALF, v, 0, 0)
    P = [s.zeros(2, 1), s.zeros(2, 1)]
    P += [s.Matrix(s.symbols(f'x{i} y{i}')) for i in range(2, 8)]
    cycles = (((0, 1), (0, 3), (0, 2), (2, 7), (1, 7), (1, 6)),
              ((3, 5), (2, 5), (4, 5), (4, 7), (4, 6), (3, 6)))
    expected = ((P[1], P[3], P[2], P[2], P[1], P[1]),
                (P[3], P[2], P[4], P[4], P[4], P[3]))
    faces = set(shared.base_formula()[2])
    height = s.Symbol('height')
    for cycle, limits in zip(cycles, expected):
        for index, ((i, j), target) in enumerate(zip(cycle, limits)):
            assert tuple(sorted(set((i, j)) | set(cycle[(index+1) % 6]))) in faces
            fraction = (height-levels[i])/(levels[j]-levels[i])
            point = (1-fraction)*P[i]+fraction*P[j]
            assert not any(s.cancel(value) for value in point.subs(height, HALF)-target)
    # The strict height-order Gram certificate already covers k,l in the
    # CLOSED unit square. At this edge k=0 and l=2v in (0,1).
    angle_checks = angles.verify()
    return {'closed_source_rows': len(rows), 'height_relations': 55,
            'equal_perimeter_triangles': True, 'positive_order_identities': 2,
            'section_face_and_limit_bindings': 12, 'rank_identity': True,
            'closed_angle_certificate': angle_checks,
            'cap_turning_identities': turning.verify(),
            'trit_identities': trit_checks(), 'reflection': boundary.symmetry_checks()}


def build(directory):
    directory.mkdir(parents=True, exist_ok=True)
    checks = metric_checks()
    relations = height_relations()
    obligations = []

    def export(name, model, clauses, claim):
        with FastSAT(model.n, clauses) as solver:
            assert solver.check() == -1, name
        write_cnf(directory/name, model.n, clauses)
        obligations.append({'file': name, 'variables': model.n,
                            'clauses': len(clauses), 'claim': claim})

    model = HeightModel('strict_stem', False, relations)
    export('c0_upper_height_strict_order.cnf', model, model.clauses,
           'P3< P1< P4< P2 is impossible with regular lower cap')
    for stem, coincident4 in (('strict_stem', True), ('coincident_stem', False)):
        model = HeightModel(stem, coincident4, relations)
        violation = [model.bits((0, 1, 2, 7))[0], model.bits((1, 2, 6, 7))[1]]
        export(f'c0_upper_height_{stem}_turn.cnf', model, model.clauses+[violation],
               'actual0127<=0 and actual1267>=0 contradict the strict metric turn')
    model = HeightModel('coincident_stem', True, relations)
    export('c0_upper_height_double_coincidence_core.cnf', model,
           model.clauses+[[model.bits((0, 1, 2, 7))[0]]], 'actual0127<=0')
    turn = [[model.bits((2, 3, 6, 7))[0]], [model.bits((1, 2, 6, 7))[1]],
            [-model.bits((0, 2, 3, 7))[1]]]
    violation = [model.bits((3, 4, 5, 6))[0], model.bits((4, 5, 6, 7))[0]]
    export('c0_upper_height_double_coincidence_mixed.cnf', model,
           model.clauses+turn+[violation], 'actual3456<=0 and actual4567<=0')
    result = {'checks': checks, 'unsat_obligations': obligations,
              'excluded_after_analytic_proof_and_independent_replay':
                  'ray1 C0: u=1/2, 0<v<1/2, regular067; reflected v=0 with regular123',
              'collinear_opposite_cap_included': True,
              'whole_height_boundary_excluded': False}
    (directory/'c0_one_regular_height.json').write_text(json.dumps(result, indent=2)+'\n')
    return result


if __name__ == '__main__':
    if not __debug__:
        raise RuntimeError('run with assertions enabled')
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('output', type=Path)
    started = time.monotonic()
    result = build(parser.parse_args().output)
    print(json.dumps({'unsat_obligations': len(result['unsat_obligations']),
                      'seconds': time.monotonic()-started}), flush=True)
