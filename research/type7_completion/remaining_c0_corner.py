#!/usr/bin/env python3
"""Exclude regular ray-1 C0 at all four height corners.

Nine actual-trit CNFs require independent RUP replay. Exact metric
rows and section winding exclude one corner; nested equal-perimeter
triangles exclude two others. The fourth is the completed two-block
limit. See the companion mathematical proof.
"""

import argparse
from itertools import combinations, product
import json
from pathlib import Path
import time

import sympy as s

import exhaustive_c0_collinear as boundary
import exhaustive_c0_turning as turning
import solver_remaining_c1_geometry as geometry
import solver_remaining_chambers as shared
import solver_remaining_limit as reduction
from solver_remaining_c1_collinear import ActualBracketModel, symbolic_checks as trit_checks
from solver_chambers import write_cnf
from solver_sat import FastSAT

HALF = s.Rational(1, 2)
QUADS = tuple(combinations(range(8), 4))
PAIRS = tuple(combinations(range(2, 8), 2))
CASES = ('strict', 'coincidence')
LEVELS = (0, HALF, HALF, HALF, 0, HALF, 0, 0)


def coordinates(levels=LEVELS):
    P = [s.zeros(2, 1), s.zeros(2, 1)]
    P += [s.Matrix(s.symbols(f'x{i} y{i}')) for i in range(2, 8)]
    Q = [p.col_join(s.Matrix([z])) for p, z in zip(P, levels)]

    def bracket(quad):
        return s.det(s.Matrix.hstack(*(Q[i]-Q[quad[0]] for i in quad[1:])))

    return P, bracket


def height_relations(levels=LEVELS):
    _, bracket = coordinates(levels)
    variables = s.symbols('C0:15')

    def cross(i, j):
        if i == j or min(i, j) < 2:
            return s.Integer(0)
        return (1 if i < j else -1)*variables[PAIRS.index(tuple(sorted((i, j))))]

    def origin(i, j, k):
        return levels[i]*cross(j, k)-levels[j]*cross(i, k)+levels[k]*cross(i, j)

    rows = []
    for quad in QUADS:
        i, j, k, l = quad
        expression = s.expand(2*(origin(j, k, l)-origin(i, k, l)
                                 +origin(i, j, l)-origin(i, j, k)))
        coefficients = [expression.coeff(variable) for variable in variables]
        assert all(value in (-1, 0, 1) for value in coefficients)
        assert s.expand(bracket(quad)-sum(coefficient*bracket((0, 1)+pair)
                           for coefficient, pair in zip(coefficients, PAIRS))) == 0
        if quad[:2] != (0, 1):
            rows.append((quad, tuple((pair, int(value)) for pair, value in zip(PAIRS, coefficients)
                                    if value)))
    assert len(rows) == 55
    return tuple(rows)


class CornerModel(ActualBracketModel):
    def __init__(self, lower_orientation, case4, case5, relations, same_lower=False):
        assert lower_orientation in (-1, 1) and case4 in CASES and case5 in CASES
        self.n, base, *_ = shared.base_formula()
        self.clauses = [list(row) for row in base]
        self.trits = {}
        high = {1, 2, 3} if same_lower else {1, 2, 3, 5}
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
            self.sumzero([self.bits(support[:i]+support[i+1:], (-1)**i)
                          for i in range(5)])
        for vertex in ((0, 4, 5, 6, 7) if same_lower else (0, 4, 6, 7)):
            self.clauses.append([self.bits((1, 2, 3, vertex), -1)[0]])
        for vertex in ((1, 2, 3) if same_lower else (1, 2, 3, 5)):
            self.clauses.append([self.bits((0, 6, 7, vertex), lower_orientation)[0]])
        zero_quads = ((0, 4, 6, 7), (0, 5, 6, 7)) if same_lower else ((1, 2, 3, 5), (0, 4, 6, 7))
        for quad in zero_quads:
            for bit in self.bits(quad):
                self.clauses.append([-bit])
        positions = ((4, (0,)), (5, (7,))) if same_lower else (
            (4, (6, 7) if case4 == 'strict' else (6,)),
            (5, (3, 2) if case5 == 'strict' else (3,)))
        for middle, parents in positions:
            for quad in QUADS:
                if middle in quad:
                    self.sumzero([self.bits(tuple(parent if vertex == middle else vertex for vertex in quad))
                                  for parent in parents]+[self.bits(quad, -1)])
        self.add_weak_gp()
        for quad, terms in relations:
            self.sumzero([self.bits(quad)]+[self.bits((0, 1)+pair, -sign)
                                            for pair, sign in terms])
        for first, second in (((0, 1, 2, 6), (0, 1, 2, 7)),
                              ((0, 1, 3, 6), (0, 1, 3, 7)),
                              ((0, 2, 3, 6), (0, 2, 3, 7))):
            self.clauses.append(list(self.bits(first))+list(self.bits(second)))


def symbolic_checks():
    P, bracket = coordinates()
    cross = lambda a, b: s.det(s.Matrix.hstack(a, b))
    original = reduction.original_system((HALF, HALF, HALF, 1, -HALF, 0))
    rows = []

    def source(terms, auxiliary=None):
        row = [s.Integer(0)]*29
        for edge, coefficient in terms.items():
            row[reduction.EDGES.index(edge)] = coefficient
        for index, coefficient in (auxiliary or {}).items():
            row[index] = coefficient
        rows.append(row)

    for edge in ((0, 6), (0, 7), (1, 2), (1, 3), (2, 3), (6, 7), (4, 6), (3, 5)):
        source({edge: 1})
    source({(4, 7): 1}, {28: 1})
    source({(2, 5): 1}, {25: 1})
    source({(0, 1): 1, (0, 2): -1, (1, 7): -1, (2, 7): 1})
    assert all(s.expand(value) == 0 for value in s.Matrix(rows)*original)
    d = list(s.symbols('d0:7'))
    d.append(HALF-sum(d))
    h = [HALF-value for value in d]
    X = geometry.horizontal_displacements(h)
    r, q = d[4]+d[5], d[3]+d[4]
    assert s.expand(X[4, 6]-r) == 0
    assert s.expand(X[4, 7]-r+h[6]) == 0
    assert s.expand(X[3, 5]-q) == 0
    assert s.expand(X[2, 5]-q+h[2]) == 0
    assert s.expand(h[6]-r-sum(d[i] for i in (0, 1, 2, 3, 7))) == 0
    assert s.expand(h[2]-q-sum(d[i] for i in (0, 1, 5, 6, 7))) == 0
    E, F = P[3]-P[2], P[7]-P[6]
    assert s.expand(2*bracket((1, 3, 6, 7))-cross(P[3], F)) == 0
    assert s.expand(cross(-P[3], -E)-cross(P[2], P[3])) == 0
    assert s.expand(cross(-P[3], F)+2*bracket((1, 3, 6, 7))) == 0
    assert s.expand(cross(F, -E)-2*bracket((2, 3, 6, 7))) == 0
    for vector, first, second in ((P[2], (0, 1, 2, 6), (0, 1, 2, 7)),
                                  (P[3], (0, 1, 3, 6), (0, 1, 3, 7)),
                                  (E, (0, 2, 3, 6), (0, 2, 3, 7))):
        a, b = cross(vector, P[6]), cross(vector, P[7])
        assert s.expand(2*bracket(first)-a) == 0
        assert s.expand(2*bracket(second)-b) == 0
        assert all(s.expand(value) == 0 for value in a*P[7]-b*P[6]+cross(P[6], P[7])*vector)

    t, lam = s.symbols('t lambda')
    section_edges = ((1, 4), (2, 4), (4, 5), (5, 7),
                     (0, 5), (5, 6), (3, 6), (3, 4))
    faces = set(shared.base_formula()[2])
    section = []
    for i, (a, b) in enumerate(section_edges):
        assert tuple(sorted(set((a, b))|set(section_edges[(i+1) % 8]))) in faces
        coefficient = (t/2-LEVELS[a])/(LEVELS[b]-LEVELS[a])
        section.append((1-coefficient)*P[a]+coefficient*P[b])
    base, upper_tip = (1-t)*P[4], (1-t)*P[4]+t*P[3]
    lower0, lower6, lower7 = t*P[3], t*P[3]+(1-t)*P[6], t*P[3]+(1-t)*P[7]
    target = (base, base+t*P[2], upper_tip, lower7, lower0, lower6, lower6, upper_tip)
    substitution = dict(zip(P[5], P[3]))
    for actual, expected in zip(section, target):
        assert all(s.cancel(value) == 0 for value in actual.subs(substitution)-expected)
    assert all(s.expand(value) == 0 for value in
               upper_tip.subs(dict(zip(P[4], P[6]+lam*F)))-lower6-lam*(lower7-lower6))
    assert s.expand(cross(t*P[2], t*P[3])-t*t*cross(P[2], P[3])) == 0
    assert s.expand(cross(lower7-lower6, lower0-lower6)
                    -(1-t)**2*cross(P[6], P[7])) == 0
    reflected = [d[(-i) % 8] for i in range(8)]
    assert s.expand(reflected[4]+reflected[5]-q) == 0
    assert s.expand(reflected[3]+reflected[4]-r) == 0
    return {'closed_source_rows': len(rows), 'two_segment_metric_bindings': True,
            'strict_segment_gaps': 2, 'rank_bindings': 3,
            'section_edge_face_bindings': 8, 'two_triangle_section_identity': True,
            'positive_triangle_area_identities': 2, 'overlap_cone_identities': 3,
            'segment_parameter_reflection': True,
            'marked_reflection': boundary.symmetry_checks(),
            'turning': turning.verify(), 'trit_identities': trit_checks()}


def same_lower_checks():
    levels = (0, HALF, HALF, HALF, 0, 0, 0, 0)
    P, _ = coordinates(levels)
    original = reduction.original_system((HALF, HALF, HALF, 1, 0, 0))
    rows = []
    for edge in ((0, 6), (0, 7), (1, 2), (1, 3), (2, 3), (6, 7),
                 (4, 6), (5, 6), (4, 5)):
        rows.append([s.Integer(edge == other) for other in reduction.EDGES]+[s.Integer(0)]*5)
    assert all(s.expand(value) == 0 for value in s.Matrix(rows)*original)
    h4, h5 = s.symbols('h4 h5')
    assert s.expand(h4+h5+(1-h4-h5)-1) == 0
    h = s.symbols('h0:8')
    X = geometry.horizontal_displacements(h)
    assert s.expand(X[4, 5]+h[4]) == 0
    assert s.expand(X[5, 6]+h[5]) == 0
    assert s.expand(X[4, 6]-(1-h[4]-h[5])) == 0
    d = s.symbols('d0:8')
    impossible_budget = (sum(d)-HALF).subs({d[4]: d[7], d[5]: HALF-d[6]-d[7]})
    assert s.expand(impossible_budget-d[0]-d[1]-d[2]-d[3]-d[7]) == 0
    faces = set(shared.base_formula()[2])
    t = s.Symbol('t')
    cycles = (((0, 1), (0, 3), (0, 2), (2, 7), (1, 7), (1, 6)),
              ((1, 4), (2, 4), (2, 5), (3, 5), (3, 6), (3, 4)))
    bottom = ((P[0], P[0], P[0], P[7], P[7], P[6]),
              (P[4], P[4], P[5], P[5], P[6], P[4]))
    top = ((P[0], P[3], P[2], P[2], P[0], P[0]),
           (P[0], P[2], P[2], P[3], P[3], P[3]))
    for cycle, at_bottom, at_top in zip(cycles, bottom, top):
        for index, ((a, b), low, high) in enumerate(zip(cycle, at_bottom, at_top)):
            assert tuple(sorted({a, b}|set(cycle[(index+1) % 6]))) in faces
            coefficient = (t/2-levels[a])/(levels[b]-levels[a])
            point = (1-coefficient)*P[a]+coefficient*P[b]
            assert all(s.expand(value) == 0 for value in point.subs(t, 0)-low)
            assert all(s.expand(value) == 0 for value in point.subs(t, 1)-high)
    from solver_remaining_c0_sections import coordinate_checks
    annuli = coordinate_checks()
    shifts, _, _ = reduction.axis.case_data(1)
    values = reduction.locus.vertex_values((HALF, HALF, HALF, HALF, 0, 0))
    steps = reduction.locus._step_values(values, shifts)
    assert tuple(steps) == (HALF, 0, 0, 0, HALF, 0, 0, 0)
    return {'same_lower_metric_rows': len(rows), 'unit_lower_triangle_perimeter': True,
            'impossible_reversed_vertex_match': True, 'section_face_bindings': 12,
            'section_endpoint_identities': 24, 'source_annuli': annuli,
            'remaining_corner_is_completed_two_block_limit': True}


def build(directory):
    directory.mkdir(parents=True, exist_ok=True)
    checks, relations = symbolic_checks(), height_relations()
    checks['same_lower'] = same_lower_checks()
    obligations = []

    def export(name, model, clauses, claim):
        with FastSAT(model.n, clauses) as solver:
            assert solver.check() == -1, name
        write_cnf(directory/name, model.n, clauses)
        obligations.append({'file': name, 'claim': claim, 'variables': model.n,
                            'clauses': len(clauses)})

    for case4, case5 in product(CASES, repeat=2):
        model = CornerModel(-1, case4, case5, relations)
        export(f'c0_corner_negative_{case4}_{case5}.cnf', model, model.clauses,
               'negative lower orientation is impossible')
    model = CornerModel(1, 'strict', 'strict', relations)
    export('c0_corner_both_strict.cnf', model, model.clauses,
           'both extra cap points cannot be strictly interior')
    for case4 in CASES:
        model = CornerModel(1, case4, 'coincidence', relations)
        violation = [-model.bits(quad)[1] for quad in ((0, 1, 2, 7), (1, 3, 6, 7))]
        export(f'c0_corner_upper_coincidence_{case4}.cnf', model, model.clauses+[violation],
               'actual0127<0 and1367<0, including exclusion of their zero violations')
    other_relations = height_relations((0, HALF, HALF, HALF, 0, 0, 0, 0))
    for orientation in (-1, 1):
        model = CornerModel(orientation, 'coincidence', 'coincidence', other_relations, same_lower=True)
        export(f'c0_corner_same_lower_{orientation}.cnf', model, model.clauses,
               'at u=v=0, P4=P0 and P5=P7 contradict the actual topology source')
    assert len(obligations) == 9
    record = {'checks': checks, 'height_relations': len(relations),
              'unsat_obligations': obligations,
              'excluded_after_independent_replay_and_winding_argument':
                  'regular ray1 C0 at all four height corners',
              'collinear_caps_claimed': False}
    (directory/'corner.json').write_text(json.dumps(record, indent=2)+'\n')
    return record


if __name__ == '__main__':
    if not __debug__:
        raise RuntimeError('run with assertions enabled')
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('output', type=Path)
    start = time.monotonic()
    result = build(parser.parse_args().output)
    print(json.dumps({'unsat_obligations': len(result['unsat_obligations']),
                      'seconds': round(time.monotonic()-start, 3)}), flush=True)
