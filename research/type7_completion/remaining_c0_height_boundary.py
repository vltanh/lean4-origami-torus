#!/usr/bin/env python3
"""Exclude regular ray-1 C0 on all four open height-boundary edges.

The metric forces vertex 4 onto segment 67. Six actual-trit CNFs,
exact endpoint identities, and the existing support bound exclude
both its strict-interior and coincident positions. Nested upper
sections exclude the other two edges. The companion contains the
analytic proof; every CNF needs independent RUP replay.
"""

import argparse
from itertools import combinations
import json
from pathlib import Path
import time

import sympy as s

import exhaustive_c0_collinear as boundary
import exhaustive_c0_endpoint_bound as endpoint
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
WEAK_SIGNS = (((0, 1, 3, 6), -1), ((0, 1, 2, 6), -1),
              ((0, 1, 3, 5), -1), ((0, 1, 5, 6), -1),
              ((0, 3, 5, 6), 1), ((1, 3, 5, 6), -1),
              ((0, 3, 5, 7), 1))
STRICT_SIGNS = (((1, 3, 6, 7), -1), ((3, 5, 6, 7), -1))


def coordinates():
    v = s.Symbol('v')
    P = [s.zeros(2, 1), s.zeros(2, 1)]
    P += [s.Matrix(s.symbols(f'x{i} y{i}')) for i in range(2, 8)]
    levels = (0, HALF, HALF, HALF, 0, v, 0, 0)
    Q = [p.col_join(s.Matrix([z])) for p, z in zip(P, levels)]

    def bracket(quad):
        return s.det(s.Matrix.hstack(*(Q[i]-Q[quad[0]] for i in quad[1:])))

    return v, P, levels, bracket


def height_relations():
    v, _, levels, bracket = coordinates()
    variables = s.symbols('C0:15')

    def cross(i, j):
        if i == j or min(i, j) < 2:
            return s.Integer(0)
        return (1 if i < j else -1)*variables[PAIRS.index(tuple(sorted((i, j))))]

    def origin(i, j, k):
        return levels[i]*cross(j, k)-levels[j]*cross(i, k)+levels[k]*cross(i, j)

    relations = []
    for quad in QUADS:
        i, j, k, l = quad
        expression = s.expand(2*(origin(j, k, l)-origin(i, k, l)
                                 +origin(i, j, l)-origin(i, j, k)))
        coefficients = [s.expand(expression.coeff(variable)) for variable in variables]
        assert s.expand(bracket(quad)-sum(coefficient*bracket((0, 1)+pair)
                           for coefficient, pair in zip(coefficients, PAIRS))) == 0
        if quad[:2] == (0, 1):
            continue
        terms = []
        for pair, coefficient in zip(PAIRS, coefficients):
            assert s.Poly(coefficient, v).degree() <= 1
            corners = [coefficient.subs(v, value) for value in (0, HALF)]
            if all(value == 0 for value in corners):
                continue
            if all(value >= 0 for value in corners):
                sign = 1
            else:
                assert all(value <= 0 for value in corners)
                sign = -1
            terms.append((pair, sign))
        relations.append((quad, tuple(terms)))
    assert len(relations) == 55
    return tuple(relations)


class EndpointModel(ActualBracketModel):
    def __init__(self, lower_orientation, case, relations):
        assert lower_orientation in (-1, 1) and case in CASES
        self.n, base, *_ = shared.base_formula()
        self.clauses = [list(row) for row in base]
        self.trits = {}
        # These two cuts are strict throughout 0<v<1/2. Vertex 4 is
        # on the lower level, so the old interior-C0 cuts are not used.
        for high in ({1, 2, 3}, {1, 2, 3, 5}):
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
        for vertex in range(8):
            if vertex not in (1, 2, 3):
                self.clauses.append([self.bits((1, 2, 3, vertex), -1)[0]])
            if vertex not in (0, 4, 6, 7):
                self.clauses.append([self.bits((0, 6, 7, vertex), lower_orientation)[0]])
        for bit in self.bits((0, 4, 6, 7)):
            self.clauses.append([-bit])
        parents = (6, 7) if case == 'strict' else (6,)
        for quad in QUADS:
            if 4 in quad:
                self.sumzero([self.bits(tuple(parent if vertex == 4 else vertex for vertex in quad))
                              for parent in parents]+[self.bits(quad, -1)])
        self.add_weak_gp()
        for quad, terms in relations:
            self.sumzero([self.bits(quad)]+[self.bits((0, 1)+pair, -sign)
                                            for pair, sign in terms])
        # Nonzero P2, P3, and E cannot be parallel to both independent
        # lower cap vectors. These rank clauses exclude only paired zeros.
        for first, second in (((0, 1, 2, 6), (0, 1, 2, 7)),
                              ((0, 1, 3, 6), (0, 1, 3, 7)),
                              ((0, 2, 3, 6), (0, 2, 3, 7))):
            self.clauses.append(list(self.bits(first))+list(self.bits(second)))


def metric_checks():
    v, P, _, bracket = coordinates()
    lv = 1-2*v
    original = reduction.original_system((HALF, HALF, HALF, 1, -v, 0))
    rows = []

    def source_row(terms, auxiliary=None):
        row = [s.Integer(0)]*29
        for edge, coefficient in terms.items():
            row[reduction.EDGES.index(edge)] = coefficient
        for index, coefficient in (auxiliary or {}).items():
            row[index] = coefficient
        rows.append(row)

    for edge in ((0, 6), (0, 7), (1, 2), (1, 3), (2, 3), (6, 7), (4, 6)):
        source_row({edge: 1})
    # v*T47=0 retains the fifth product-scale syzygy. Since v>0,
    # this proves T47=0 without discarding any auxiliary variable.
    source_row({(4, 7): v}, {28: HALF})
    source_row({(0, 1): 1, (0, 2): -1, (1, 7): -1, (2, 7): 1})
    assert all(s.expand(value) == 0 for value in s.Matrix(rows)*original)
    d = list(s.symbols('d0:7'))
    d.append(HALF-sum(d))
    h = [HALF-value for value in d]
    X = geometry.horizontal_displacements(h)
    radius = d[4]+d[5]
    assert s.expand(X[4, 6]-radius) == 0
    assert s.expand(X[4, 7]-radius+h[6]) == 0
    assert s.expand(X[6, 7]+h[6]) == 0
    assert s.expand(h[6]-radius-sum(d[i] for i in (0, 1, 2, 3, 7))) == 0
    L, M, D = d[1]+d[2], d[6]+d[7], d[0]+d[1]+d[2]+d[6]+d[7]
    assert s.expand(h[5]-2*v*D-d[3]-d[4]-lv*D) == 0
    cross = lambda a, b: s.det(s.Matrix.hstack(a, b))
    F = P[7]-P[6]
    Q5 = P[5]-2*v*P[3]-lv*P[6]
    identities = (
        2*bracket((0, 3, 5, 6))-cross(P[5]-2*v*P[3], P[6]),
        2*bracket((1, 3, 5, 6))+cross(P[3], P[5]-lv*P[6]),
        2*bracket((0, 3, 5, 7))-cross(P[5]-2*v*P[3], P[7]),
        2*bracket((1, 3, 6, 7))-cross(P[3], F),
        2*bracket((3, 5, 6, 7))-cross(Q5, F),
    )
    assert all(s.expand(value) == 0 for value in identities)
    lower_cross = cross(P[6], P[7])
    for vector, first, second in ((P[2], (0, 1, 2, 6), (0, 1, 2, 7)),
                                  (P[3], (0, 1, 3, 6), (0, 1, 3, 7)),
                                  (P[3]-P[2], (0, 2, 3, 6), (0, 2, 3, 7))):
        a, b = cross(vector, P[6]), cross(vector, P[7])
        assert s.expand(2*bracket(first)-a) == 0
        assert s.expand(2*bracket(second)-b) == 0
        assert all(s.expand(value) == 0 for value in a*P[7]-b*P[6]+lower_cross*vector)
    R = s.diag(1, -1)
    assert s.expand(cross(-R*F, R*Q5)-cross(F, Q5)) == 0
    assert s.expand(cross(R*P[6], R*P[3])-cross(P[3], P[6])) == 0
    return {'closed_source_rows': len(rows), 'endpoint_metric_lengths': 3,
            'strict_segment_gap': True, 'radius_decomposition': True,
            'determinant_identities': len(identities), 'rank_bindings': 3,
            'reflected_cross_product_identities': 2,
            'marked_reflection': boundary.symmetry_checks(),
            'endpoint_support': endpoint.verify(), 'trit_identities': trit_checks()}


def upper_section_checks():
    v, t = s.symbols('v t')
    original = reduction.original_system((HALF, HALF, HALF, HALF, -v, 0))
    rows = []
    for edge in ((0, 6), (0, 7), (1, 2), (1, 3), (2, 3), (6, 7), (3, 4)):
        row = [s.Integer(edge == other) for other in reduction.EDGES]+[s.Integer(0)]*5
        rows.append(row)
    row = [s.Integer(0)]*29
    row[reduction.EDGES.index((2, 4))] = 1-2*v
    row[25] = -1
    rows.append(row)
    assert all(s.expand(value) == 0 for value in s.Matrix(rows)*original)
    _, P, _, _ = coordinates()
    levels = (0, HALF, HALF, HALF, HALF, v, 0, 0)
    edges_b = ((0, 1), (0, 3), (0, 2), (2, 7), (1, 7), (1, 6))
    edges_a = ((3, 5), (2, 5), (4, 5), (4, 7), (4, 6), (3, 6))
    source_faces = set(shared.base_formula()[2])
    for cycle in (edges_b, edges_a):
        for i, edge in enumerate(cycle):
            assert tuple(sorted(set(edge)|set(cycle[(i+1) % len(cycle)]))) in source_faces
    target_b = (P[0], P[3], P[2], P[2], P[0], P[0])
    target_a = (P[3], P[2], P[4], P[4], P[4], P[3])
    for cycle, target in ((edges_b, target_b), (edges_a, target_a)):
        for (i, j), point in zip(cycle, target):
            coefficient = (t-levels[i])/(levels[j]-levels[i])
            section = (1-coefficient)*P[i]+coefficient*P[j]
            assert all(s.cancel(value) == 0 for value in section.subs(t, HALF)-point)
    link = (0, 6, 3, 2, 4, 7)
    assert {tuple(sorted((5, link[i], link[(i+1) % 6]))) for i in range(6)} \
        == {face for face in source_faces if 5 in face}
    high = {1, 2, 3, 4}
    assert sum((link[i] in high) != (link[(i+1) % 6] in high) for i in range(6)) == 2
    d1, d2, d3 = s.symbols('d1 d2 d3')
    assert s.expand((HALF-d2)+(HALF-d3)+(d2+d3)-1) == 0
    assert s.expand((HALF-d3)-(d1+d2)-(HALF-d1-d2-d3)) == 0
    # Reuse the independently checked six-face/ten-face annulus source,
    # including connectedness, Euler characteristic, and both boundaries.
    from solver_remaining_c0_sections import coordinate_checks
    annuli = coordinate_checks()
    return {'closed_upper_metric_rows': len(rows), 'upper_section_edge_bindings': 12,
            'critical_vertex_link_checked': True, 'equal_perimeter_contradiction': True,
            'source_annuli': annuli}


def build(directory):
    directory.mkdir(parents=True, exist_ok=True)
    checks, relations = metric_checks(), height_relations()
    checks['upper_sections'] = upper_section_checks()
    obligations = []

    def export(name, model, clauses, claim):
        with FastSAT(model.n, clauses) as solver:
            assert solver.check() == -1, name
        write_cnf(directory/name, model.n, clauses)
        obligations.append({'file': name, 'claim': claim, 'variables': model.n,
                            'clauses': len(clauses)})

    for case in CASES:
        negative = EndpointModel(-1, case, relations)
        export(f'c0_u0_{case}_negative_cap.cnf', negative, negative.clauses,
               'the lower cap cannot have negative orientation')
        positive = EndpointModel(1, case, relations)
        export(f'c0_u0_{case}_core.cnf', positive,
               positive.clauses+[[-positive.bits((0, 1, 2, 7))[1]]],
               'the actual core bracket0127 is strictly negative')
        turn = [[positive.bits(quad, sign)[0]] for quad, sign in turning.METRIC_SIGNS]
        violation = [positive.bits(quad, -sign)[0] for quad, sign in WEAK_SIGNS]
        violation += [-positive.bits(quad, sign)[0] for quad, sign in STRICT_SIGNS]
        export(f'c0_u0_{case}_cone.cnf', positive, positive.clauses+turn+[violation],
               'the strict metric turn forces the closed P5 cone and two strict cross signs')
    record = {'checks': checks, 'height_relations': len(relations),
              'weak_actual_consequences': WEAK_SIGNS,
              'strict_actual_consequences': STRICT_SIGNS,
              'unsat_obligations': obligations,
              'excluded_after_analytic_proof_and_independent_replay':
                  'regular ray1 C0: all four open edges of the closed height square',
              'corner_or_collinear_cap_exclusion_claimed': False}
    (directory/'height_boundary.json').write_text(json.dumps(record, indent=2)+'\n')
    return record


if __name__ == '__main__':
    if not __debug__:
        raise RuntimeError('run with assertions enabled')
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('output', type=Path)
    start = time.monotonic()
    result = build(parser.parse_args().output)
    print(json.dumps({'unsat_obligations': len(result['unsat_obligations']),
                      'height_relations': result['height_relations'],
                      'seconds': round(time.monotonic()-start, 3)}), flush=True)
