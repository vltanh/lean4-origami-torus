#!/usr/bin/env python3
"""Source checks for a regular C0 nested-quadrilateral reduction.

Usage: python remaining_c0_nested_quadrilaterals.py OUTPUT_DIRECTORY

For 0<v<u<1/2, the companion excludes the complementary annulus being
inner whenever generic3467 or generic2356 is positive. On u=v it excludes
that nesting alternative altogether. The argument applies to both ray
markings and retains zero weights/minors. It does not exclude all C0.
All six exported Boolean obligations need independent RUP replay.
"""

import argparse
from collections import Counter
from itertools import combinations
import json
from pathlib import Path
import time

import sympy as s

import exhaustive_c0_angles as angles
import exhaustive_c0_collinear as reflection
import exhaustive_remaining_axis as axis
import exhaustive_remaining_locus as locus
import remaining_c1_sections as c1
import solver_remaining_c1_geometry as geometry
import solver_remaining_chambers as shared
import solver_remaining_limit as reduction
from solver_chambers import write_cnf
from solver_sat import FastSAT

HALF = s.Rational(1, 2)
DIRECT_FACES = ((0, 1, 3), (0, 2, 3), (0, 2, 7),
                (1, 2, 7), (1, 6, 7), (0, 1, 6))


def equal(first, second):
    assert all(s.cancel(value) == 0 for value in first-second)


def metric_checks():
    u, v = s.symbols('u v')
    h = s.symbols('h0:8')
    d = [HALF-value for value in h]
    p = [s.zeros(2, 1), s.zeros(2, 1)]
    p += [s.Matrix(s.symbols(f'x{i} y{i}')) for i in range(2, 8)]
    x = geometry.horizontal_displacements(h)
    lu, lv = 1-2*u, 1-2*v
    D = h[3]+h[4]+h[5]-1
    L, M = 1-h[1]-h[2], 1-h[6]-h[7]

    # Bind the local horizontal formulas and the entire auxiliary matrix
    # to each marked cocycle. No ray-1 total-weight identity is reused.
    values = (HALF, HALF, HALF, 1-u, -v, 0)
    matrix = reduction.original_system(values)
    intrinsic, spatial = axis.baselines(locus.vertex_values(values))
    for mark in (1, 2):
        shifts, _, edges = axis.case_data(mark)
        xx = [s.Integer(0)]
        for i in range(7):
            a, b = shifts[i, i+1]
            xx.append(s.expand(xx[-1]-h[i]-a-HALF*b))
        budget = {h[7]: s.Rational(9, 2)-mark-sum(h[:7])}
        for i, j in edges:
            a, b = shifts[i, j]
            assert s.expand(xx[j]-xx[i]+a+HALF*b-x[i, j].subs(budget)) == 0
        assert s.expand((D-d[0]-L-M-(1-mark)).subs(budget)) == 0
        rows = []
        for i, j in edges:
            dz = spatial[j]-spatial[i]
            dy = intrinsic[j]-intrinsic[i]+shifts[i, j][1]
            rows.append(reduction.QMAP.get((i, j), 0)
                        +2*dz*(reduction.H[j]-reduction.H[i])
                        -2*dy*reduction.W*(int(j == 6)-int(i == 6)))
        rows += locus.q_syzygies(locus.vertex_values(values), reduction.QMAP)
        actual, zero = s.linear_eq_to_matrix(rows, reduction.AUXILIARIES)
        assert not any(zero) and actual == matrix

    T = {edge: s.expand((p[edge[1]]-p[edge[0]]).dot(p[edge[1]]-p[edge[0]])-value**2)
         for edge, value in x.items()}
    formal = s.symbols('T0:24')
    tt = dict(zip(reduction.EDGES, formal))

    def stresses(t):
        return [2*u*t[3, 4]+lu*t[4, 6]-2*u*lu*t[3, 6],
                2*v*t[3, 5]+lv*t[5, 6]-2*v*lv*t[3, 6],
                t[4, 5]-2*u*t[3, 5]-lu*t[5, 6]-2*v*t[3, 4]-lv*t[4, 6]
                +(2*u*lv+2*v*lu)*t[3, 6],
                lv*(t[2, 4]-t[3, 4])-lu*(t[2, 5]-t[3, 5]),
                v*(t[4, 7]-t[4, 6])-u*(t[5, 7]-t[5, 6])]

    source_rows = []
    for index, expression in enumerate(stresses(tt)):
        row = [s.diff(expression, variable) for variable in formal]+[s.Integer(0)]*5
        if index == 3:
            row[25] = -1
        if index == 4:
            row[28] = HALF
        source_rows.append(row)
    for edge in ((1, 2), (1, 3), (2, 3), (0, 6), (0, 7), (6, 7)):
        source_rows.append([s.Integer(edge == other) for other in reduction.EDGES]+[s.Integer(0)]*5)
    core = tt[0, 1]-tt[0, 2]-tt[1, 7]+tt[2, 7]
    source_rows.append([s.diff(core, variable) for variable in formal]+[s.Integer(0)]*5)
    assert all(s.expand(value) == 0 for value in s.Matrix(source_rows)*matrix)
    assert s.expand(core.subs(dict(zip(formal, (T[e] for e in reduction.EDGES))))
                    +2*(p[2].dot(p[7])-d[0]+h[1]*h[7])) == 0

    r, z = h[3]-lu*D, h[5]-2*v*D
    q4, q5 = p[4]-2*u*p[3]-lu*p[6], p[5]-2*v*p[3]-lv*p[6]
    E, F = p[3]-p[2], p[7]-p[6]
    U, V, J, C, K = stresses(T)
    assert s.expand(q4.dot(q4)-r*r-U) == 0
    assert s.expand(q5.dot(q5)-z*z-V) == 0
    assert s.expand(2*(q4.dot(q5)+r*z-d[4])+J) == 0
    S, W = lv*q4-lu*q5, v*q4-u*q5
    es = E.dot(S)-h[2]*(lv*r+lu*z)+lv*(h[2]-d[3])
    fw = F.dot(W)-h[6]*(v*r+u*z)+u*(h[6]-d[5])
    assert s.expand(2*es-C+2*(u-v)*T[2, 3]) == 0
    assert s.expand(2*fw+K-(v-u)*T[6, 7]) == 0

    # Effective quadrilateral parameters use only closed nearest bounds.
    a, q = v/u, 1-v/u
    sigma = 1-z-a*r
    tau = sigma-q*h[6]
    assert s.expand(r-2*u*h[3]-lu*(1-h[4]-h[5])) == 0
    assert s.expand(z-lv*h[5]-2*v*(1-h[3]-h[4])) == 0
    assert s.cancel(z-a*(1-h[4]-r)-q*h[5]) == 0
    assert s.cancel(sigma-q*(1-h[5])-a*h[4]) == 0
    assert s.cancel(tau-q*(1-h[5]-h[6])-a*h[4]) == 0
    n2 = (a*r+z)**2-2*a*d[4]
    assert s.cancel(n2-sigma**2+2*q*d[5]) == 0
    assert s.cancel((h[6]*(v*r+u*z)-u*(h[6]-d[5]))/u
                    +h[6]*sigma-d[5]) == 0
    assert s.cancel(n2+2*q*(d[5]-h[6]*sigma)+q*q*h[6]**2-tau*tau) == 0
    assert s.cancel(z+a*r+q*h[6]+tau-1) == 0
    assert s.expand(2*s.Symbol('t')*(L+h[1]+h[2])
                    +(1-2*s.Symbol('t'))*(M+h[6]+h[7])-1) == 0

    # Equal heights give the triangle lengths r,z,h4, including h4=0.
    assert s.expand((r+z+h[4]-1).subs(v, u)) == 0
    assert s.expand(((r+z)**2-2*d[4]-h[4]**2).subs(v, u)) == 0
    return {'marked_cocycles_checked': [1, 2], 'full_source_rows': 29,
            'closed_polynomial_stresses': len(source_rows),
            'circle_and_dot_identities': 5,
            'effective_quadrilateral_and_diagonal_identities': True,
            'ray2_D': 'd0+L+M-1', 'ray1_budget_used_for_ray2': False}


def section_checks():
    u, v, t = s.symbols('u v t')
    p = [s.zeros(2, 1), s.zeros(2, 1)]
    p += [s.Matrix(s.symbols(f'x{i} y{i}')) for i in range(2, 8)]
    levels = (0, HALF, HALF, HALF, u, v, 0, 0)
    lu, lv = 1-2*u, 1-2*v
    a, q = v/u, 1-v/u
    q4, q5 = p[4]-2*u*p[3]-lu*p[6], p[5]-2*v*p[3]-lv*p[6]
    F = p[7]-p[6]
    critical = (p[5], 2*v*p[3]+lv*p[6], a*p[4]+q*p[6], a*p[4]+q*p[7])
    weights = ({5: 1}, {3: 2*v, 6: lv}, {4: a, 6: q}, {4: a, 7: q})
    critical_faces = ((3, 5, 6), (3, 4, 6), (4, 6, 7), (4, 5, 7))
    vectors = (-q5, a*q4, q*F, -(a*q4-q5+q*F))
    _, _, original_faces, *_ = shared.base_formula()
    faces = set(original_faces)
    for i, (point, row) in enumerate(zip(critical, weights)):
        assert s.cancel(sum(row.values())-1) == 0
        assert s.cancel(sum(coefficient*levels[j] for j, coefficient in row.items())-v) == 0
        equal(point, sum((coefficient*p[j] for j, coefficient in row.items()), s.zeros(2, 1)))
        assert set(row) | set(weights[(i+1) % 4]) <= set(critical_faces[i])
        assert critical_faces[i] in faces
        equal(critical[(i+1) % 4]-point, vectors[i])

    direct_edges = ((0, 1), (0, 3), (0, 2), (2, 7), (1, 7), (1, 6))
    direct = (p[0], 2*t*p[3], 2*t*p[2], 2*t*p[2]+(1-2*t)*p[7],
              (1-2*t)*p[7], (1-2*t)*p[6])
    for i, ((a0, b0), point) in enumerate(zip(direct_edges, direct)):
        equal(point, p[a0]+(t-levels[a0])/(levels[b0]-levels[a0])*(p[b0]-p[a0]))
        assert tuple(sorted(set(direct_edges[i]) | set(direct_edges[(i+1) % 6]))) == DIRECT_FACES[i]

    cap_edges = set(combinations((1, 2, 3), 2)) | set(combinations((0, 6, 7), 2))
    annuli = (set(DIRECT_FACES), faces-set(DIRECT_FACES))
    for annulus in annuli:
        edge_counts = Counter(edge for face in annulus for edge in combinations(face, 2))
        assert {edge for edge, count in edge_counts.items() if count == 1} == cap_edges
        assert all(count in (1, 2) for count in edge_counts.values())
        assert len(set().union(*map(set, annulus)))-len(edge_counts)+len(annulus) == 0
    links = {4: (1, 2, 5, 7, 6, 3), 5: (0, 6, 3, 2, 4, 7)}
    high_sets = {4: ({1, 2, 3, 5}, {1, 2, 3}), 5: ({2, 3}, {2, 3, 4})}
    for vertex, cycle in links.items():
        assert {tuple(sorted((vertex, cycle[i], cycle[(i+1) % 6]))) for i in range(6)} == {
            face for face in faces if vertex in face}
        for high in high_sets[vertex]:
            assert sum((cycle[i] in high) != (cycle[(i+1) % 6] in high) for i in range(6)) == 2

    # Every direct edge is a positive scalar times a fixed nonzero cap
    # edge. These are the fixed support directions in the companion.
    direct_vectors = (2*t*p[3], -2*t*(p[3]-p[2]), (1-2*t)*p[7],
                      -2*t*p[2], -(1-2*t)*F, -(1-2*t)*p[6])
    for i, vector in enumerate(direct_vectors):
        equal(direct[(i+1) % 6]-direct[i], vector)

    c = 2*t*p[3]+(1-2*t)*p[6]
    d6 = t/u*p[4]+(1-t/u)*p[6]
    d7 = t/u*p[4]+(1-t/u)*p[7]
    equal(d6-direct[5], t/u*(p[4]-lu*p[6]))
    equal(d7-direct[4], t/u*(p[4]-lu*p[7]))
    equal(d7-direct[3], t/u*(p[4]-2*u*p[2]-lu*p[7]))
    # The unique direct trajectory starting at P6 ends at zero, whereas
    # c starts at P6 and ends at the nonzero upper-cap point P3.
    endpoints = ((0, 0), (0, 3), (0, 2), (7, 2), (7, 0), (6, 0))
    assert [pair for pair in endpoints if pair[0] == 6] == [(6, 0)]
    equal(c.subs(t, 0), p[6])
    equal(c.subs(t, HALF), p[3])
    # The only remaining simultaneous tracking choices make two
    # consecutive direct edges nonzero opposite multiples of F.
    equal((-2*t*p[2]).subs({p[2][i]: -lu/(2*u)*F[i] for i in range(2)}), t*lu/u*F)
    equal(direct_vectors[4], -(1-2*t)*F)
    for i, expected in ((0, p[5]), (1, c.subs(t, u)), (2, p[4]), (3, p[4])):
        equal(critical[i].subs(v, u), expected)

    # The marked reflection preserves each annulus and interchanges the
    # lower/upper favorable turns. Its cocycle/gauge is checked upstream.
    permutation = tuple((1-i) % 8 for i in range(8))
    for annulus in annuli:
        assert {tuple(sorted(permutation[i] for i in face)) for face in annulus} == annulus
    lit = shared.common.lit
    assert lit(tuple(permutation[i] for i in (3, 4, 6, 7))) == lit((2, 3, 5, 6))
    assert lit(tuple(permutation[i] for i in (4, 5, 6, 7))) == lit((2, 3, 4, 5))
    return {'annulus_face_counts': list(map(len, annuli)), 'critical_edge_bindings': 4,
            'direct_edge_bindings': 6, 'both_intermediate_height_orders_checked': True,
            'tracking_identities': 6, 'marked_reflection': reflection.symmetry_checks()}


def height_cut():
    high = {1, 2, 3, 4}
    result = []
    for support in combinations(range(8), 5):
        row = [(1 if vertex in high else -1)*(-1)**i
               *shared.common.lit(support[:i]+support[i+1:]) for i, vertex in enumerate(support)]
        result += [row, [-value for value in row]]
    return result


def direct_finite_turns():
    z1, z2, z3, t = s.symbols('z1 z2 z3 t')
    p = [s.zeros(2, 1), s.zeros(2, 1)]
    p += [s.Matrix(s.symbols(f'x{i} y{i}')) for i in range(2, 8)]
    z = (0, z1, z2, z3, s.Symbol('z4'), s.Symbol('z5'), 0, 0)
    points = [point.col_join(s.Matrix([height])) for point, height in zip(p, z)]

    def bracket(quad):
        return s.Matrix.hstack(*(points[i]-points[quad[0]] for i in quad[1:])).det()

    direct = (p[0], t/z3*p[3], t/z2*p[2], t/z2*p[2]+(1-t/z2)*p[7],
              (1-t/z1)*p[7], (1-t/z1)*p[6])
    expected = (t*(1-t/z1)/(z1*z3)*bracket((0, 1, 3, 6)),
                -t*t/(z1*z2*z3)*bracket((0, 1, 2, 3)),
                -t*(1-t/z2)/(z2*z3)*bracket((0, 2, 3, 7)),
                t*(1-t/z2)/(z1*z2)*bracket((0, 1, 2, 7)),
                t*(1-t/z1)/(z1*z2)*bracket((1, 2, 6, 7)),
                -(1-t/z1)**2/z1*bracket((0, 1, 6, 7)))
    for i, target in enumerate(expected):
        actual = s.Matrix.hstack(direct[i]-direct[(i-1) % 6], direct[(i+1) % 6]-direct[i]).det()
        assert s.cancel(actual-target) == 0
    return {'finite_direct_turn_identities': 6}


def build(directory):
    directory.mkdir(parents=True, exist_ok=True)
    result = {'metric': metric_checks(), 'sections': section_checks(),
              'strict_corner_and_zero_norm': c1.metric_checks(),
              'arbitrary_finite_height_turns': c1.finite_turn_checks(),
              'direct_finite_turns': direct_finite_turns()}
    n, base, *_ = shared.base_formula()
    positive = base+angles.cap_units(1)
    ordered = positive+height_cut()
    lit = shared.common.lit
    nesting, lower, upper = map(lit, ((0, 1, 5, 6), (3, 4, 6, 7), (2, 3, 5, 6)))
    words = []
    with FastSAT(n, ordered) as solver:
        while solver.check() == 1:
            witness = solver.model(n)
            assert shared.satisfies(witness, ordered)
            word = tuple(witness[:70])
            words.append(word)
            solver.add([-(i+1)*value for i, value in enumerate(word)])
        assert solver.check() == -1
    words.sort()
    counts = Counter(tuple(word[abs(variable)-1]*(1 if variable > 0 else -1)
                           for variable in (nesting, lower, upper)) for word in words)
    assert counts == {(1, -1, 1): 11, (1, 1, 1): 5, (1, 1, -1): 11, (1, -1, -1): 16,
                      (-1, -1, -1): 24, (-1, 1, -1): 126, (-1, 1, 1): 44, (-1, -1, 1): 126}
    geometric_clauses = [[nesting, -lower], [nesting, -upper]]
    remaining = [word for word in words if shared.satisfies(word, geometric_clauses)]
    assert len(words) == 363 and len(remaining) == 67
    direct_inner_turns = [lit((0, 1, 3, 6)), lit((0, 2, 3, 7)), -lit((1, 2, 6, 7))]
    assert all(shared.satisfies(word, [[variable] for variable in direct_inner_turns])
               for word in remaining if word[nesting-1] > 0)

    def block(rows):
        return [[-(i+1)*value for i, value in enumerate(row)] for row in rows]

    formulas = {
        'c0_nested_negative_cap.cnf': base+angles.cap_units(-1),
        'c0_nested_common_turn.cnf': positive+[[lit((3, 4, 5, 6))]],
        'c0_nested_nesting.cnf': positive+[[nesting], [lit((0, 1, 5, 7))]],
        'c0_nested_height_turns.cnf': ordered+[[lit((2, 3, 4, 5)), lit((4, 5, 6, 7))]],
        'c0_nested_ordered_coverage.cnf': ordered+block(words),
        'c0_nested_residual_coverage.cnf': ordered+geometric_clauses+block(remaining),
    }
    for name, clauses in formulas.items():
        with FastSAT(n, clauses) as solver:
            assert solver.check() == -1
        write_cnf(directory/name, n, clauses)
    encode = lambda word: ''.join('+' if value > 0 else '-' for value in word)
    result.update(markings=[1, 2], unsat_obligations=list(formulas),
                  source_height_order='0<v<u<1/2', generic_ordered_completions=len(words),
                  generic_completions_excluded_by_section_argument=len(words)-len(remaining),
                  residual_generic_completions=len(remaining),
                  counts_by_0156_3467_2356={','.join(map(str, key)): value for key, value in sorted(counts.items())},
                  ordered_words=list(map(encode, words)), residual_words=list(map(encode, remaining)),
                  diagonal_conclusion='u=v: complementary annulus cannot be inner',
                  direct_inner_residual='all 43 words have a unique reflex finite direct corner at edge01',
                  finite_section_geometry_required=True, whole_C0_excluded=False)
    (directory/'c0_nested_quadrilaterals.json').write_text(json.dumps(result, indent=2)+'\n')
    return result


if __name__ == '__main__':
    if not __debug__:
        raise RuntimeError('run with assertions enabled')
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('output', type=Path)
    started = time.monotonic()
    record = build(parser.parse_args().output)
    print(json.dumps({key: value for key, value in record.items()
                      if key not in ('ordered_words', 'residual_words')}
                     | {'seconds': time.monotonic()-started}), flush=True)
