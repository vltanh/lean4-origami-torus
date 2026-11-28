#!/usr/bin/env python3
"""Exact critical sections of the regular ray-1 C0 annuli, for 0<u<v<1/2.

This verifies metric identities and section coordinates.  It does not
assert an exclusion: nesting and convexity require a separate argument.
"""

from itertools import combinations
import json
import time

import sympy as s

import remaining_c0_height_order as metric
import solver_remaining_chambers as shared

HALF = s.Rational(1, 2)
DIRECT_FACES = ((0, 1, 3), (0, 2, 3), (0, 2, 7),
                (1, 2, 7), (1, 6, 7), (0, 1, 6))
U_FACES = ((3, 4, 6), (3, 5, 6), (0, 5, 6), (0, 5, 7), (4, 5, 7))
V_FACES = ((2, 4, 5), (1, 2, 4), (1, 3, 4), (3, 4, 6), (3, 5, 6))


def section_coordinates(P, u, v):
    """Clockwise traversal orders when their weak turn tests hold."""
    lu, lv, K = 1-2*u, 1-2*v, v-u
    critical_u = (P[4], 2*u*P[3]+lu*P[6],
                  u/v*P[5]+K/v*P[6], u/v*P[5],
                  u/v*P[5]+K/v*P[7])
    critical_v = (P[5], lv/lu*P[4]+2*K/lu*P[2],
                  lv/lu*P[4], lv/lu*P[4]+2*K/lu*P[3],
                  2*v*P[3]+lv*P[6])
    return critical_u, critical_v


def coordinate_checks():
    u, v, t = s.symbols('u v t')
    K, lu, lv = v-u, 1-2*u, 1-2*v
    P = [s.zeros(2, 1), s.zeros(2, 1)]
    P += [s.Matrix(s.symbols(f'x{i} y{i}')) for i in range(2, 8)]
    levels = (0, HALF, HALF, HALF, u, v, 0, 0)
    points = [p.col_join(s.Matrix([level])) for p, level in zip(P, levels)]
    cross = lambda a, b: s.det(s.Matrix.hstack(a, b))

    def bracket(q):
        return s.det(s.Matrix.hstack(*(points[i]-points[q[0]] for i in q[1:])))

    E, F = P[3]-P[2], P[7]-P[6]
    Q4, Q5 = P[4]-2*u*P[3]-lu*P[6], P[5]-2*v*P[3]-lv*P[6]
    S, W = lv*Q4-lu*Q5, v*Q4-u*Q5
    first, second = section_coordinates(P, u, v)
    expected_edges = (
        (-Q4, u/v*Q5, -K/v*P[6], K/v*P[7], (W-K*F)/v),
        ((S-2*K*E)/lu, -2*K/lu*P[2], 2*K/lu*P[3], -lv/lu*Q4, Q5),
    )
    for polygon, edges in zip((first, second), expected_edges):
        for i, expected in enumerate(edges):
            assert all(s.cancel(value) == 0
                       for value in polygon[(i+1) % 5]-polygon[i]-expected)

    turns_u = (2*(u*bracket((3, 4, 5, 6))-K*bracket((3, 4, 6, 7)))/v,
               2*u/v*bracket((3, 4, 5, 6)),
               -2*u*K/v**2*bracket((0, 3, 5, 6)),
               -K**2/v**3*bracket((0, 5, 6, 7)),
               K/v**2*bracket((0, 4, 5, 7)))
    turns_v = (2*(lv*bracket((3, 4, 5, 6))-2*K*bracket((2, 3, 5, 6)))/lu,
               -4*K/lu**2*bracket((1, 2, 4, 5)),
               8*K**2/lu**3*bracket((1, 2, 3, 4)),
               4*K*lv/lu**2*bracket((1, 3, 4, 6)),
               2*lv/lu*bracket((3, 4, 5, 6)))
    for polygon, turns in zip((first, second), (turns_u, turns_v)):
        for i, expected in enumerate(turns):
            actual = cross(polygon[i]-polygon[(i-1) % 5], polygon[(i+1) % 5]-polygon[i])
            assert s.cancel(actual-expected) == 0

    # Each consecutive pair is on the stated original face.  Barycentric
    # coordinates also check the common physical height without a picture.
    weights_u = ({4: 1}, {3: 2*u, 6: lu}, {5: u/v, 6: K/v},
                 {5: u/v, 0: K/v}, {5: u/v, 7: K/v})
    weights_v = ({5: 1}, {4: lv/lu, 2: 2*K/lu}, {4: lv/lu, 1: 2*K/lu},
                 {4: lv/lu, 3: 2*K/lu}, {3: 2*v, 6: lv})
    _, _, faces, *_ = shared.base_formula()
    cap_edges = {frozenset(edge) for cap in ((1, 2, 3), (0, 6, 7))
                 for edge in combinations(cap, 2)}
    annuli = (set(DIRECT_FACES), set(faces)-set(DIRECT_FACES))
    assert tuple(map(len, annuli)) == (6, 10)
    for annulus in annuli:
        edges = {frozenset(edge) for face in annulus for edge in combinations(face, 2)}
        vertices = set().union(*map(set, annulus))
        boundary = {edge for edge in edges if sum(edge <= set(face) for face in annulus) == 1}
        assert boundary == cap_edges
        assert len(vertices)-len(edges)+len(annulus) == 0
        pending, seen = [next(iter(annulus))], set()
        while pending:
            face = pending.pop()
            if face in seen:
                continue
            seen.add(face)
            pending.extend(other for other in annulus-seen if len(set(face) & set(other)) == 2)
        assert seen == annulus
    assert all(frozenset(set(a) & set(b)) in cap_edges
               for a in annuli[0] for b in annuli[1] if len(set(a) & set(b)) == 2)
    for height, weights, polygons, face_list in (
            (u, weights_u, first, U_FACES), (v, weights_v, second, V_FACES)):
        for i, (row, point) in enumerate(zip(weights, polygons)):
            assert s.cancel(sum(row.values())-1) == 0
            assert s.cancel(sum(coef*levels[j] for j, coef in row.items())-height) == 0
            actual = sum((coef*P[j] for j, coef in row.items()), s.zeros(2, 1))
            assert all(s.cancel(value) == 0 for value in actual-point)
            assert set(row) | set(weights[(i+1) % 5]) <= set(face_list[i])
            assert face_list[i] in faces
    assert set(DIRECT_FACES) <= set(faces)
    direct = (P[0], 2*t*P[3], 2*t*P[2], 2*t*P[2]+(1-2*t)*P[7],
              (1-2*t)*P[7], (1-2*t)*P[6])
    direct_turns = [s.expand(cross(direct[i]-direct[(i-1) % 6],
                                  direct[(i+1) % 6]-direct[i])) for i in range(6)]
    assert s.expand(direct_turns[0]-2*t*(1-2*t)*cross(P[3], P[6])) == 0
    return {'annulus_face_counts': [6, 10], 'critical_section_edges': 10, 'critical_turn_identities': 10,
            'section_face_bindings': 10, 'direct_faces': DIRECT_FACES,
            'u_faces': U_FACES, 'v_faces': V_FACES}


def scalar_checks():
    u, v = s.symbols('u v')
    d = list(s.symbols('d0:7'))
    d.append(HALF-sum(d))
    h = [HALF-value for value in d]
    K, lu, lv = v-u, 1-2*u, 1-2*v
    D, L, M = HALF-d[3]-d[4]-d[5], d[1]+d[2], d[6]+d[7]
    r, q = h[3]-lu*D, h[5]-2*v*D
    RS, RW = lv*r+lu*q, v*r+u*q
    NS, NW = RS**2-2*lu*lv*d[4], RW**2-2*u*v*d[4]
    ES, FW = h[2]*RS-lv*(h[2]-d[3]), h[6]*RW-u*(h[6]-d[5])
    side_s, side_w = lv-RS+2*K*h[2], u-RW+K*h[6]
    assert s.expand(NS-4*K*ES+4*K*K*h[2]**2-side_s**2) == 0
    assert s.expand(NW-2*K*FW+K*K*h[6]**2-side_w**2) == 0
    assert s.expand(side_s-lv*h[4]-2*K*(HALF-d[2]-d[3]-d[4])) == 0
    assert s.expand(side_w-u*h[4]-K*(HALF-d[4]-d[5]-d[6])) == 0
    assert s.cancel(r+u/v*q+K/v*(M+h[7])+side_w/v-1) == 0
    assert s.cancel(side_s/lu+2*K/lu*(h[1]+L)+lv/lu*r+q-1) == 0
    t = s.Symbol('t')
    assert s.expand(2*t*(L+h[1]+h[2])+(1-2*t)*(M+h[6]+h[7])-1) == 0
    assert s.expand(r+q+2*K*D-HALF-d[4]) == 0

    # Zero mixed determinants force these explicit deficit faces.
    ds = s.factor(NS-ES**2/h[2]**2)
    dw = s.factor(NW-FW**2/h[6]**2)
    assert s.cancel(ds-2*lv**2*d[3]/h[2]**2*(d[2]*(h[2]-d[3])
                        +lu/lv*h[2]*(h[2]-d[3]-d[4]))) == 0
    assert s.cancel(dw-2*u**2*d[5]/h[6]**2*(d[6]*(h[6]-d[5])
                        +v/u*h[6]*(h[6]-d[5]-d[4]))) == 0
    assert s.expand((2*r*q-d[4]-2*D*(lv/2-lu*q)).subs(d[3], 0)) == 0
    assert s.expand((2*r*q-d[4]-4*D*(u/2-v*r)).subs(d[5], 0)) == 0

    # Minkowski expansion: <T,T>>0 and <T,a+b>>0 make every
    # middle projected edge strictly shorter than its horizontal weight.
    tt, ta, tb = s.symbols('TT TA TB')
    c_mass = 2*d[4]+4*K*(ta+tb)+4*K*K*tt
    middle_mass = 1-2*(HALF+d[4])+c_mass
    assert s.expand(middle_mass-4*K*(ta+tb)-4*K*K*tt) == 0
    assert s.expand(h[3]+h[4]+h[5]-1-D) == 0
    return {'last_side_square_identities': 2, 'positive_side_factors': 2,
            'unit_section_perimeters': 3, 'zero_mixed_discriminants': 2,
            'negative_parallel_zero_branches': 2, 'timelike_middle_edges': 3}


def verify():
    return {'source': metric.metric_bindings(), 'coordinates': coordinate_checks(),
            'scalars': scalar_checks(), 'assumptions': ['ray1', 'regular positive C0 caps', '0<u<v<1/2'],
            'new_exclusion_claimed': False}


if __name__ == '__main__':
    if not __debug__:
        raise RuntimeError('run with assertions enabled')
    start = time.monotonic()
    record = verify()
    record['seconds'] = round(time.monotonic()-start, 3)
    print(json.dumps(record), flush=True)
