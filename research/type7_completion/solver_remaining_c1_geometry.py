#!/usr/bin/env python3
"""Exact circle and dot-product identities on the full closed C1 component.

No nonzero triangle area, q scale, or small weight is divided out. The
identities are useful necessary conditions for both remaining markings;
this module does not assert that the component is excluded.
"""

import json

import sympy as s

import exhaustive_remaining_axis as axis
import exhaustive_remaining_locus as locus
import solver_remaining_limit as reducer


def horizontal_displacements(weights):
    """All local edges in terms of cyclic signed horizontal weights."""
    _, _, edges = axis.case_data(1)
    answer = {}
    for i, j in edges:
        distance = (j-i) % 8
        if distance <= 3:
            origin, length, sign = i, distance, 1
        else:
            origin, length, sign = j, 8-distance, -1
        assert 1 <= length <= 3
        answer[i, j] = sign*((0 if length == 1 else 1)
                            -sum(weights[(origin+k) % 8] for k in range(length)))
    return answer


def verify():
    alpha, beta = s.symbols('alpha beta')
    h = s.symbols('h0:8')
    delta = [s.Rational(1, 2)-weight for weight in h]
    X = horizontal_displacements(h)
    area_records = {}
    for mark in (1, 2):
        shifts, faces, edges = axis.case_data(mark)
        x = [s.Integer(0)]
        for i in range(7):
            shift = shifts[i, i+1]
            x.append(s.expand(x[-1]-h[i]-shift[0]-s.Rational(shift[1], 2)))
        closure = {h[7]: s.Rational(9, 2)-mark-sum(h[:7])}
        for i, j in edges:
            actual = x[j]-x[i]+shifts[i, j][0]+s.Rational(shifts[i, j][1], 2)
            assert s.expand(actual-X[i, j].subs(closure)) == 0
        v = (0, alpha/2, s.Rational(1, 2), s.Rational(1, 2),
             s.Rational(1, 2), -beta/2, 0, 0)
        areas = []
        for i, j, k in faces:
            dxj = x[j]-x[i]+shifts[i, j][0]+s.Rational(shifts[i, j][1], 2)
            dxk = x[k]-x[i]+shifts[i, k][0]+s.Rational(shifts[i, k][1], 2)
            dyj = v[j]-v[i]+shifts[i, j][1]
            dyk = v[k]-v[i]+shifts[i, k][1]
            areas.append(s.expand(dxj*dyk-dxk*dyj))
        assert s.expand(sum(areas)) == 2
        area_records[str(mark)] = {'oriented_area_sum': '2', 'face_count': len(areas)}

    P = [s.zeros(2, 1), s.zeros(2, 1)]
    P.extend(s.Matrix(s.symbols(f'u{i} z{i}')) for i in range(2, 8))
    norm = lambda value: s.expand(value.dot(value))
    T = {edge: norm(P[edge[1]]-P[edge[0]])-X[edge]**2 for edge in X}
    F12 = (alpha-1)*(T[0, 1]-alpha*T[0, 2])-alpha*T[1, 2]
    F13 = (alpha-1)*(T[0, 1]-alpha*T[0, 3])-alpha*T[1, 3]
    F0 = T[0, 1]-alpha*T[0, 2]-T[1, 7]+alpha*T[2, 7]
    S = T[3, 5]-(1-beta)*T[3, 6]-T[4, 5]+(1-beta)*T[4, 6]
    V = -beta*T[3, 5]+beta*(1-beta)*T[3, 6]-(1-beta)*T[5, 6]
    D = T[5, 7]-T[5, 6]-beta*(T[4, 7]-T[4, 6])

    # Independently bind the six named stresses to the full 29-row system.
    ts = {edge: s.Symbol(f'T{edge[0]}{edge[1]}') for edge in X}
    formal = [
        (alpha-1)*(ts[0, 1]-alpha*ts[0, 2])-alpha*ts[1, 2],
        (alpha-1)*(ts[0, 1]-alpha*ts[0, 3])-alpha*ts[1, 3],
        ts[0, 1]-alpha*ts[0, 2]-ts[1, 7]+alpha*ts[2, 7],
        ts[3, 5]-(1-beta)*ts[3, 6]-ts[4, 5]+(1-beta)*ts[4, 6],
        -beta*ts[3, 5]+beta*(1-beta)*ts[3, 6]-(1-beta)*ts[5, 6],
        ts[5, 7]-ts[5, 6]-beta*(ts[4, 7]-ts[4, 6]),
    ]
    matrix = reducer.original_system(locus.components()[1]['values']).subs(
        {locus.A: alpha/2, locus.B: -beta/2}, simultaneous=True)
    for index, expression in enumerate(formal):
        row = [s.diff(expression, ts[edge]) for edge in reducer.EDGES]+[s.Integer(0)]*5
        if index == 5:
            row[28] = -1
        assert all(s.expand(value) == 0 for value in s.Matrix([row])*matrix)

    E2, E3, F = P[2]-P[3], P[4]-P[3], P[7]-P[6]
    R1, Y0 = -alpha*P[3], alpha*P[2]
    rho1 = alpha*(1-h[1]-h[2])+(1-alpha)*h[0]
    sigma0 = (1-alpha)*(1-h[0])+alpha*h[1]
    R5 = P[5]-beta*P[3]-(1-beta)*P[6]
    Y5 = beta*E3-R5
    rho5 = beta*(1-h[3]-h[4])+(1-beta)*h[5]
    sigma5 = (1-beta)*(1-h[5])+beta*h[4]

    circle1 = norm(R1)-rho1**2
    dot1 = R1.dot(E2)+h[2]*rho1-delta[1]
    norm0 = norm(Y0)-sigma0**2+2*(1-alpha)*delta[0]
    dot0 = Y0.dot(P[7])+h[7]*sigma0-delta[0]
    circle5 = norm(R5)-rho5**2
    dot4 = R5.dot(E3)+h[3]*rho5-delta[4]
    norm5 = norm(Y5)-sigma5**2+2*(1-beta)*delta[5]
    dot5 = Y5.dot(F)+h[6]*sigma5-delta[5]
    identities = {
        'circle1': circle1+F13,
        'dot1': 2*alpha*dot1-F12+F13-alpha**2*T[2, 3],
        'norm0': norm0+F12,
        'dot0': 2*dot0-(alpha-1)*T[0, 7]+F0,
        'circle5': circle5+V,
        'dot4': 2*dot4-S-beta*T[3, 4],
        'norm5': norm5-circle5+beta*S,
        'dot5': 2*dot5-D+(1-beta)*T[6, 7],
    }
    for expression in identities.values():
        assert s.expand(expression) == 0
    assert all(s.expand(value) == 0 for value in R1+Y0-alpha*E2)
    assert all(s.expand(value) == 0 for value in R5+Y5-beta*E3)
    assert s.expand(rho1+sigma0-(1-alpha*h[2])) == 0
    assert s.expand(rho5+sigma5-(1-beta*h[3])) == 0

    return {'scalar_identities': list(identities), 'linked_vector_pairs': 2,
            'linked_radius_sums': 2, 'full_system_stress_bindings': 6,
            'markings': area_records,
            'domain': '1/4 <= alpha <= 1; 0 <= beta <= 1; 0 <= h_i <= 1/2',
            'exceptional_upper_cap': 'alpha=beta=1: q24 is retained',
            'component_exclusion': False}


if __name__ == '__main__':
    if not __debug__:
        raise RuntimeError('run with assertions enabled')
    print(json.dumps(verify()), flush=True)
