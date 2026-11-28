#!/usr/bin/env python3
"""Exact nonedge bounds for the regular C0 region 0<u<v<1/2.

The companion derives the limiting inequalities from two explicit
lattice lifts.  This checker verifies their product factors, all source
row combinations, and the resulting vector norm and dot formulas.
These two norm bounds also follow from the existing circle identities;
they do not strengthen the metric locus or exclude this height region.
"""

import json
import time

import sympy as sym

import exhaustive_remaining_axis as axis
import solver_remaining_c1_geometry as geometry
import solver_remaining_limit as reduction


def verify():
    half = sym.Rational(1, 2)
    u, v = sym.symbols('u v')
    lu, lv, gap = 1-2*u, 1-2*v, v-u
    h = list(sym.symbols('h0:7'))
    h.append(sym.Rational(7, 2)-sum(h))
    d = [half-value for value in h]
    L, M = d[1]+d[2], d[6]+d[7]
    D = half-d[3]-d[4]-d[5]
    P = [sym.zeros(2, 1), sym.zeros(2, 1)]
    P.extend(sym.Matrix(sym.symbols(f'x{i} y{i}')) for i in range(2, 8))
    norm = lambda point: point.dot(point)
    X = geometry.horizontal_displacements(h)
    T = {edge: sym.expand(norm(P[edge[1]]-P[edge[0]])-value**2)
         for edge, value in X.items()}

    # The explicit lift vectors are (1,-1) for 04 and (-1,1) for 15.
    # Reconstruct horizontal coordinates from the marked cyclic edges.
    shifts, _, _ = axis.case_data(1)
    intrinsic_x = [sym.Integer(0)]
    for i in range(7):
        shift = shifts[i, i+1]
        intrinsic_x.append(intrinsic_x[-1]-h[i]-shift[0]-half*shift[1])
    x04 = sym.Rational(3, 2)-sum(h[:4])
    x15 = 2-sum(h[1:5])
    assert sym.expand(intrinsic_x[4]+1-half-x04) == 0
    assert sym.expand(intrinsic_x[5]-intrinsic_x[1]-1+half-x15) == 0

    # These exact generic products are divided by the inverse-height
    # parameter before taking the C0 limit.  No product scale is zeroed.
    v1, v3, v4, v5 = sym.symbols('v1 v3 v4 v5')
    a, c, dd, f = v1-v3, v3-v4, v3-v5-1, 2*v3-1
    p05, p14 = f*(2*dd+1), -4*a*c
    p04 = (2*v3-v4)**2-(v4-1)**2
    p15 = (2*v3-v5-1-v1)**2-(v5-v1+1)**2
    assert sym.expand(p04-f*(2*c+1)) == 0
    assert sym.expand(p15+4*a*dd) == 0
    assert sym.expand((2*dd+1)*p04-(2*c+1)*p05) == 0
    assert sym.expand(c*p15-dd*p14) == 0
    at_c0 = {v1: half, v3: half, v4: 1-u, v5: -v}
    assert sym.cancel(((2*c+1)/(2*dd+1)).subs(at_c0)-u/v) == 0
    assert sym.cancel((dd/c).subs(at_c0)-lv/lu) == 0

    original = reduction.original_system((half, half, half, 1-u, -v, 0))
    aux04 = u/v*reduction.QS[0]+2*u*reduction.H[4]
    aux15 = lv/lu*reduction.QS[1]-lv*(reduction.H[5]-reduction.H[1])
    combinations = (
        {(0, 5): u/v, (3, 4): -2*u/lu, (3, 5): 2*u/lv},
        {(1, 4): lv/lu, (3, 4): -lv/lu, (3, 5): 1},
    )
    for coefficients, auxiliary in zip(combinations, (aux04, aux15)):
        row = sym.Matrix([[coefficients.get(edge, 0) for edge in reduction.EDGES]+[0]*5])
        target = sym.Matrix([[sym.diff(auxiliary, variable) for variable in reduction.AUXILIARIES]])
        assert all(sym.cancel(value) == 0 for value in row*original-target)

    T04, T15 = norm(P[4])-x04*x04, norm(P[5])-x15*x15
    residual04 = T04-sum(coefficient*T[edge] for edge, coefficient in combinations[0].items())
    residual15 = T15-sum(coefficient*T[edge] for edge, coefficient in combinations[1].items())
    U = 2*u*T[3, 4]+lu*T[4, 6]-2*u*lu*T[3, 6]
    V = 2*v*T[3, 5]+lv*T[5, 6]-2*v*lv*T[3, 6]
    J = (T[4, 5]-2*u*T[3, 5]-lu*T[5, 6]-2*v*T[3, 4]-lv*T[4, 6]
         +(2*u*lv+2*v*lu)*T[3, 6])
    C = lv*(T[2, 4]-T[3, 4])-lu*(T[2, 5]-T[3, 5])
    K = v*(T[4, 7]-T[4, 6])-u*(T[5, 7]-T[5, 6])

    # Independently bind every equality used in the vector consequences.
    formal = sym.symbols('T0:24')
    formal_T = dict(zip(reduction.EDGES, formal))
    stress_expressions = (
        2*u*formal_T[3, 4]+lu*formal_T[4, 6]-2*u*lu*formal_T[3, 6],
        2*v*formal_T[3, 5]+lv*formal_T[5, 6]-2*v*lv*formal_T[3, 6],
        formal_T[4, 5]-2*u*formal_T[3, 5]-lu*formal_T[5, 6]
        -2*v*formal_T[3, 4]-lv*formal_T[4, 6]
        +(2*u*lv+2*v*lu)*formal_T[3, 6],
        lv*(formal_T[2, 4]-formal_T[3, 4])-lu*(formal_T[2, 5]-formal_T[3, 5]),
        v*(formal_T[4, 7]-formal_T[4, 6])-u*(formal_T[5, 7]-formal_T[5, 6]),
    )
    source_rows = []
    for i, expression in enumerate(stress_expressions):
        row = [sym.diff(expression, variable) for variable in formal]+[sym.Integer(0)]*5
        if i == 3:
            row[25] = -1
        if i == 4:
            row[28] = half
        source_rows.append(row)
    for edge in ((1, 2), (1, 3), (0, 6), (0, 7)):
        source_rows.append([sym.Integer(edge == other) for other in reduction.EDGES]+[sym.Integer(0)]*5)
    assert all(sym.expand(value) == 0 for value in sym.Matrix(source_rows)*original)

    r, s = h[3]-lu*D, h[5]-2*v*D
    RS, RW = lv*r+lu*s, v*r+u*s
    Sigma, Tau = RS+2*gap*L, RW+gap*M
    BS, BW = Sigma*Sigma-2*lu*lv*d[4], Tau*Tau-2*u*v*d[4]
    S0, W0 = lv*P[4]-lu*P[5], v*P[4]-u*P[5]
    norm_error = lv*lv*U+lu*lu*V+lu*lv*J
    # Positive factors 2*(v-u)*lu and (v-u)*v give the two upper bounds.
    assert sym.cancel(2*gap*lu*residual15-norm(S0)+BS+norm_error) == 0
    assert sym.cancel(gap*v*residual04-norm(W0)+BW
                      +u*v/(lu*lv)*norm_error) == 0

    E, F = P[3]-P[2], P[7]-P[6]
    dotS = h[2]*Sigma-lv*(h[2]-d[3])-2*gap*d[1]
    dotW = h[6]*Tau-u*(h[6]-d[5])-gap*d[7]
    assert sym.expand(E.dot(S0)-dotS-C/2-gap*(T[1, 2]-T[1, 3])) == 0
    assert sym.expand(F.dot(W0)-dotW+K/2-gap*(T[0, 7]-T[0, 6])/2) == 0

    # Useful positive scalar representation, without asserting a joint
    # Gram identity for S0,W0 from their two separate upper bounds.
    rhat = r+lu*M-2*u*L
    shat = s+2*v*L-lv*M
    assert sym.expand(rhat-(d[4]+d[5]+M+2*u*d[0])) == 0
    assert sym.expand(shat-(L+d[3]+d[4]+lv*d[0])) == 0
    assert sym.expand(Sigma-lv*rhat-lu*shat) == 0
    assert sym.expand(Tau-v*rhat-u*shat) == 0
    Q4, Q5 = P[4]-2*u*P[3]-lu*P[6], P[5]-2*v*P[3]-lv*P[6]
    S, W = lv*Q4-lu*Q5, v*Q4-u*Q5
    assert all(sym.expand(value) == 0 for value in S0-S+2*gap*P[3])
    assert all(sym.expand(value) == 0 for value in W0-W-gap*P[6])
    assert sym.expand(r-d[4]-d[5]-2*u*D) == 0
    assert sym.expand(s-d[3]-d[4]-lv*D) == 0
    return {'explicit_nonedge_lifts': 2, 'generic_product_identities': 4,
            'nonedge_auxiliary_bindings': 2, 'metric_source_bindings': 9,
            'norm_upper_bounds': 2, 'exact_dot_identities': 2,
            'norm_bounds_strengthen_metric_locus': False,
            'remaining_height_region_excluded': False}


if __name__ == '__main__':
    if not __debug__:
        raise RuntimeError('run with assertions enabled')
    started = time.monotonic()
    result = verify()
    result['seconds'] = round(time.monotonic()-started, 3)
    print(json.dumps(result), flush=True)
