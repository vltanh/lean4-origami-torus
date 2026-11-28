#!/usr/bin/env python3
"""Relative unit directions at every short endpoint-cap edge of interior C0.

The estimates hold for both remaining markings and every collapse rate.
This exact source package is a scale lemma, not an exclusion theorem.
"""

import argparse
import json
from pathlib import Path

import sympy as s

import exhaustive_c0_collinear as boundary
import exhaustive_c0_double_coincidence as diagonal
import exhaustive_remaining_axis as axis
import remaining_c1_short_edges as edge23
import solver_remaining_c1_geometry as geometry

HALF = s.Rational(1, 2)


def relative12_checks():
    t, ell, b, length, ratio, a, g = s.symbols('t ell b h r a g')
    norm, other_norm, dot, theta, vertical, horizontal = s.symbols('W2 Q2 dot theta V14 X14')
    h0 = HALF-ratio*length
    k = h0+ratio-1
    x02 = 1-h0-length
    assert s.expand(x02-HALF-(ratio-1)*length) == 0
    e01 = ell**2-b**2-t*h0**2
    e12 = t*length**2*norm+t*t*length**2*a*a-t*length**2-t*t*length**2*g*g
    e02 = t*length**2*norm+(ell+t*length*a)**2-t*x02*x02-(b+t*length*g)**2
    polar = ell*a-b*g-k
    assert s.expand(e02-e01-e12-2*t*length*polar) == 0
    e14 = t*other_norm+theta*theta-t*horizontal**2-vertical**2
    e24 = (t*(other_norm+length**2*norm-2*length*dot)
           +(theta-t*length*a)**2-t*(horizontal+length)**2
           -(vertical-t*length*g)**2)
    second = dot+a*theta+horizontal-g*vertical
    assert s.expand(e12+e14-e24-2*t*length*second) == 0
    target = ell**2*norm-ell**2-t*t*h0*h0*g*g+2*t*b*k*g+t*k*k
    witness = ell**2*e12/(t*length**2)+t*g*g*e01 \
        -t*polar*(ell*a+b*g+k)
    assert s.cancel(target-witness) == 0
    coefficient = b*theta/ell-vertical
    rhs = -horizontal-dot-k*theta/ell
    assert s.cancel(coefficient*g-rhs-second+theta*polar/ell) == 0
    u = s.Symbol('u')
    assert s.cancel(coefficient.subs({ell: HALF, b: HALF, theta: u-HALF,
                                     vertical: HALF-u})+(1-2*u)) == 0
    weights = s.symbols('h0:8')
    X = geometry.horizontal_displacements(weights)
    assert s.expand(X[0, 2]-(1-weights[0]-weights[1])) == 0
    assert s.expand(X[1, 2]+weights[1]) == 0
    assert s.expand(X[2, 4]-X[1, 4]-weights[1]) == 0
    for mark in (1, 2):
        shifts, _, _ = axis.case_data(mark)
        assert all(shifts[pair][1] == 0 for pair in ((0, 1), (0, 2), (1, 2), (1, 4), (2, 4)))
        assert tuple(shifts[1, 2][i]+shifts[2, 4][i]-shifts[1, 4][i]
                     for i in (0, 1)) == (0, 0)
    return {'finite_axis_polarization': True, 'finite_face124_polarization': True,
            'finite_relative_norm_identity': True,
            'nonzero_limiting_coefficient': '-(1-2u)', 'marked_sources': [1, 2]}


def endpoint_checks():
    """Finite core/cap identities used at the h1=0 endpoint."""
    t, ell, b, h0, h, h2, h7 = s.symbols('t ell b h0 h h2 h7')
    a, g, a3, g3, z7, v7 = s.symbols('a g a3 g3 z7 v7')
    nw, n3, n7, dot3, dot7 = s.symbols('W2 P3sq P7sq WdotP3 WdotP7')
    L = 1-h-h2
    x02, x17 = 1-h0-h, h0+h7-1
    e01 = ell**2-b**2-t*h0**2
    e02 = t*h*h*nw+(ell+t*h*a)**2-t*x02*x02-(b+t*h*g)**2
    e17 = t*n7+(z7-ell)**2-t*x17*x17-(v7-b)**2
    e27 = t*(n7+h*h*nw-2*h*dot7)+(z7-ell-t*h*a)**2 \
        -t*(x17+h)**2-(v7-b-t*h*g)**2
    core = h*dot7+h*(z7*a-v7*g)-(HALF-h0)+h*h7
    assert s.expand(e02-e01-e27+e17-2*t*core) == 0
    e12 = t*h*h*nw+t*t*h*h*a*a-t*h*h-t*t*h*h*g*g
    e13 = t*n3+t*t*a3*a3-t*L*L-t*t*g3*g3
    e23 = t*(n3+h*h*nw-2*h*dot3)+t*t*(a3-h*a)**2 \
        -t*h2*h2-t*t*(g3-h*g)**2
    cap = h*dot3+t*h*(a*a3-g*g3)-(h*h+L*L-h2*h2)/2
    assert s.expand(e12+e13-e23-2*t*cap) == 0
    d2 = s.Symbol('d2')
    assert s.cancel(((h*h+L*L-h2*h2)/(2*h)).subs(h2, HALF-d2)
                    -(d2/h-HALF-d2+h)) == 0
    X = geometry.horizontal_displacements(s.symbols('h0:8'))
    hh = s.symbols('h0:8')
    assert s.expand(X[1, 7]-(hh[0]+hh[7]-1)) == 0
    assert s.expand(X[2, 7]-X[1, 7]-hh[1]) == 0
    shifts, _, _ = axis.case_data(1)
    assert shifts[1, 7][1] == shifts[2, 7][1] == 0
    return {'finite_core_polarization': True, 'finite_upper_cap_polarization': True,
            'endpoint_limits': 'd0/h1=d2/h1 -> (1+w_x)/2; w_x<=0',
            'bounded_13_source': diagonal.metric_checks()}


def exact_checks():
    edge23_source = edge23.relative_metric_checks()
    # Its finite equations are unchanged. In C0 the limit coefficient
    # is -(1-2v), obtained by alpha=1, beta=2v in the source calculation.
    v, beta = s.symbols('v beta')
    assert s.expand((-(1-beta)).subs(beta, 2*v)+(1-2*v)) == 0
    reflection = boundary.symmetry_checks()
    p = reflection['permutation']
    assert {tuple(sorted(pair)) for pair in ((1, 2), (2, 3),
            (p[1], p[2]), (p[2], p[3]))} == {(1, 2), (2, 3), (6, 7), (0, 7)}
    return {'relative12': relative12_checks(), 'relative23': edge23_source,
            'C0_edge23_coefficient': '-(1-2v)', 'reflection': reflection,
            'cap_edge_cover': [(1, 2), (2, 3), (6, 7), (0, 7)],
            'endpoint': endpoint_checks()}


if __name__ == '__main__':
    if not __debug__:
        raise RuntimeError('run with assertions enabled')
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('output', type=Path)
    output = parser.parse_args().output
    output.mkdir(parents=True, exist_ok=True)
    result = {'checks': exact_checks(), 'domain': 'both markings; interior C0',
              'conclusion': 'unit transverse cap-edge directions with axial/intrinsic errors O(t*h)',
              'relative_rate_assumptions': [], 'exclusion_claimed': False}
    (output/'c0_short_edges.json').write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps({'relative_edge_sources': 2, 'cap_edges': 4, 'exclusion_claimed': False}))
