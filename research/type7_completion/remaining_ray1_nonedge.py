#!/usr/bin/env python3
"""An exact nonedge15 cut at the remaining ray-1 endpoint.

Usage: python remaining_ray1_nonedge.py

The cut proves b1>=-o(h1), excluding the negative-axial endpoint regime.
It uses two metric equalities and one already-required nonedge translate;
it has no Boolean or nonlinear-solver dependency.
"""

import json
import time

import sympy as s

import exhaustive_remaining_axis as axis


def exact_checks():
    shifts, _, edges = axis.case_data(1)
    assert (1, 5) not in edges
    assert (1, 2) in edges and (2, 5) in edges
    assert shifts[1, 2] == (-1, 0)
    assert shifts[2, 5] == (-1, 1)
    # The candidate nonedge translate is also(-1,1), one of the original
    # bounds -4<=kx<=4,-3<=ky<=3. No extra distance condition is imposed.
    assert -4 <= -1 <= 4 and -3 <= 1 <= 3

    half = s.Rational(1, 2)
    d0, d2, d3, d4, d5, d6, d7 = s.symbols('d0 d2 d3 d4 d5 d6 d7')
    h = d0+d2+d3+d4+d5+d6+d7
    x1 = -half+d0
    x2 = half+d0-h
    x5 = half-d5-d6-d7
    deficit = d0+d5+d6+d7
    x15 = x5-x1-1+half
    x25 = x5-x2+shifts[2, 5][0]+half*shifts[2, 5][1]
    assert s.expand(x15-(half-deficit)) == 0
    assert s.expand(x25-(x15-1+h)) == 0
    assert s.expand(x15*x15-x25*x25-(1-h)*(h-2*deficit)) == 0

    h, r, t, b, lam, ell, v = s.symbols('h R t b1 lambda ell V15')
    p2, n2, p5, n5, z5 = s.symbols('P2 Z2 P5 Z5 zeta5')
    z2 = ell+b+t*lam
    actual12 = t*(p2*p2+n2*n2)+(b+t*lam)**2
    actual25 = t*((p5-p2)**2+(n5-n2)**2)+(z5-z2)**2
    actual15 = t*(p5*p5+n5*n5)+(z5-ell)**2
    e12 = actual12-(t*h*h+b*b)
    e25 = actual25-(t*(-half+h-r)**2+(v-b)**2)
    e15 = actual15-(t*(half-r)**2+v*v)
    transverse_dot = (p5-p2)*p2+(n5-n2)*n2
    target = (t*(h*h-(1-h)*(h-2*r))+2*b*b-2*v*b
              +2*t*transverse_dot+2*(z5-z2)*(b+t*lam))
    assert s.expand(e15-e25-e12-target) == 0
    # The endpoint coefficient of b1 is2*(-1/2-1/2)=-2.
    assert 2*(-half-half) == -2
    return {'nonedge': '15', 'translate': [-1, 1], 'metric_rows': ['12', '25'],
            'horizontal_deficit': 'R=d0+d5+d6+d7, 0<=R<=h1',
            'exact_identity': str(target),
            'endpoint_cut': 'b1>=-o(h1)',
            'negative_axial_gap_divided_by_h1': '2'}


def main():
    start = time.monotonic()
    result = exact_checks()
    result.update(negative_axial_regime_excluded=True, whole_endpoint_excluded=False,
                  seconds=round(time.monotonic()-start, 3))
    print(json.dumps(result), flush=True)


if __name__ == '__main__':
    if not __debug__:
        raise RuntimeError('run with assertions enabled')
    main()
