#!/usr/bin/env python3
"""Exact section obstruction for the upper-a/coincident common-axis family.

This excludes the specified geometric family, not every one-collinear
C0 limit.  The source checks use no numerical or Boolean solver.
"""

import json
import time

import sympy as s

import remaining_c0_height_order as metric
import solver_remaining_c0_sections as sections
import solver_remaining_chambers as shared


def checks():
    half = s.Rational(1, 2)
    alpha, beta, w = s.symbols('alpha beta w')
    length, mass, x4, x5, x7, y7 = s.symbols('L M x4 x5 x7 y7')
    points = [s.zeros(2, 1), s.zeros(2, 1), s.Matrix((-half, 0)),
              s.Matrix((-length, 0)), s.Matrix((x4, 0)),
              s.Matrix((x5, 0)), s.Matrix((mass, 0)), s.Matrix((x7, y7))]
    levels = (0, 1, 1, 1, alpha, beta, 0, 0)
    direct_edges = ((0, 1), (0, 3), (0, 2), (2, 7), (1, 7), (1, 6))
    upper_edges = ((3, 4), (1, 4), (2, 4), (2, 5), (3, 5), (3, 6))
    faces = set(shared.base_formula()[2])

    def section(edge):
        i, j = edge
        fraction = (w-levels[i])/(levels[j]-levels[i])
        return (1-fraction)*points[i]+fraction*points[j]

    direct, upper = tuple(map(section, direct_edges)), tuple(map(section, upper_edges))
    expected = (points[0], w*points[3], w*points[2],
                w*points[2]+(1-w)*points[7], (1-w)*points[7], (1-w)*points[6])
    assert all(s.cancel(value) == 0 for actual, target in zip(direct, expected)
               for value in actual-target)
    assert all(point[1] == 0 for point in upper)
    assert s.cancel(upper[1][0]-(1-w)*x4/(1-alpha)) == 0
    assert s.cancel(upper[4][0]+length-(1-w)*(x5+length)/(1-beta)) == 0
    for index in (3, 4):
        assert s.expand(direct[index][1]-(1-w)*y7) == 0
    for edges in (direct_edges, upper_edges):
        for index, edge in enumerate(edges):
            assert tuple(sorted(set(edge) | set(edges[(index+1) % len(edges)]))) in faces

    u, v, d0, p, q, g = s.symbols('u v d0 p q g')
    lu, lv, k = 1-2*u, 1-2*v, v-u
    h2, h3 = half-length, half-p
    D = d0+length+mass
    budget = {g: half-D-p-q}
    r, radius_s = h3-lu*D, half-g-2*v*D
    assert s.expand((r-q-g-2*u*D).subs(budget)) == 0
    assert s.expand((radius_s-p-q-lv*D).subs(budget)) == 0
    # Q4 is negative after the direct-annulus containment bound at edge14.
    # In the Q5-positive case, its dot product with Q4 forces q=0.
    positive_q5 = -h2*(lv*r+lu*radius_s)-h2*(lv*r+lu*radius_s)+lv*(h2-p)
    assert s.expand(positive_q5.subs(budget).subs(q, 0)
                    +p*(lv+4*h2*k)) == 0
    # In the Q5-negative case, the E.S equation gives 2*h2*r=h2-p.
    negative_q5 = h2*(-lv*r+lu*radius_s)-h2*(lv*r+lu*radius_s)+lv*(h2-p)
    assert s.expand(negative_q5-lv*(h2-p-2*h2*r)) == 0
    assert s.expand(h2-p-2*h2*r-2*(h2*lu*D-length*p)) == 0
    # q=2*r*s and s=p+q+lv*D then give s=h2+lv*L/lu.
    rr, ss = s.symbols('r s')
    assert s.cancel((ss-p-2*rr*ss-lv*D).subs(rr, (h2-p)/(2*h2))
                    -(p*ss/h2-p-lv*D)) == 0
    assert s.cancel((h2+h2*lv*D/p).subs(D, length*p/(h2*lu))
                    -h2-lv*length/lu) == 0
    candidate_x5 = -2*v*length+lv*mass-(h2+lv*length/lu)
    assert s.cancel(candidate_x5+v-lv*(mass-h2-length/lu)) == 0
    assert s.cancel(h2+length/lu-half-2*u*length/lu) == 0
    # For Q4=-r,Q5=+s the weak lower mixed sign fails.
    F = points[7]-points[6]
    W = s.Matrix((-v*rr-u*ss, 0))
    assert s.expand(-s.det(s.Matrix.hstack(W, F))-(v*rr+u*ss)*y7) == 0
    return {'closed_metric_source': metric.metric_bindings(),
            'annulus_source': sections.coordinate_checks(),
            'section_face_bindings': 12,
            'radius_sign_cases': 4,
            'scope': 'ray1 C0, 0<u<v<1/2, d1=0, regular positive067, P2/P4/P5/P6 collinear',
            'specified_family_excluded': True,
            'whole_one_collinear_interior_excluded': False,
            'numerical_or_boolean_solver_used': False}


if __name__ == '__main__':
    if not __debug__:
        raise RuntimeError('run with assertions enabled')
    started = time.monotonic()
    result = checks()
    result['seconds'] = time.monotonic()-started
    print(json.dumps(result, indent=2))
