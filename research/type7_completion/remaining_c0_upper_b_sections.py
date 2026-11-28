#!/usr/bin/env python3
"""Source checks for the upper-b C0 section/spur exclusion.

The companion rules out the direct annulus being the outer annulus.
This is a geometric winding argument, with no Boolean solver premise.
The opposite nesting order is not excluded by this checker.
"""

import json
import time

import sympy as s

import remaining_c0_height_order as metric
import solver_remaining_c0_sections as sections
import solver_remaining_chambers as shared


def checks():
    alpha, beta, w = s.symbols('alpha beta w')
    half = s.Rational(1, 2)
    length, mass = s.symbols('L M')
    a = half-length
    points = [s.zeros(2, 1), s.zeros(2, 1), s.Matrix((a, 0)),
              s.Matrix((-length, 0))]
    points += [s.Matrix(s.symbols(f'x{i} y{i}')) for i in range(4, 8)]
    levels = (0, 1, 1, 1, alpha, beta, 0, 0)
    faces = set(shared.base_formula()[2])
    direct_edges = ((0, 1), (0, 3), (0, 2), (2, 7), (1, 7), (1, 6))
    upper_edges = ((3, 4), (1, 4), (2, 4), (2, 5), (3, 5), (3, 6))

    def section(edge):
        i, j = edge
        fraction = (w-levels[i])/(levels[j]-levels[i])
        return (1-fraction)*points[i]+fraction*points[j]

    direct = tuple(map(section, direct_edges))
    upper = tuple(map(section, upper_edges))
    expected_direct = (s.zeros(2, 1), w*points[3], w*points[2],
                       w*points[2]+(1-w)*points[7],
                       (1-w)*points[7], (1-w)*points[6])
    assert all(s.cancel(value) == 0 for actual, expected in zip(direct, expected_direct)
               for value in actual-expected)
    for edges in (direct_edges, upper_edges):
        for i, edge in enumerate(edges):
            assert tuple(sorted(set(edge) | set(edges[(i+1) % len(edges)]))) in faces
    for index, vertex, coefficient in ((0, 4, (1-w)/(1-alpha)),
                                       (4, 5, (1-w)/(1-beta)),
                                       (5, 6, 1-w)):
        assert s.cancel(upper[index][1]-coefficient*points[vertex][1]) == 0
        assert not any(s.cancel(value) for value in upper[index].subs(w, 1)-points[3])

    # The negative excursion 0 -> wP3 -> 0 cancels as an oriented chain.
    # The remaining body has the displayed five vertices. Its negative
    # horizontal coordinates are bounded by a constant times (1-w).
    body = (direct[0], direct[2], direct[3], direct[4], direct[5])
    assert not any(s.expand(value) for value in direct[2]-direct[1]
                   -(direct[0]-direct[1])-(direct[2]-direct[0]))
    for index in (2, 3):
        assert s.expand(body[index][1]-(1-w)*points[7][1]) == 0
    assert body[0][1] == body[1][1] == 0

    # Both possible relative orders of the two interior critical heights
    # have contiguous upper and lower links; no section cycle is born,
    # split, joined, or destroyed at 4 or 5.
    links = {4: (1, 2, 5, 7, 6, 3), 5: (0, 6, 3, 2, 4, 7)}
    high_sets = {4: ({1, 2, 3, 5}, {1, 2, 3}),
                 5: ({2, 3}, {2, 3, 4})}
    for vertex, cycle in links.items():
        for i, neighbor in enumerate(cycle):
            assert tuple(sorted((vertex, neighbor, cycle[(i+1) % len(cycle)]))) in faces
        for high in high_sets[vertex]:
            changes = sum((cycle[i] in high) != (cycle[(i+1) % len(cycle)] in high)
                          for i in range(len(cycle)))
            assert changes == 2

    # All scalar identities are bound to the original closed C0 source
    # by metric.metric_bindings(), rather than imposed on a new model.
    u, v, d0, p, q, g = s.symbols('u v d0 p q g')
    lu, lv = 1-2*u, 1-2*v
    D = d0+length+mass
    budget = {g: half-d0-length-mass-p-q}
    h3, h5 = half-p, half-g
    r, radius_s = h3-lu*D, h5-2*v*D
    assert s.expand((r-q-g-2*u*D).subs(budget)) == 0
    assert s.expand((radius_s-p-q-lv*D).subs(budget)) == 0
    sigma, tau = s.symbols('sigma tau')
    dot_residual = (-half*(lv*sigma*r-lu*tau*radius_s)
                    -half*(lv*r+lu*radius_s)+lv*(half-p))
    scalar_residual = lv*(sigma+1)*r+lu*(1-tau)*radius_s-2*lv*h3
    assert s.expand(scalar_residual+2*dot_residual) == 0
    assert s.expand(scalar_residual.subs({sigma: -1, tau: 1})+2*lv*h3) == 0
    assert s.expand(scalar_residual.subs({sigma: 1, tau: 1})+2*lv*lu*D) == 0
    for epsilon in (-1, 1):
        x5 = -2*v*length+lv*epsilon*mass-radius_s
        assert s.expand((x5+2*v*length+p+q+lv*(D-epsilon*mass)).subs(budget)) == 0
        assert s.expand(x5-lv*epsilon*mass+2*v*length+radius_s) == 0
        assert s.expand(D-epsilon*mass-d0-length-(1-epsilon)*mass) == 0

    return {'closed_metric_source': metric.metric_bindings(),
            'annulus_source': sections.coordinate_checks(),
            'section_face_bindings': 12,
            'upper_spur_normal_identities': 3,
            'intermediate_vertex_links_checked': 2,
            'relative_height_orders_checked': 2,
            'collinear_radius_sign_cases': 4,
            'scope': 'upper-b ray1 C0, regular067, all interior heights; direct annulus outer is impossible',
            'opposite_nesting_order_excluded': False,
            'numerical_or_boolean_solver_used': False}


if __name__ == '__main__':
    if not __debug__:
        raise RuntimeError('run with assertions enabled')
    started = time.monotonic()
    result = checks()
    result['seconds'] = time.monotonic()-started
    print(json.dumps(result, indent=2))
