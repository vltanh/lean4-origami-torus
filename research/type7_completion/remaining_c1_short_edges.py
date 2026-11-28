#!/usr/bin/env python3
"""Relative unit directions for shrinking cap edges of interior C1.

This package proves source identities and records the complete six-orbit
zero-edge cover.  It is a relative-scale lemma, not a boundary exclusion.
It applies to either marking and makes no comparison between h2 and t.
"""

import argparse
from itertools import combinations
import json
from pathlib import Path

import sympy as S

import exhaustive_remaining_axis as axis
import solver_remaining_c1_geometry as geometry
import solver_remaining_c1_collinear_rank as rank


HALF = S.Rational(1, 2)


def relative_metric_checks():
    t, ell, b, h0, length, ratio, a, g = S.symbols('t ell b h0 h r a g')
    p2norm, p3norm, wnorm, qnorm, dot = S.symbols('P2sq P3sq Wsq Qsq WdotQ')
    z2, v2, theta, vertical, horizontal = S.symbols('z2 v2 theta V25 X25')
    h1 = HALF - ratio * length
    x02 = 1 - h0 - h1
    x03 = x02 - length
    x12 = -h1
    x13 = 1 - h1 - length
    z3, v3 = z2 + t * length * a, v2 + t * length * g
    e01 = ell**2 - b**2 - t * h0**2
    e02 = t * p2norm + z2**2 - t * x02**2 - v2**2
    e03 = t * p3norm + z3**2 - t * x03**2 - v3**2
    e12 = t * p2norm + (z2-ell)**2 - t*x12**2 - (v2-b)**2
    e13 = t * p3norm + (z3-ell)**2 - t*x13**2 - (v3-b)**2
    k = h0-ratio
    polar = ell*a-b*g-k
    assert S.expand(e03-e02-e13+e12-2*t*length*polar) == 0

    # W=(P3-P2)/h and Q=P5-P2.  Triangle235 has zero period.
    e23 = t*length**2*wnorm + t*t*length**2*a*a \
        - t*length**2 - t*t*length**2*g*g
    e25 = t*qnorm+theta**2-t*horizontal**2-vertical**2
    e35 = t*(qnorm+length**2*wnorm-2*length*dot) \
        + (theta-t*length*a)**2 - t*(horizontal+length)**2 \
        - (vertical-t*length*g)**2
    second = dot+a*theta+horizontal-g*vertical
    assert S.expand(e23+e25-e35-2*t*length*second) == 0

    # This identity gives |W| <= C(1+t|g|), using bounded k and ell>0.
    norm = ell**2*wnorm-ell**2-t*t*h0*h0*g*g+2*t*b*k*g+t*k*k
    witness = ell**2*e23/(t*length**2)+t*g*g*e01 \
        - t*polar*(ell*a+b*g+k)
    assert S.cancel(norm-witness) == 0
    coefficient = b*theta/ell-vertical
    rhs = -horizontal-dot-k*theta/ell
    assert S.cancel(coefficient*g-rhs-second+theta*polar/ell) == 0

    alpha, beta = S.symbols('alpha beta')
    limit = {b: alpha/2, ell: alpha/2,
             theta: (beta-1)/2, vertical: (1-beta)/2}
    assert S.cancel(coefficient.subs(limit)+(1-beta)) == 0

    # Bind all horizontal expressions and vertical periods to both markings.
    weights = S.symbols('h0:8')
    horizontal_edges = geometry.horizontal_displacements(weights)
    assert S.expand(horizontal_edges[0, 2]-(1-weights[0]-weights[1])) == 0
    assert S.expand(horizontal_edges[0, 3]-(1-weights[0]-weights[1]-weights[2])) == 0
    assert S.expand(horizontal_edges[1, 2]+weights[1]) == 0
    assert S.expand(horizontal_edges[1, 3]-(1-weights[1]-weights[2])) == 0
    assert S.expand(horizontal_edges[2, 3]+weights[2]) == 0
    assert S.expand(horizontal_edges[2, 5]+weights[2]-horizontal_edges[3, 5]) == 0
    for mark in (1, 2):
        shifts, _, _ = axis.case_data(mark)
        assert all(shifts[pair][1] == 0 for pair in
                   ((0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)))
        assert shifts[2, 5][1] == shifts[3, 5][1] == 1
        assert tuple(shifts[2, 3][j]+shifts[3, 5][j]-shifts[2, 5][j]
                     for j in (0, 1)) == (0, 0)
    return {'finite_axis_polarization': True, 'finite_triangle235_polarization': True,
            'finite_relative_norm_identity': True,
            'nonzero_limiting_coefficient': '-(1-beta)', 'marked_sources': [1, 2]}


def determinant_checks():
    length, t, a, second_length, second_a = S.symbols('h t a k c')
    points = [S.Matrix(S.symbols(f'x{i} y{i} z{i}')) for i in range(8)]
    wx, wy, vx, vy = S.symbols('wx wy vx vy')
    w = S.Matrix([wx, wy, 0])
    finite_w = S.Matrix([wx, wy, t*a])
    points[3] = points[2] + length*finite_w

    def det(configuration, quad):
        return S.det(S.Matrix.hstack(*(configuration[i]-configuration[quad[0]]
                                       for i in quad[1:])))

    count = 0
    for quad in combinations(range(8), 4):
        if not {2, 3} <= set(quad):
            continue
        divided = S.cancel(det(points, quad)/length)
        assert not divided.has(length)
        virtual = list(points)
        virtual[3] = virtual[2]+w
        assert S.expand(divided.subs(t, 0)-det(virtual, quad)) == 0
        assert S.Poly(S.expand(divided-det(virtual, quad)), t).degree() <= 1
        count += 1
    assert count == 15

    # A simultaneous zero07 edge retains its own scale; no h/k ratio enters.
    points[0] = S.zeros(3, 1)
    points[7] = second_length*S.Matrix([vx, vy, t*second_a])
    divided = S.cancel(det(points, (0, 2, 3, 7))/(length*second_length))
    assert not divided.has(length, second_length)
    assert S.expand(divided.subs(t, 0)-points[2][2]*(wx*vy-wy*vx)) == 0
    return {'single_edge_normalized_brackets': count,
            'double_edge0237_normalization': True,
            'no_edge_scale_ratio': True}


def symmetry_and_orbits():
    records = rank.symbolic_checks()['marked_symmetries']
    reflection = {'A': 'B', 'B': 'A', 'C': 'C', 'D': 'D', 'E': 'F', 'F': 'E'}
    representatives = ('EA', 'EB', 'EC', 'ED', 'EE', 'EF')
    seen, cover = set(), []
    for first, second in representatives:
        orbit = {(first, second), (second, first),
                 (reflection[first], reflection[second]),
                 (reflection[second], reflection[first])}
        assert not seen & orbit
        seen |= orbit
        cover.append({'representative': first+second,
                      'orders': sorted(a+b for a, b in orbit)})
    expected = {(a, b) for a in reflection for b in reflection
                if a in ('E', 'F') or b in ('E', 'F')}
    assert seen == expected and len(seen) == 20
    for mark in (1, 2):
        relevant = [record for record in records if record['mark'] == mark]
        r = next(record['permutation'] for record in relevant if record['rotation'] == 6)
        c = next(record['permutation'] for record in relevant if record['rotation'] == 4)
        edges = {tuple(sorted((2, 3))), tuple(sorted((r[2], r[3]))),
                 tuple(sorted((c[2], c[3]))),
                 tuple(sorted((r[c[2]], r[c[3]])))}
        assert edges == {(2, 3), (3, 4), (6, 7), (0, 7)}
    return {'marked_cap_edge_cover': [(2, 3), (3, 4), (6, 7), (0, 7)],
            'zero_edge_order_orbits': cover, 'marked_symmetries': records}


def build(directory):
    directory.mkdir(parents=True, exist_ok=True)
    packet = {'domain': 'either marking; interior C1; a shrinking cap edge',
              'metric_checks': relative_metric_checks(),
              'determinant_checks': determinant_checks(),
              'symmetry_checks': symmetry_and_orbits(),
              'conclusion': '|P3-P2|/h2 -> 1 and both axial/intrinsic vertical differences are O(t*h2)',
              'relative_rate_assumptions': [], 'zero_edge_exclusion_claimed': False}
    (directory/'c1_short_edges.json').write_text(json.dumps(packet, indent=2)+'\n')
    return packet


if __name__ == '__main__':
    if not __debug__:
        raise RuntimeError('run with assertions enabled')
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('output', type=Path)
    result = build(parser.parse_args().output)
    print(json.dumps({'relative_metric_checks': result['metric_checks'],
                      'normalized_brackets': result['determinant_checks'],
                      'zero_edge_order_orbits': 6,
                      'zero_edge_exclusion_claimed': False}))
