#!/usr/bin/env python3
"""Exact product-locus cover for the bounded ray-1/2 axis chart.

Usage: python exhaustive_remaining_locus.py [OUTPUT_JSON]

Checks all factor choices, six closed nearest-lift polygons, the five
universal q syzygies, exact saturation, and the marked dihedral reduction
to two limit families.  This is a necessary asymptotic cover, not a
finite-height exclusion or a real-feasibility certificate.
"""

import argparse
from itertools import combinations, product
import json
from pathlib import Path

import sympy as s

import exhaustive_remaining_axis as axis

A, B = s.symbols('A B')
HALF = s.Rational(1, 2)
EIGHTH = s.Rational(1, 8)
VARIABLES = s.symbols('v1 v2 v3 v4 v5 v7')


def components():
    """Coordinates are (v1,v2,v3,v4,v5,v7); facets are nonnegative."""
    return [
        {'id': 0, 'values': (HALF, HALF, HALF, A, B, 0),
         'facets': (A-HALF, 1-A, B+HALF, -B),
         'caps': ((0, 6, 7), (1, 2, 3)), 'middle': (4, 5)},
        {'id': 1, 'values': (A, HALF, HALF, HALF, B, 0),
         'facets': (A-EIGHTH, HALF-A, B+HALF, -B),
         'caps': ((0, 6, 7), (2, 3, 4)), 'middle': (1, 5)},
        {'id': 2, 'values': (A, B, HALF, HALF, -HALF, 0),
         'facets': (A-EIGHTH, HALF-A, B, HALF-B),
         'caps': ((0, 6, 7), (3, 4, 5)), 'middle': (1, 2)},
        {'id': 3, 'values': (A+HALF, A+HALF, A+HALF, A+1, A, B),
         'facets': (A+s.Rational(3, 8), -A, B-A, A-B+HALF),
         'caps': ((4, 5, 6), (1, 2, 3)), 'middle': (0, 7)},
        {'id': 4, 'values': (B+HALF, B+HALF, B+HALF, A, B, B),
         'facets': (B+s.Rational(3, 8), -B, A-B-HALF, B+1-A),
         'caps': ((5, 6, 7), (1, 2, 3)), 'middle': (0, 4)},
        {'id': 5, 'values': (A, B+HALF, B+HALF, B+HALF, B, B),
         'facets': (A-EIGHTH, -B, B+HALF-A),
         'caps': ((5, 6, 7), (2, 3, 4)), 'middle': (0, 1)},
    ]


def vertex_values(values):
    v1, v2, v3, v4, v5, v7 = map(s.sympify, values)
    return [s.Integer(0), v1, v2, v3, v4, v5, v3-HALF, v7]


def factor_coordinates(v):
    """Independent affine coordinates, in the order f,a,c,d,b,e."""
    return (2*v[3]-1, v[1]-v[3], v[2]-v[3], v[3]-v[4],
            2*v[3]-2*v[5]-1, 2*v[3]-2*v[7]-1)


def q_syzygies(v, q):
    """Five exact identities, valid for every t>0 and at every limit."""
    f, a, c, d, b, e = factor_coordinates(v)
    q0, q1, q2, q3, q4, q5 = (q[edge] for edge in axis.PRODUCT_EDGES)
    return [
        a*q2-c*q1,
        (1-b)*q2+2*d*q3,
        f*q5-e*q0,
        2*c*(q4-q5)+e*(q2-q3),
        (2*d+1)*q5-b*q4,
    ]


def _linear_ideal(expressions, variables):
    matrix, rhs = s.linear_eq_to_matrix(expressions, variables)
    reduced, pivots = matrix.row_join(rhs).rref()
    if len(variables) in pivots:
        return None
    return tuple(tuple(row) for row in reduced.tolist() if any(row))


def _contained(left, right):
    matrix = s.Matrix(left)
    return matrix.col_join(s.Matrix(right)).rank() == matrix.rank()


def polygon_vertices(facets):
    facets = tuple(map(s.sympify, facets))
    assert all(value >= 0 for value in facets if not value.free_symbols)
    lines = [value for value in facets if value.free_symbols]
    points = set()
    for first, second in combinations(lines, 2):
        matrix, rhs = s.linear_eq_to_matrix((first, second), (A, B))
        if matrix.det() == 0:
            continue
        point = tuple(matrix.inv()*rhs)
        substitution = dict(zip((A, B), point))
        if all(value.subs(substitution) >= 0 for value in facets):
            points.add(point)
    return sorted(points)


def _step_values(v, shifts):
    return [s.expand(v[(i+1) % 8]-v[i]+shifts[i, (i+1) % 8][1]) for i in range(8)]


def marked_dihedral_gauges(mark):
    """Rotations use K; reflections use -K and intrinsic inversion."""
    shifts, faces, edges = axis.case_data(mark)
    oriented = {face[i:]+face[:i] for face in faces for i in range(3)}
    records = []
    for sign in (1, -1):
        for rotation in range(8):
            permutation = tuple((rotation+sign*i) % 8 for i in range(8))
            image_faces = [tuple(permutation[i] for i in face) for face in faces]
            # Reversing the cyclic vertex labels acts as intrinsic -I,
            # which preserves the orientation of this triangulated torus.
            assert all(face in oriented for face in image_faces)
            gauge = {0: (0, 0)}
            for _ in range(8):
                for i, j in edges+[(j, i) for i, j in edges]:
                    if i in gauge and j not in gauge:
                        gauge[j] = tuple(gauge[i][k]+sign*shifts[permutation[i], permutation[j]][k]
                                         -shifts[i, j][k] for k in (0, 1))
            assert len(gauge) == 8
            for i, j in edges:
                assert tuple(sign*shifts[permutation[i], permutation[j]][k]-shifts[i, j][k]
                             for k in (0, 1)) == tuple(gauge[j][k]-gauge[i][k] for k in (0, 1))
            records.append({'sign': sign, 'rotation': rotation,
                            'gauge': [gauge[i] for i in range(8)]})
    return records


def verify_saturation():
    f, a, c, d, b, e = variables = s.symbols('f a c d b e')
    q0, q1, q2, q3, q4, q5 = q = s.symbols('q05 q14 q24 q25 q47 q57')
    t, u = s.symbols('t u')
    polynomials = [f*b, -4*a*d, -4*c*d, -2*c*(b-1), (2*d+1)*e, b*e]
    syzygies = [a*q2-c*q1, (1-b)*q2+2*d*q3, f*q5-e*q0,
                2*c*(q4-q5)+e*(q2-q3), (2*d+1)*q5-b*q4]
    for expression in syzygies:
        assert s.expand(expression.subs(dict(zip(q, polynomials)), simultaneous=True)) == 0
    graph = [t*value-polynomial for value, polynomial in zip(q, polynomials)]
    saturated = s.groebner(graph+[u*t-1], u, t, *variables, *q, order='lex')
    eliminated = [row.as_expr() for row in saturated.polys if not row.as_expr().has(u)]
    direct = s.groebner(graph+syzygies, t, *variables, *q, order='lex')
    assert len(eliminated) == len(direct.polys) == 19
    assert all(s.expand(left-right.as_expr()) == 0 for left, right in zip(eliminated, direct.polys))
    fiber = s.groebner(polynomials+syzygies, *variables, *q, order='lex')
    assert all(fiber.reduce(expression.subs(t, 0))[1] == 0 for expression in eliminated)
    return {'syzygies': [str(value) for value in syzygies],
            'saturated_basis_size': 19, 'fiber_basis_size': len(fiber.polys)}


def verify():
    shifts, _, edges = axis.case_data(1)
    assert all(axis.case_data(2)[0][edge][1] == shifts[edge][1] for edge in edges)
    v = vertex_values(VARIABLES)
    f, a, c, d, b, e = factor_coordinates(v)
    pairs = ((f, b), (a, d), (c, d), (c, b-1), (2*d+1, e), (b, e))
    varieties = {}
    for choice in product((0, 1), repeat=6):
        ideal = _linear_ideal([pair[index] for pair, index in zip(pairs, choice)], VARIABLES)
        if ideal is not None:
            varieties.setdefault(ideal, []).append(choice)
    maximal = [ideal for ideal in varieties if not any(
        ideal != other and _contained(ideal, other) for other in varieties)]
    assert sum(map(len, varieties.values())) == 25 and len(varieties) == 18 and len(maximal) == 6
    expected = []
    records = []
    for component in components():
        values = tuple(map(s.sympify, component['values']))
        # Eliminate A,B from the parameterization to recover its plane.
        equations = [old-new for old, new in zip(VARIABLES, values)]
        full = s.groebner(equations, A, B, *VARIABLES, order='lex')
        equations = [row.as_expr() for row in full.polys if not row.as_expr().has(A, B)]
        ideal = _linear_ideal(equations, VARIABLES)
        expected.append(ideal)
        vv = vertex_values(values)
        actual_facets = [vv[1]-EIGHTH]
        for i, j in edges:
            vertical = vv[j]-vv[i]+shifts[i, j][1]
            actual_facets.extend((HALF-vertical, HALF+vertical))
        actual_vertices = polygon_vertices(actual_facets)
        expected_vertices = polygon_vertices(component['facets'])
        assert actual_vertices == expected_vertices and len(actual_vertices) in (3, 4)
        # The actual polytope is bounded: |v1,v2,v3,v5,v7|<=1/2
        # from edges0i, and |v4|<=1 from edge34.  Identical complete
        # vertex sets therefore prove equality with the stated polygon.
        assert set().union(*(value.free_symbols for value in values)) == {A, B}
        spatial = axis.baselines(vv)[1]
        lower, upper = component['caps']
        assert all(s.expand(spatial[i]-spatial[lower[0]]) == 0 for i in lower)
        assert all(s.expand(spatial[i]-spatial[upper[0]]) == 0 for i in upper)
        assert s.expand(spatial[upper[0]]-spatial[lower[0]]-HALF) == 0
        for point in actual_vertices:
            substitution = dict(zip((A, B), point))
            for i in component['middle']:
                assert (spatial[i]-spatial[lower[0]]).subs(substitution) >= 0
                assert (spatial[upper[0]]-spatial[i]).subs(substitution) >= 0
        cap_products = []
        for cap in component['caps']:
            assert set(combinations(cap, 2)) <= set(edges)
            for i, j in combinations(cap, 2):
                assert s.expand(vv[j]-vv[i]+shifts[i, j][1]) == 0
                if (i, j) in axis.PRODUCT_EDGES:
                    cap_products.append(''.join(map(str, (i, j))))
        assert cap_products == {0: [], 1: ['24'], 2: [], 3: [], 4: ['57'], 5: ['57', '24']}[component['id']]
        records.append({'id': component['id'], 'values': list(map(str, values)),
                        'facets': list(map(str, component['facets'])),
                        'vertices': [[str(value) for value in point] for point in actual_vertices],
                        'steps': list(map(str, _step_values(vv, shifts))),
                        'spatial_levels': list(map(str, spatial)),
                        'caps': component['caps'], 'middle': component['middle'],
                        'cap_products': cap_products})
    assert set(maximal) == set(expected)
    for ideal in varieties:
        assert any(_contained(ideal, other) for other in maximal)

    # The only possible cap-q exceptions are two corners already in C0.
    q = {edge: s.Symbol('q'+''.join(map(str, edge))) for edge in axis.PRODUCT_EDGES}
    for index in (1, 4, 5):
        vv = vertex_values(components()[index]['values'])
        relations = list(map(s.expand, q_syzygies(vv, q)))
        if index == 1:
            assert s.expand(relations[0]-(A-HALF)*q[2, 4]) == 0
            assert s.expand(relations[1]-(1+2*B)*q[2, 4]) == 0
            corner = {A: HALF, B: -HALF}
            target = vertex_values(components()[0]['values'])
            assert [value.subs(corner) for value in vv] == [
                value.subs({A: HALF, B: -HALF}) for value in target]
        elif index == 4:
            assert s.expand(relations[2]-2*B*q[5, 7]) == 0
            assert s.expand(relations[4]-2*(B+1-A)*q[5, 7]) == 0
            target = vertex_values(components()[0]['values'])
            assert [value.subs({A: 1, B: 0}) for value in vv] == [
                value.subs({A: 1, B: 0}) for value in target]
        else:
            assert relations[1] == q[2, 4] and relations[4] == q[5, 7]

    # A single large step can always be rotated to index0.  The other
    # nonzero component then lies in indices3,4,5: canonical family C0.
    for index, rotation in ((0, 0), (2, 5), (3, 3), (5, 4)):
        component = components()[index]
        steps = _step_values(vertex_values(component['values']), shifts)
        transformed = [steps[(i+rotation) % 8] for i in range(8)]
        assert transformed[0] == HALF
        assert all(transformed[i] == 0 for i in (1, 2, 6, 7))
        assert s.expand(sum(transformed[3:6])-HALF) == 0
        for point in polygon_vertices(component['facets']):
            substitution = dict(zip((A, B), point))
            assert 0 <= transformed[3].subs(substitution) <= HALF
            assert 0 <= transformed[5].subs(substitution) <= HALF

    # For a 2+2 support choose the larger member of one pair as its first
    # edge, by a checked reflection if necessary.  It is at least1/4.
    choices = ((1, 1, 0, A-s.Rational(1, 4)),
               (1, -1, 2, s.Rational(1, 4)-A),
               (4, 1, 7, -B-s.Rational(1, 4)),
               (4, -1, 1, B+s.Rational(1, 4)))
    for index, sign, rotation, extra in choices:
        component = components()[index]
        steps = _step_values(vertex_values(component['values']), shifts)
        transformed = [steps[(i+rotation) % 8] if sign == 1
                       else steps[(rotation-i-1) % 8] for i in range(8)]
        assert all(transformed[i] == 0 for i in (2, 3, 6, 7))
        assert s.expand(transformed[0]+transformed[1]-HALF) == 0
        assert s.expand(transformed[4]+transformed[5]-HALF) == 0
        for point in polygon_vertices(component['facets']+(extra,)):
            substitution = dict(zip((A, B), point))
            assert s.Rational(1, 4) <= transformed[0].subs(substitution) <= HALF
            assert 0 <= transformed[5].subs(substitution) <= HALF

    return {'factor_choices': 64, 'consistent_choices': 25, 'distinct_planes': 18,
            'maximal_components': records, 'canonical_limit_families': [0, 1],
            'dihedral_gauges': {str(mark): marked_dihedral_gauges(mark) for mark in (1, 2)},
            'product_saturation': verify_saturation(),
            'finite_height_exclusion': False}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('output', type=Path, nargs='?')
    args = parser.parse_args()
    record = verify()
    if args.output is not None:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps(record, indent=2)+'\n')
    print(json.dumps({'factor_choices': record['factor_choices'],
                      'consistent_choices': record['consistent_choices'],
                      'distinct_planes': record['distinct_planes'],
                      'maximal_components': len(record['maximal_components']),
                      'canonical_limit_families': record['canonical_limit_families'],
                      'marked_dihedral_checks': 32,
                      'product_saturation': record['product_saturation'],
                      'finite_height_exclusion': False}), flush=True)


if __name__ == '__main__':
    if not __debug__:
        raise RuntimeError('run with assertions enabled')
    main()
