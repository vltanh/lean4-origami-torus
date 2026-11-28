#!/usr/bin/env python3
"""Verify an exact diagnostic for a proposed global C0 relaxation.

This ray-2 C0 configuration satisfies all 29 limiting metric/product rows,
the closed horizontal and vertical nearest bounds, positive intrinsic face
areas, regular positive caps, all six common signs from exhaustive_c0_angles,
and a strict, consistent signed section-area ordering at every interior
height. Nevertheless edge 03 crosses the interior of face 617.

Thus these relaxed conditions do not imply an embedding or an exclusion of
ray 2. This is neither a Type 7 realization nor a new case exclusion. The
checker uses fixed rational input and one isolated positive square root;
it performs no numerical search. Section formulas are bound to the original
edges and faces before their signed areas are used.

Run: python research/type7_completion/verify_global_relaxation_gap.py
"""

import json

import sympy as s

import exhaustive_c0_angles as source
import solver_remaining_limit as reduction


R = s.Rational
HALF = R(1, 2)
QUARTER = R(1, 4)


def unit(parameter):
    denominator = 1 + parameter**2
    return s.Matrix([
        (1 - parameter**2) / denominator,
        2 * parameter / denominator,
    ])


def cross(first, second):
    return s.det(s.Matrix.hstack(first, second))


def equal(first, second):
    assert all(s.cancel(value) == 0 for value in first - second)


def bracket(points, quad):
    anchor, *others = quad
    return s.expand(s.det(s.Matrix.hstack(
        *(points[index] - points[anchor] for index in others)
    )))


def signed_twice_area(polygon):
    return s.expand(sum(
        cross(point, polygon[(index + 1) % len(polygon)])
        for index, point in enumerate(polygon)
    ))


def verify():
    # Rational stereographic parameters for three cap directions and the
    # direction of the middle edge. Both endpoint cap perimeters are one.
    length3, length6 = R(197, 500), R(233, 1000)
    parameters = (R(-1713, 200), R(-1249, 1000), R(223, 1000), R(227, 1000))
    direction2, direction6, direction7, middle_direction = map(unit, parameters)
    assert all(vector.dot(vector) == 1 for vector in (
        direction2, direction6, direction7, middle_direction
    ))

    point3 = s.Matrix([length3, 0])
    point6 = length6 * direction6
    h1 = s.factor((1 - 2 * length3) / (
        2 * (1 - length3 * (1 + direction2[0]))
    ))
    h2 = 1 - length3 - h1
    h7 = s.factor((1 - 2 * length6) / (
        2 * (1 - length6 * (1 + direction6.dot(direction7)))
    ))
    h6 = 1 - length6 - h7
    point2, point7 = h1 * direction2, h7 * direction7
    upper_edge, lower_edge = point3 - point2, point7 - point6

    deficit0 = s.factor(h1 * h7 + point2.dot(point7))
    h0 = HALF - deficit0
    middle_budget = deficit0 + length3 + length6 - 1
    h4 = s.factor(middle_budget / (
        1 - h2 - h6 - (upper_edge + lower_edge).dot(middle_direction)
    ))
    middle_edge = h4 * middle_direction
    h3 = s.factor(HALF - h2 * h4 - upper_edge.dot(middle_edge))
    h5 = s.factor(HALF - h6 * h4 - lower_edge.dot(middle_edge))
    horizontal_lengths = (h0, h1, h2, h3, h4, h5, h6, h7)
    assert sum(horizontal_lengths) == R(5, 2)
    assert all(0 < value < HALF for value in horizontal_lengths)
    assert all(horizontal_lengths[index] + horizontal_lengths[(index + 1) % 8]
               > HALF for index in range(8))

    radius4 = h3 - middle_budget / 2
    radius5 = h5 - middle_budget / 2
    along = s.factor((radius4**2 - radius5**2 - h4**2) / (2 * h4))
    radicand = s.factor(radius5**2 - along**2)
    assert radius4 > 0 and radius5 > 0 and radicand > 0
    perpendicular = s.Matrix([-middle_direction[1], middle_direction[0]])
    root = s.sqrt(radicand)
    root_variable = s.Symbol('positive_root')
    formal_q5 = along * middle_direction + root_variable * perpendicular
    formal_q4 = formal_q5 + middle_edge
    center = (point3 + point6) / 2
    formal_points = [
        s.zeros(2, 1), s.zeros(2, 1), point2, point3,
        center + formal_q4, center + formal_q5, point6, point7,
    ]
    points = [point.subs(root_variable, root) for point in formal_points]
    levels = (0, HALF, HALF, HALF, QUARTER, QUARTER, 0, 0)
    formal_spatial = [point.col_join(s.Matrix([level]))
                      for point, level in zip(formal_points, levels)]
    spatial = [point.subs(root_variable, root) for point in formal_spatial]

    upper_cap_area = cross(point2, point3)
    lower_cap_area = cross(point6, point7)
    assert upper_cap_area.is_Rational and upper_cap_area > 0
    assert lower_cap_area.is_Rational and lower_cap_area > 0

    # Bind the construction to the actual ray-2 cocycle, oriented faces,
    # and full auxiliary source system, not only the five circle identities.
    shifts, faces, edges = reduction.axis.case_data(2)
    face_sets = {frozenset(face) for face in faces}
    edge_sets = {frozenset(edge) for edge in edges}
    assert len(faces) == 16 and len(edges) == 24
    intrinsic_x = [s.Integer(0)]
    for index in range(7):
        first_shift, second_shift = shifts[index, index + 1]
        intrinsic_x.append(s.factor(
            intrinsic_x[-1] - horizontal_lengths[index]
            - first_shift - HALF * second_shift
        ))
    component_values = (HALF, HALF, HALF, R(3, 4), -QUARTER, 0)
    intrinsic_y = reduction.locus.vertex_values(component_values)
    horizontal = {
        (first, second): s.factor(
            intrinsic_x[second] - intrinsic_x[first]
            + shifts[first, second][0] + HALF * shifts[first, second][1]
        )
        for first, second in edges
    }
    vertical = {
        (first, second): intrinsic_y[second] - intrinsic_y[first]
        + shifts[first, second][1]
        for first, second in edges
    }
    assert all(abs(value) < HALF for value in horizontal.values())
    assert all(abs(value) <= HALF for value in vertical.values())

    def intrinsic_edge(first, second):
        if first < second:
            return horizontal[first, second], vertical[first, second]
        return -horizontal[second, first], -vertical[second, first]

    for index in range(8):
        assert intrinsic_edge(index, (index + 1) % 8)[0] == -horizontal_lengths[index]
    for first, second, third in faces:
        x1, y1 = intrinsic_edge(first, second)
        x2, y2 = intrinsic_edge(first, third)
        assert x1 * y2 - x2 * y1 > 0

    residuals = s.Matrix([
        s.expand((points[second] - points[first]).dot(points[second] - points[first])
                 - horizontal[first, second]**2)
        for first, second in edges
    ])
    projected_rows = reduction.closed_c0_rows()[:, :24].subs({
        reduction.A: R(3, 4), reduction.B: -QUARTER,
    })
    assert projected_rows.rows == 12
    assert all(s.simplify(value) == 0 for value in projected_rows * residuals)
    auxiliary_matrix = reduction.original_system(component_values)
    auxiliary_rhs = -residuals.col_join(s.zeros(5, 1))
    assert auxiliary_matrix.shape == (29, 14)
    auxiliaries, free_parameters = auxiliary_matrix.gauss_jordan_solve(auxiliary_rhs)
    assert free_parameters.rows == 0
    assert all(s.simplify(value) == 0 for value in
               auxiliary_matrix * auxiliaries - auxiliary_rhs)

    # Every subsequent sign is certified by rational endpoint evaluations.
    root_lower = R(int(s.floor(root * 10**12)), 10**12)
    root_upper = root_lower + R(1, 10**12)
    assert 0 < root_lower < root_upper
    assert root_lower**2 < radicand < root_upper**2

    def prove_positive_linear(expression):
        polynomial = s.Poly(s.expand(expression), root_variable)
        assert polynomial.degree() <= 1
        assert all(coefficient.is_Rational for coefficient in polynomial.all_coeffs())
        for endpoint in (root_lower, root_upper):
            value = s.factor(expression.subs(root_variable, endpoint))
            assert value.is_Rational and value > 0

    assert len(source.EXTRA_SIGNS) == 6
    for quad, sign in source.EXTRA_SIGNS:
        formal_minor = bracket(formal_spatial, quad)
        assert s.expand(formal_minor.subs(root_variable, root)
                        - bracket(spatial, quad)) == 0
        prove_positive_linear(sign * formal_minor)

    height = s.Symbol('height')
    p = formal_points
    direct = [
        s.zeros(2, 1), 2 * height * p[3], 2 * height * p[2],
        2 * height * p[2] + (1 - 2 * height) * p[7],
        (1 - 2 * height) * p[7], (1 - 2 * height) * p[6],
    ]
    lower = [
        (1 - 2 * height) * p[6] + 2 * height * p[3],
        (1 - 4 * height) * p[6] + 4 * height * p[4],
        (1 - 4 * height) * p[7] + 4 * height * p[4],
        (1 - 4 * height) * p[7] + 4 * height * p[5],
        4 * height * p[5],
        (1 - 4 * height) * p[6] + 4 * height * p[5],
    ]
    upper = [
        2 * (1 - 2 * height) * p[4] + (4 * height - 1) * p[3],
        2 * (1 - 2 * height) * p[4],
        2 * (1 - 2 * height) * p[4] + (4 * height - 1) * p[2],
        2 * (1 - 2 * height) * p[5] + (4 * height - 1) * p[2],
        2 * (1 - 2 * height) * p[5] + (4 * height - 1) * p[3],
        (1 - 2 * height) * p[6] + 2 * height * p[3],
    ]

    def bind_section(polygon, section_edges, interval):
        assert len(polygon) == len(section_edges)
        bound_faces = set()
        for index, ((first, second), point) in enumerate(zip(section_edges, polygon)):
            assert frozenset((first, second)) in edge_sets
            assert min(levels[first], levels[second]) <= interval[0]
            assert interval[1] <= max(levels[first], levels[second])
            assert levels[first] != levels[second]
            fraction = (height - levels[first]) / (levels[second] - levels[first])
            equal(point, (1 - fraction) * p[first] + fraction * p[second])
            assert s.cancel((1 - fraction) * levels[first]
                            + fraction * levels[second] - height) == 0
            face = frozenset(section_edges[index]) | frozenset(
                section_edges[(index + 1) % len(section_edges)]
            )
            assert len(face) == 3 and face in face_sets
            bound_faces.add(face)
        return bound_faces

    direct_faces = bind_section(direct, (
        (0, 1), (0, 3), (0, 2), (2, 7), (1, 7), (1, 6),
    ), (0, HALF))
    lower_faces = bind_section(lower, (
        (3, 6), (4, 6), (4, 7), (5, 7), (0, 5), (5, 6),
    ), (0, QUARTER))
    upper_faces = bind_section(upper, (
        (3, 4), (1, 4), (2, 4), (2, 5), (3, 5), (3, 6),
    ), (QUARTER, HALF))
    assert len(direct_faces) == 6 and len(lower_faces | upper_faces) == 10
    assert not direct_faces & (lower_faces | upper_faces)
    assert direct_faces | lower_faces | upper_faces == face_sets
    assert signed_twice_area(lower).subs(height, 0) == lower_cap_area
    assert signed_twice_area(direct).subs(height, 0) == -lower_cap_area
    assert signed_twice_area(upper).subs(height, HALF) == upper_cap_area
    assert signed_twice_area(direct).subs(height, HALF) == -upper_cap_area

    # These are oriented polygonal walks; their positive area difference
    # does not assert containment or simplicity. Each quotient is affine in
    # height and in the isolated root, so four rational corner checks cover
    # its entire closed rectangle. The removed height factor is positive.
    gaps = []
    for polygon, vanishing, endpoints in (
        (lower, height, (0, QUARTER)),
        (upper, HALF - height, (QUARTER, HALF)),
    ):
        gap = s.expand(signed_twice_area(polygon) + signed_twice_area(direct))
        quotient = s.cancel(gap / vanishing)
        assert s.Poly(quotient, height).degree() <= 1
        for endpoint in endpoints:
            prove_positive_linear(quotient.subs(height, endpoint))
        gaps.append(gap)
    assert s.expand((gaps[0] - gaps[1]).subs(height, QUARTER)) == 0

    # Explicitly reject an embedding interpretation. The crossing below
    # involves only rational cap coordinates, so even its weights are rational.
    first, second, a, b, c = 0, 3, 6, 1, 7
    assert frozenset((first, second)) in edge_sets
    assert frozenset((a, b, c)) in face_sets
    assert not {first, second} & {a, b, c}
    matrix = s.Matrix.hstack(
        spatial[second] - spatial[first],
        -(spatial[b] - spatial[a]),
        -(spatial[c] - spatial[a]),
    )
    parameter, beta, gamma = matrix.inv() * (spatial[a] - spatial[first])
    alpha = 1 - beta - gamma
    assert all(value.is_Rational for value in (parameter, alpha, beta, gamma))
    assert 0 < parameter < 1 and alpha > 0 and beta > 0 and gamma > 0
    equal((1 - parameter) * spatial[first] + parameter * spatial[second],
          alpha * spatial[a] + beta * spatial[b] + gamma * spatial[c])

    return {
        'status': 'verified diagnostic; not an embedding or an exclusion',
        'marking': 2,
        'component': 'C0',
        'u': '1/4',
        'v': '1/4',
        'metric_and_product_rows': 29,
        'projected_metric_rows': 12,
        'closed_nearest_bounds': True,
        'positive_intrinsic_faces': 16,
        'positive_regular_caps': 2,
        'strict_common_signs': 6,
        'section_vertex_bindings': 18,
        'original_faces_bound': 16,
        'strict_signed_area_ordering': 'every 0 < height < 1/2',
        'crossing': {
            'edge': [0, 3],
            'face': [6, 1, 7],
            'edge_parameter': str(parameter),
            'face_barycentric_weights': list(map(str, (alpha, beta, gamma))),
        },
        'ray2_exclusion_claimed': False,
    }


if __name__ == '__main__':
    if not __debug__:
        raise RuntimeError('run with assertions enabled')
    print(json.dumps(verify(), sort_keys=True))
