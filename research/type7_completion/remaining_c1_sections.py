#!/usr/bin/env python3
"""Exact algebra and topology obligations for the regular C1 section proof.

Usage: python remaining_c1_sections.py OUTPUT_DIRECTORY

The geometric proof uses sections of the original embedded sequence, not
only an arbitrary weak realization of its limiting determinant signs.
All emitted CNFs require independent RUP replay.
"""

import argparse
from collections import Counter
from itertools import combinations
from itertools import product
import json
from pathlib import Path
import time

import sympy as S

import exhaustive_c1_angles as angles
import solver_remaining_chambers as shared
from solver_chambers import write_cnf


def cross(first, second):
    return S.det(S.Matrix.hstack(first, second))


def equal_vectors(first, second):
    assert all(S.cancel(value) == 0 for value in first - second)


def metric_checks():
    h0, h1, h, k, a = S.symbols('h0 h1 h k a')
    q = 1 - a
    rho = a * (1 - h1 - h) + q * h0
    sigma = q * (1 - h0) + a * h1
    tau = sigma - q * k
    p = S.Rational(1, 2) - h0
    n2 = sigma ** 2 - 2 * q * p
    assert S.expand(n2 + q ** 2 * k ** 2 + 2 * q * (p - k * sigma) - tau ** 2) == 0
    assert S.expand(rho + a * h + q * k + tau - 1) == 0
    assert S.expand(rho - a * (S.Rational(1, 2) - h)
                    - a * (S.Rational(1, 2) - h1) - q * h0) == 0
    assert S.expand(tau - q * (S.Rational(1, 2) - k)
                    - q * (S.Rational(1, 2) - h0) - a * h1) == 0

    # Twice rho*tau*|Y| times the sum of the two cosines at the
    # distinguished critical vertex.
    numerator = S.expand(tau * (rho ** 2 + n2 - (a * h) ** 2)
                         + rho * (n2 + tau ** 2 - (q * k) ** 2))
    r, u = S.Rational(1, 2) - h, S.Rational(1, 2) - k
    low0 = q * u * (q + 2 * a * r)
    low1 = a * r * (a + 2 * q * u)
    decomposition = (2 * h0 * low0 + 2 * h1 * low1
                     + 2 * (h0 + h1 - S.Rational(1, 2)) * a * q * (h + k - 2 * h * k))
    assert S.expand(numerator - decomposition) == 0
    # Here h,k are regular cap edges, so 0<h,k<1/2. Both low0 and
    # low1 are strictly positive, while h0+h1>=1/2.

    pp, qq, t = S.symbols('p q t')
    sig = S.Rational(1, 2) + (1 - t) * pp - t * qq
    nn = sig ** 2 - 2 * (1 - t) * pp
    lower = ((t * pp + (1 - t) * qq) * (1 - 2 * pp - 2 * qq)
             + (t * pp - (1 - t) * qq) ** 2)
    assert S.expand(nn - (S.Rational(1, 2) - pp - qq) ** 2 - lower) == 0
    return {'critical_perimeter_identities': 2,
            'strict_corner_positive_decomposition': True,
            'zero_norm_identity': True}


def section_checks():
    a, b, t = S.symbols('alpha beta t')
    p = [S.zeros(2, 1), S.zeros(2, 1)]
    p.extend(S.Matrix(S.symbols(f'x{i} y{i}')) for i in range(2, 8))
    e2, e3, f = p[2] - p[3], p[4] - p[3], p[7] - p[6]
    r1, y0 = -a * p[3], a * p[2]
    r5 = p[5] - b * p[3] - (1 - b) * p[6]
    y5 = b * e3 - r5
    z0, z5 = y0 + (1 - a) * p[7], y5 + (1 - b) * f
    low_b = [t * p[3], t * p[2], (1 - t) * p[7] + t * p[2],
             (1 - t / a) * p[7], (1 - t / a) * p[6], S.zeros(2, 1)]
    high_b = low_b[:3] + [(t - a) / (1 - a) * p[i] for i in (2, 4, 3)]
    low_a = [(1 - t) * p[6] + t * p[3],
             (1 - t / b) * p[6] + t / b * p[5], t / b * p[5],
             (1 - t / b) * p[7] + t / b * p[5],
             (1 - t) * p[7] + t * p[4], (1 - t) * p[6] + t * p[4]]
    high_a = [low_a[0]] + [(1 - t) / (1 - b) * p[5] + (t - b) / (1 - b) * p[i]
                           for i in (3, 2, 4)] + low_a[4:]
    # Bind the four section orders to the original sixteen faces, not
    # only to the displayed coordinate formulas.
    edge_cycles = (
        ((0, 3), (0, 2), (2, 7), (1, 7), (1, 6), (0, 1)),
        ((0, 3), (0, 2), (2, 7), (1, 2), (1, 4), (1, 3)),
        ((3, 6), (5, 6), (0, 5), (5, 7), (4, 7), (4, 6)),
        ((3, 6), (3, 5), (2, 5), (4, 5), (4, 7), (4, 6)),
    )
    _, _, original_faces, *_ = shared.base_formula()
    face_set = {tuple(sorted(face)) for face in original_faces}
    heights = (0, a, 1, 1, 1, b, 0, 0)
    annuli = [set(), set()]
    for index, (cycle, polygon) in enumerate(zip(edge_cycles, (low_b, high_b, low_a, high_a))):
        for position, ((i, j), vertex) in enumerate(zip(cycle, polygon)):
            equal_vectors(vertex, p[i] + (t-heights[i])/(heights[j]-heights[i])*(p[j]-p[i]))
            face = tuple(sorted(set(cycle[position]) | set(cycle[(position+1) % 6])))
            assert len(face) == 3 and face in face_set
            annuli[index//2].add(face)
    assert len(annuli[0]) == len(annuli[1]) == 8
    assert not annuli[0] & annuli[1] and annuli[0] | annuli[1] == face_set
    expected_boundary = set(combinations((0, 6, 7), 2)) | set(combinations((2, 3, 4), 2))
    for annulus in annuli:
        edges = Counter(edge for face in annulus for edge in combinations(face, 2))
        assert {edge for edge, count in edges.items() if count == 1} == expected_boundary
        assert all(count in (1, 2) for count in edges.values())
        vertices = set().union(*map(set, annulus))
        assert len(vertices)-len(edges)+len(annulus) == 0
    for vertex, link in ((1, (0, 3, 4, 2, 7, 6)), (5, (0, 6, 3, 2, 4, 7))):
        assert {tuple(sorted((vertex, link[i], link[(i+1) % 6]))) for i in range(6)} == {
            face for face in face_set if vertex in face}
        upper = [neighbor in (2, 3, 4) for neighbor in link]
        assert sum(upper[i] != upper[(i+1) % 6] for i in range(6)) == 2
    expected = [
        [t * e2, (1 - t) * p[7], -t / a * z0,
         -(1 - t / a) * f, -(1 - t / a) * p[6], -t / a * r1],
        [t * e2, (1 - t) * p[7], -(1 - t) / (1 - a) * z0,
         (t - a) / (1 - a) * (p[4] - p[2]), -(t - a) / (1 - a) * e3,
         -(1 - t) / (1 - a) * r1],
        [t / b * r5, -(1 - t / b) * p[6], (1 - t / b) * p[7],
         t / b * z5, -(1 - t) * f, -t * e3],
        [(1 - t) / (1 - b) * r5, (t - b) / (1 - b) * e2,
         (t - b) / (1 - b) * (p[4] - p[2]), (1 - t) / (1 - b) * z5,
         -(1 - t) * f, -t * e3],
    ]
    for polygon, vectors in zip((low_b, high_b, low_a, high_a), expected):
        for i, vector in enumerate(vectors):
            equal_vectors(polygon[(i + 1) % 6] - polygon[i], vector)
    for lo, hi, critical in ((low_b, high_b, a), (low_a, high_a, b)):
        for first, second in zip(lo, hi):
            equal_vectors(first.subs(t, critical), second.subs(t, critical))

    h = S.symbols('h0:8')
    rho1 = a * (1 - h[1] - h[2]) + (1 - a) * h[0]
    sigma0 = (1 - a) * (1 - h[0]) + a * h[1]
    tau0 = sigma0 - (1 - a) * h[7]
    rho5 = b * (1 - h[3] - h[4]) + (1 - b) * h[5]
    sigma5 = (1 - b) * (1 - h[5]) + b * h[4]
    tau5 = sigma5 - (1 - b) * h[6]
    perimeters = [
        t * h[2] + (1 - t) * h[7] + t / a * tau0
        + (1 - t / a) * (1 - h[7]) + t / a * rho1,
        t * h[2] + (1 - t) * h[7] + (1 - t) / (1 - a) * (tau0 + rho1)
        + (t - a) / (1 - a) * (1 - h[2]),
        t / b * (rho5 + tau5) + (1 - t / b) * (1 - h[6])
        + (1 - t) * h[6] + t * h[3],
        (1 - t) / (1 - b) * (rho5 + tau5) + (t - b) / (1 - b) * (1 - h[3])
        + (1 - t) * h[6] + t * h[3],
    ]
    assert all(S.cancel(value - 1) == 0 for value in perimeters)

    # Identities used when a true corner tracks one outer vertex.
    x, y, z = low_a[0], low_a[5], low_a[4]
    u, v, w = low_b[:3]
    matches = [
        (w - low_a[4], t * (p[2] - p[4])),
        (w - low_a[3], t / b * (b * p[2] + (1 - b) * p[7] - p[5])),
        (u - low_a[2], t / b * (b * p[3] - p[5])),
        (v - low_a[2], t / b * (b * p[2] - p[5])),
        (u - high_a[0], -(1 - t) * p[6]),
        (u - high_a[1], (1 - t) / (1 - b) * (b * p[3] - p[5])),
        (v - high_a[2], (1 - t) / (1 - b) * (b * p[2] - p[5])),
        (w - high_a[2], (1 - t) / (1 - b) * (b * p[2] + (1 - b) * p[7] - p[5])),
        (z - low_b[2], t * (p[4] - p[2])),
        (z - low_b[3], t / a * (a * p[4] + (1 - a) * p[7])),
        (x - low_b[4], t / a * (a * p[3] + (1 - a) * p[6])),
        (y - low_b[4], t / a * (a * p[4] + (1 - a) * p[6])),
        (x - high_b[0], (1 - t) * p[6]),
        (x - high_b[5], (1 - t) / (1 - a) * (a * p[3] + (1 - a) * p[6])),
        (y - high_b[4], (1 - t) / (1 - a) * (a * p[4] + (1 - a) * p[6])),
        (z - high_b[4], (1 - t) / (1 - a) * (a * p[4] + (1 - a) * p[7])),
    ]
    for first, second in matches:
        equal_vectors(first, second)
    return {'section_source_faces': len(face_set), 'section_intersection_bindings': 24,
            'annulus_boundary_and_link_checks': True,
            'section_edge_identities': 24, 'perimeter_identities': 4,
            'vertex_tracking_identities': len(matches)}


def finite_turn_checks():
    z1, z2, z3, z4, z5 = S.symbols('z1 z2 z3 z4 z5')
    p = [S.zeros(2, 1), S.zeros(2, 1)]
    p.extend(S.Matrix(S.symbols(f'x{i} y{i}')) for i in range(2, 8))
    heights = (0, z1, z2, z3, z4, z5, 0, 0)
    points = [v.col_join(S.Matrix([z])) for v, z in zip(p, heights)]

    def bracket(indices):
        first, *rest = indices
        return S.det(S.Matrix.hstack(*(points[i] - points[first] for i in rest)))

    b1, b2 = z1 / z3 * p[3], z1 / z2 * p[2]
    b3 = b2 + (1 - z1 / z2) * p[7]
    b_turns = (cross(b1, b2), cross(b2 - b1, b3 - b2), cross(b3 - b2, -b3))
    b_expected = (-z1 / (z2 * z3) * bracket((0, 1, 2, 3)),
                  -(1 - z1 / z2) * z1 / (z2 * z3) * bracket((0, 2, 3, 7)),
                  (1 - z1 / z2) / z2 * bracket((0, 1, 2, 7)))
    a0 = p[6] + z5 / z3 * (p[3] - p[6])
    a3 = p[6] + z5 / z4 * (p[4] - p[6])
    a2 = p[7] + z5 / z4 * (p[4] - p[7])
    a_turns = (cross(a0 - p[5], a3 - a0), cross(a3 - a0, a2 - a3),
               cross(a2 - a3, p[5] - a2))
    a_expected = (-z5 / (z3 * z4) * bracket((3, 4, 5, 6)),
                  (1 - z5 / z4) * z5 / (z3 * z4) * bracket((3, 4, 6, 7)),
                  -(1 - z5 / z4) / z4 * bracket((4, 5, 6, 7)))
    for actual, expected in zip(b_turns + a_turns, b_expected + a_expected):
        assert S.cancel(actual - expected) == 0
    return {'finite_section_turn_identities': 6}


def coincident_checks():
    x, y, z = (S.Matrix(S.symbols(f'{name}0 {name}1')) for name in ('X', 'Y', 'Z'))
    zero = S.zeros(2, 1)
    b = (zero, x, y, z)
    for shift in range(4):
        a = tuple(b[(i + shift) % 4] for i in range(4))
        closure = a[0] + a[2] - a[3] - b[1] + b[2] - b[3]
        upper = cross(b[1] - b[2], a[2] - b[3])
        lower = cross(a[0] - b[1], b[3] - b[2])
        if shift == 0:
            assert S.expand(lower - cross(closure, z - y)) == 0
        elif shift == 1:
            assert S.expand(lower) == 0
        elif shift == 2:
            assert S.expand(upper - cross(x - y, closure)) == 0
        else:
            equal_vectors(closure, zero)
            assert S.expand(lower - cross(y - x, z - y)) == 0

    s, t = S.symbols('s t')
    triangle = (zero, S.Matrix([1, 0]), S.Matrix([0, -1]))

    def polygon(flat, rotation, fraction):
        vertices = [None] * 4
        true = [i for i in range(4) if i != flat]
        for index, vertex in enumerate(true):
            vertices[vertex] = triangle[(index + rotation) % 3]
        vertices[flat] = (1 - fraction) * vertices[(flat - 1) % 4] + fraction * vertices[(flat + 1) % 4]
        return vertices

    counts = {'inconsistent': 0, 'endpoint_or_outside': 0, 'nonpositive_cap': 0}
    rows = []
    for flat_b, flat_a, rotation in product((1, 2, 3), (0, 2, 3), range(3)):
        b = polygon(flat_b, 0, s)
        a = polygon(flat_a, rotation, t)
        equations = a[0] + a[2] - a[3] - b[1] + b[2] - b[3]
        upper = S.factor(cross(b[1] - b[2], a[2] - b[3]))
        lower = S.factor(cross(a[0] - b[1], b[3] - b[2]))
        matrix, rhs = S.linear_eq_to_matrix(equations, (s, t))
        if matrix.rank() < matrix.row_join(rhs).rank():
            kind = 'inconsistent'
            solution = 'none'
        else:
            solutions = list(S.linsolve(list(equations), (s, t)))
            assert len(solutions) == 1
            sol_s, sol_t = solutions[0]
            assert all(S.expand(value.subs({s: sol_s, t: sol_t}, simultaneous=True)) == 0
                       for value in equations)
            solution = str((sol_s, sol_t))
            if not (sol_s.free_symbols | sol_t.free_symbols):
                assert not (0 < sol_s < 1 and 0 < sol_t < 1)
                kind = 'endpoint_or_outside'
            elif sol_t == t and S.expand(sol_s - t) in (-1, 1):
                kind = 'endpoint_or_outside'
            else:
                assert sol_s == sol_t == t
                upper = S.factor(upper.subs(s, t))
                assert upper in (0, -t, t - 1)
                kind = 'nonpositive_cap'
        counts[kind] += 1
        rows.append({'flat_b': flat_b, 'flat_a': flat_a, 'rotation': rotation,
                     'solution': solution, 'upper_cap_numerator': str(upper),
                     'lower_cap_numerator': str(lower), 'obstruction': kind})
    assert sum(counts.values()) == 27
    return {'quadrilateral_matches': 4, 'triangle_matches': 27,
            'triangle_obstructions': counts, 'triangle_records': rows}


def build(directory):
    started = time.monotonic()
    result = {**metric_checks(), **section_checks(), **finite_turn_checks(), **coincident_checks()}
    directory.mkdir(parents=True, exist_ok=True)
    n, base, *_ = shared.base_formula()
    positive = base + angles.cap_units(1, 1)
    lit = shared.common.lit
    common = [lit((0, 1, 2, 3)), -lit((0, 1, 2, 7)),
              -lit((3, 4, 5, 6)), -lit((4, 5, 6, 7))]
    first = lit((0, 1, 5, 6))
    formulas = {
        'c1_sections_common.cnf': positive + [[-value for value in common]],
        'c1_sections_nesting.cnf': positive + [[first], [lit((0, 1, 5, 7))]],
        'c1_sections_inner_b.cnf': positive + [[first], [-lit((0, 2, 3, 7))]],
        'c1_sections_inner_a.cnf': positive + [[-first], [-lit((3, 4, 6, 7))]],
    }
    for upper, lower in ((-1, -1), (-1, 1), (1, -1)):
        formulas[f'c1_sections_cap_{upper}_{lower}.cnf'] = base + angles.cap_units(upper, lower)
    for name, clauses in formulas.items():
        write_cnf(directory / name, n, clauses)
    result.update(unsat_obligations=list(formulas),
                  domain='both regular C1 caps; 0<alpha,beta<1; actual embedded limiting sequences',
                  markings=[1, 2], requires_finite_section_geometry=True,
                  replay_seconds=time.monotonic() - started)
    (directory / 'c1_sections.json').write_text(json.dumps(result, indent=2) + '\n')
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('output', type=Path)
    result = build(parser.parse_args().output)
    print(json.dumps({key: value for key, value in result.items() if key != 'triangle_records'}))


if __name__ == '__main__':
    if not __debug__:
        raise RuntimeError('run with assertions enabled')
    main()
