#!/usr/bin/env python3
"""Exact common-line limit reduction for marking 1, large-step mask 04.

Usage: python remaining_ray1_mask04.py OUTPUT [--models MANIFEST]

The finite cover uses the full shared 18,080 generic models, without a
mask-specific separation filter.  It writes 50 nonparallel-line CNFs,
two rhombus CNFs, and an exact coverage record.  This proves the limit
reduction documented in remaining_ray1_mask04.md, not an exclusion of
the remaining common-line boundary.
"""

import argparse
from itertools import combinations, product
import json
from pathlib import Path

import numpy as np
import sympy as s

import solver_remaining_chambers as shared

A = (1, 2, 3, 4)
B = (0, 6, 7, 5)
Q = tuple(combinations(range(8), 4))
QI = {quad: index for index, quad in enumerate(Q)}
HALF = s.Rational(1, 2)

# Coordinates encode entire weak-order cells, not metric samples.
A_LINES = {
    'I': (0, -2, -1, -3),
    'II': (0, -3, 1, -2),
    'II_left': (0, -2, 0, -1),
    'II_right': (0, -2, 1, -2),
    'II_both': (0, -1, 0, -1),
}
B_LINES = {
    'I': (0, 1, 2, 3),
    'II': (0, -1, 3, 2),
    'II_left': (0, 0, 2, 1),
    'II_right': (0, -1, 2, 2),
    'II_both': (0, 0, 1, 1),
}


def sign(value):
    return int(value > 0)-int(value < 0)


def literal(quad):
    parity = sum(quad[i] > quad[j] for i in range(4) for j in range(i+1, 4))
    return (-1)**parity*(QI[tuple(sorted(quad))]+1)


def ellipse_types():
    """All rank-three cap sign types with at most one zero area.

    The affine circuit is (-D123,D023,-D013,D012).  Neither apex
    (positions 0 and 3) can belong to the convex hull of the other
    three points: the two foci are strictly inside a genuine ellipse.
    """
    result = []
    for areas in product((-1, 0, 1), repeat=4):
        if areas.count(0) > 1:
            continue
        circuit = (-areas[3], areas[2], -areas[1], areas[0])
        if not (1 in circuit and -1 in circuit):
            continue
        if any(circuit[i] and all(value == 0 or value == -circuit[i]
                                 for j, value in enumerate(circuit) if j != i)
               for i in (0, 3)):
            continue
        result.append(areas)
    assert len(result) == 22
    return tuple(result)


def area_units(cap, other, areas, axial_sign):
    return [axial_sign*value*literal(triple+(vertex,))
            for triple, value in zip(combinations(cap, 3), areas) if value
            for vertex in other]


def line_units(x, y, orientation=1):
    result = []
    for ai, aj in combinations(range(4), 2):
        for bi, bj in combinations(range(4), 2):
            value = sign(x[aj]-x[ai])*sign(y[bj]-y[bi])*orientation
            if value:
                result.append(value*literal((A[ai], A[aj], B[bi], B[bj])))
    return result


def selected(models, units):
    keep = np.ones(len(models), dtype=bool)
    for unit in units:
        keep &= models[:, abs(unit)-1] == sign(unit)
    return np.flatnonzero(keep)


def assert_implied(models, indices, units):
    assert len(indices)
    for unit in units:
        assert np.all(models[indices, abs(unit)-1] == sign(unit)), unit


def rhombus_units():
    a, x, y = s.symbols('a x y', positive=True)
    points = {
        0: (0, 0, 0), 1: (0, 0, 1), 2: (-a, 0, 1),
        3: (x, y, 1), 4: (x-a, y, 1),
        5: (HALF, 0, 0), 6: (0, 0, 0), 7: (HALF, 0, 0),
    }
    result = []
    for quad in Q:
        first, *rest = quad
        determinant = s.factor(s.Matrix([
            [points[i][axis]-points[first][axis] for axis in range(3)]
            for i in rest]).det())
        if determinant == 0:
            continue
        # Every nonzero expression is independent of x; its sign is
        # therefore valid for arbitrary real horizontal rhombus shape.
        assert not determinant.has(x)
        assert determinant.is_positive is True or determinant.is_negative is True
        result.append((1 if determinant.is_positive else -1)*literal(quad))
    assert len(result) == 32
    return result


def exact_checks():
    h0, h1, h2, h3, h7, dot = s.symbols('h0 h1 h2 h3 h7 dot')
    height1 = h0*h0
    height2 = (1-h0-h1)**2-h1*h1
    height7 = height1+h7*h7-(h0+h7-1)**2
    edge27 = h7*h7+h1*h1-2*dot-(h0+h1+h7-1)**2-height7+height2
    assert s.expand(edge27-(1-2*h0-2*h1*h7-2*dot)) == 0

    # Equal focal sums give the exact chain-excess identity.
    rx, px, a, c = s.symbols('rx px a c')
    norm_difference = c*c-(1-a-c)**2
    # |R-P3|^2-|R-P2|^2 = -2*a*(rx-px)+a^2,
    # |P3|^2-|P2|^2 = (1-h1-a)^2-h1^2 = 2*a*px+a^2.
    px_expression = ((1-h1-a)**2-h1*h1-a*a)/(2*a)
    rx_expression = s.solve(-2*a*(rx-px_expression)+a*a-norm_difference, rx)[0]
    assert s.cancel(rx_expression+(1-a)*(h1+a+c-1)/a) == 0

    cosine, half_sine = s.symbols('cosine half_sine')
    norm_identity = c*c+a*a+2*a*c*cosine-(1-a-c)**2
    assert s.expand(norm_identity-2*((a+c-HALF)-a*c*(1-cosine))) == 0
    gap = HALF-(half_sine**2/2+(1-half_sine)/(2*(1+half_sine)))
    assert s.cancel(gap-half_sine*(1-half_sine)*(half_sine+2)/(2*(half_sine+1))) == 0

    u, v = s.symbols('u v')
    assert s.expand(HALF-(u+v-2*u*v)-2*(HALF-u)*(HALF-v)) == 0
    assert s.expand((h2-h1)**2-(1-h1-h2)**2
                    +(1-2*h1)*(1-2*h2)) == 0
    assert s.expand((h2-h3)**2-(1-h2-h3)**2
                    +(1-2*h2)*(1-2*h3)) == 0

    # The endpoint chain=1 argument, including unequal outer weights.
    qx = s.symbols('qx')
    endpoint = h3*h3+(h1-h3)**2+2*(h1-h3)*qx-h1*h1
    assert s.expand(endpoint-2*(h1-h3)*(qx-h3)) == 0

    # The four endpoint triples form one orbit of the graph/cap metric
    # symmetries. These preserve both chain sums up to exchange.
    transformations = [tuple(range(8)), tuple((5-i) % 8 for i in range(8)),
                       tuple((i+4) % 8 for i in range(8)),
                       tuple((1-i) % 8 for i in range(8))]
    images = {tuple(sorted(p[i] for i in (1, 2, 3))) for p in transformations}
    assert images == {(1, 2, 3), (2, 3, 4), (5, 6, 7), (0, 6, 7)}
    return {'stress_identity': 'h0=1/2-h1*h7-P2.dot(P7)',
            'wedge_gap': str(s.factor(gap)),
            'endpoint_symmetries': transformations,
            'rhombus_fixed_signs': 32}


def finite_cover(models):
    kinds = ellipse_types()
    af = [selected(models, area_units(A, B, row, -1)) for row in kinds]
    bf = [selected(models, area_units(B, A, row, 1)) for row in kinds]
    nonlinear, all_members = [], set()
    core = {(1, 0, -1, -1), (1, 1, -1, -1), (1, 1, 0, -1)}
    core_count, endpoint_count = 0, 0
    endpoint_models = set()
    for i, aa in enumerate(kinds):
        for j, bb in enumerate(kinds):
            indices = np.intersect1d(af[i], bf[j], assume_unique=True)
            if not len(indices):
                continue
            nonlinear.append({'A': aa, 'B': bb, 'models': indices.tolist()})
            all_members.update(map(int, indices))
            if aa in core and bb in core:
                core_count += 1
                assert_implied(models, indices, [literal((2, 3, 6, 7)),
                    literal((1, 4, 6, 7)), -literal((2, 3, 0, 5)),
                    -literal((1, 4, 0, 5))])
            else:
                endpoint_count += 1
                assert 0 in (aa[0], aa[3], bb[0], bb[3])
            if aa == (0, -1, -1, 1):
                endpoint_models.update(map(int, indices))
                # All four B vectors lie in the cone between T=P4-P3
                # and -E. A positive y component is -cross(P1P2,X).
                for edge in ((0, 6), (7, 0), (6, 5), (7, 5)):
                    assert_implied(models, indices,
                        [-literal((1, 2)+edge), literal((3, 4)+edge)])
    assert len(nonlinear) == 21 and len(all_members) == 52
    assert (core_count, endpoint_count, len(endpoint_models)) == (9, 12, 12)

    orders = [row for row in product(range(4), repeat=4)
              if set(row) == set(range(max(row)+1)) and max(row) > 0]
    assert len(orders) == 74
    one_flat = []
    for name, x in A_LINES.items():
        cells = []
        for y in orders:
            line_matches = selected(models, line_units(x, y))
            if not len(line_matches):
                continue
            for j, areas in enumerate(kinds):
                indices = np.intersect1d(line_matches, bf[j], assume_unique=True)
                if len(indices):
                    cells.append({'height_order': y, 'areas': areas,
                                  'models': indices.tolist()})
        one_flat.append({'name': name, 'line_order': x, 'cells': cells})
    assert [len(row['cells']) for row in one_flat] == [3, 0, 1, 1, 5]
    allowed_orders = {'I': {(0, 1, 0, 1)}, 'II': set(),
                      'II_left': {(0, 1, 1, 1)},
                      'II_right': {(0, 0, 0, 1)},
                      'II_both': {(0, 1, 0, 1), (0, 1, 1, 1), (0, 0, 0, 1)}}
    for row in one_flat:
        assert {tuple(cell['height_order']) for cell in row['cells']} == allowed_orders[row['name']]

    two_flat = []
    for an, x in A_LINES.items():
        for bn, y in B_LINES.items():
            for orientation in (-1, 1):
                units = line_units(x, y, orientation)
                assert len(selected(models, units)) == 0
                two_flat.append({'A': an, 'B': bn, 'orientation': orientation,
                                 'units': units})
    assert len(two_flat) == 50
    rhombus = rhombus_units()
    assert len(selected(models, rhombus)) == len(selected(models, [-v for v in rhombus])) == 0
    return {'noncollinear_pairs': nonlinear, 'one_collinear_cap': one_flat,
            'nonparallel_collinear_caps': two_flat, 'rhombus_units': rhombus}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('output', type=Path)
    parser.add_argument('--models', type=Path)
    args = parser.parse_args()
    args.output.mkdir(parents=True, exist_ok=True)
    n, clauses, faces, edges, neighbors, pairs = shared.base_formula()
    if args.models:
        source = json.loads(args.models.read_text())
        raw = source.get('all_models', source.get('models'))
        assert raw is not None
        models = tuple(sorted(tuple(1 if value == '+' else -1 for value in row)
                              if isinstance(row, str) else tuple(row) for row in raw))
    else:
        symmetries = shared.topological_symmetries(faces, pairs)
        models, _ = shared.enumerate_models(n, clauses, symmetries)
    assert len(models) == len(set(models)) == 18080
    assert all(len(row) == 70 and row[0] == 1 and set(row) == {-1, 1} for row in models)
    record = {'exact_checks': exact_checks(), 'models': len(models),
              'uses_mask_separation_filter': False,
              'cover': finite_cover(np.asarray(models, dtype=np.int8))}
    for row in record['cover']['nonparallel_collinear_caps']:
        name = f"two_flat_{row['A']}_{row['B']}_{'p' if row['orientation'] > 0 else 'm'}.cnf"
        shared.common.write_cnf(args.output/name, n, clauses+[[unit] for unit in row['units']])
    for orientation in (-1, 1):
        name = 'rhombus_'+('p' if orientation > 0 else 'm')+'.cnf'
        shared.common.write_cnf(args.output/name, n,
            clauses+[[orientation*unit] for unit in record['cover']['rhombus_units']])
    (args.output/'coverage.json').write_text(json.dumps(record, indent=2)+'\n')
    print(json.dumps({'models': len(models), 'noncollinear_pairs': 21,
                      'one_collinear_cells': 10, 'nonparallel_cases': 50,
                      'rhombus_cases': 2, 'status': 'common-line limit reduction only'}))


if __name__ == '__main__':
    if not __debug__:
        raise RuntimeError('run with assertions enabled')
    main()
