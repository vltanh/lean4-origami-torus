#!/usr/bin/env python3
"""Exact finite checks for the nondegenerate-cap limit exclusion.

Usage: python verify_cap_limit.py [COVERAGE.cnf]

The optional CNF is replayed with orientation_checkpoint/check_unsat.cpp.
This proves the finite algebra in cap_limit.md, not a fixed-height
exclusion. No floating-point computations or nonlinear solver are used.
"""

from collections import Counter
from itertools import combinations, product
from pathlib import Path
import sys

import sympy as s

import direct_metric as direct
from verify_linking import CNF, SAT, formula, lit

A_CAP, B_CAP = (0, 1, 4, 5), (2, 3, 6, 7)
MASK = s.Matrix([[1, 0, 1, 1], [1, 0, 0, 0],
                 [1, 1, 1, 0], [0, 0, 1, 0]])
QUADS = tuple(combinations(range(8), 4))


def edges(cap):
    return tuple(zip(cap, cap[1:] + cap[:1]))


def bracket_sign(model, points):
    value = lit(points)
    return model[abs(value) - 1] * (1 if value > 0 else -1)


def stress_identity():
    faces, shifts, graph, _, _, kx, ky = direct.load_data()
    x = [s.Integer(0)] + list(s.symbols('x1:8'))
    gamma = [s.Integer(0)] + list(s.symbols('g1:8'))
    t = s.Symbol('t', positive=True)
    X = lambda i, j: x[j] - x[i] + s.Rational(kx[i, j])
    G = lambda i, j: gamma[j] - gamma[i]
    # The common 1/(4t) part of every cross distance cancels.
    D = lambda i, j: X(i, j)**2 + 2*s.Rational(ky[i, j])*G(i, j) + t*G(i, j)**2
    entries = []
    for a, b in edges(A_CAP):
        for c, d in edges(B_CAP):
            value = s.expand(X(a, b)*X(c, d) + t*G(a, b)*G(c, d)
                             - (D(a, d)+D(b, c)-D(a, c)-D(b, d))/2)
            assert s.Poly(value, *(x[1:]+gamma[1:])).total_degree() <= 1
            entries.append(value)
    R = s.Matrix(4, 4, entries)
    assert s.expand(sum(MASK[i, j]*R[i, j] for i in range(4) for j in range(4))) == s.Rational(1, 2)
    assert s.expand(sum(R)) == 1
    # This fixed marked symmetry exchanges the even and odd edge pairs.
    permutation = (0, 5, 2, 7, 4, 1, 6, 3)
    matrix = s.Matrix([[-1, -1], [0, 1]])
    gauge = [s.Matrix([0, 0]) for _ in range(8)]
    gauge[4] = s.Matrix([1, 0])
    assert {tuple(sorted(permutation[v] for v in f)) for f in faces} == {tuple(sorted(f)) for f in faces}
    for i, j in graph:
        assert s.Matrix(shifts[permutation[i], permutation[j]]) == matrix*s.Matrix(shifts[i, j])+gauge[j]-gauge[i]
    assert all(MASK[3-i, 3-j] == 1-MASK[i, j] for i in range(4) for j in range(4))


def cap_models(output=None):
    n, clauses, _, _, _ = formula(7)
    extra = CNF(n)
    extra.unlink(A_CAP, B_CAP)
    clauses = clauses + extra.C
    for cap, opposite in ((A_CAP, B_CAP), (B_CAP, A_CAP)):
        for tri in combinations(cap, 3):
            anchor = lit(tri+(opposite[0],))
            for vertex in opposite[1:]:
                value = lit(tri+(vertex,))
                clauses.extend([[-anchor, value], [anchor, -value]])
    assert extra.n == 215 and len(clauses) == 7818
    solver = SAT(extra.n, clauses)
    models = []
    while True:
        status = solver.check()
        if status == -1:
            break
        assert status == 1
        model = tuple(solver.model())
        models.append(model)
        solver.add([-(i+1)*v for i, v in enumerate(model)])
    assert len(models) == len(set(models)) == 16
    if output is not None:
        blocked = clauses + [[-(i+1)*v for i, v in enumerate(model)] for model in models]
        output.write_text(f'p cnf {extra.n} {len(blocked)}\n' + ''.join(
            ' '.join(map(str, row))+' 0\n' for row in blocked))
    return models


def weak_orders(models):
    counts = Counter()
    for model in models:
        comparisons = [(i, 4+j, -bracket_sign(model, (a, b, c, d)), False)
                       for i, (a, b) in enumerate(edges(A_CAP))
                       for j, (c, d) in enumerate(edges(B_CAP))]
        turns = []
        for offset, cap, opposite, sign in ((0, A_CAP, B_CAP, 1), (4, B_CAP, A_CAP, -1)):
            for i in range(4):
                a, b, c = (cap[(i+j) % 4] for j in range(3))
                turn = sign*bracket_sign(model, (a, b, c, opposite[0]))
                turns.append(turn)
                comparisons.append((offset+i, offset+(i+1) % 4, turn, True))
        assert len(set(turns)) == 1
        for signs in product((-1, 1), repeat=7):
            signs = (1,)+signs
            reach = [[False]*8 for _ in range(8)]
            strict = []
            for i, j, value, is_strict in comparisons:
                if signs[i]*signs[j]*value < 0:
                    i, j = j, i
                reach[i][j] = True
                if is_strict:
                    strict.append((i, j))
            for k in range(8):
                for i in range(8):
                    for j in range(8):
                        reach[i][j] |= reach[i][k] and reach[k][j]
            if any(reach[j][i] for i, j in strict):
                continue
            left, components = set(range(8)), []
            while left:
                i = min(left)
                component = {j for j in left if j == i or reach[i][j] and reach[j][i]}
                left -= component
                if len(component) > 1:
                    components.append(tuple(sorted(component)))
            assert len(components) == 1
            component = components[0]
            assert component in ((0, 2, 4, 6), (1, 3, 5, 7))
            a, b, c, d = component
            assert signs[a] == -signs[b] and signs[c] == -signs[d]
            counts[component] += 1
    assert counts == Counter({(0, 2, 4, 6): 56, (1, 3, 5, 7): 56})


def trapezoid_signs(models):
    A, L, C, M, d = s.symbols('A L C M d')
    bases = (A, L, C, M)
    # Include both global orientations after the planar normalization.
    models = models + [tuple(-v for v in model) for model in models]
    counts = []
    for sign in (1, -1):
        points = {0: (0, 0, 0), 1: (0, -1, 0), 4: (L, -1, 0), 5: (A, 0, 0),
                  2: (0, 0, 1), 3: (sign*d, -sign, 1),
                  6: (sign*(d+M), -sign, 1), 7: (sign*C, 0, 1)}
        determinants = []
        for q in QUADS:
            origin, *rest = q
            determinants.append(s.expand(s.Matrix([
                [points[v][k]-points[origin][k] for k in range(3)] for v in rest]).det()))
        slack = -A-M-d if sign == 1 else d-C-L
        count = 0
        for model in models:
            inequalities = {s.expand(value*orientation) for value, orientation in zip(determinants, model)} - {s.Integer(0)}
            if inequalities & {-A, -L, -C, -M, s.Integer(-1)}:
                continue
            count += 1
            assert slack in inequalities
            for value in inequalities:
                if value in {*bases, s.Integer(1)}:
                    continue
                remainder = s.Poly(s.expand(value-slack), *bases, d)
                assert all(coefficient >= 0 for _, coefficient in remainder.terms())
                assert not remainder.as_expr().has(d)
        counts.append(count)
    assert counts == [4, 4]


def trapezoid_boundary_signs(models):
    """Retain the directions of a vanishing base in either cap.

    A bracket containing that actual short edge can be divided by its
    positive length before taking the limit.  The relative axial bound
    makes this the indicated planar directional derivative.  No relation
    between the two caps' collapsing base lengths is assumed.
    """
    A, L, C, M, d = s.symbols('A L C M d')
    bases = (A, L, C, M)
    collapsed_edges = {A: {0, 5}, L: {1, 4}, C: {2, 7}, M: {3, 6}}
    models = models + [tuple(-v for v in model) for model in models]
    count = 0
    for sign in (1, -1):
        points = {0: (0, 0, 0), 1: (0, -1, 0), 4: (L, -1, 0), 5: (A, 0, 0),
                  2: (0, 0, 1), 3: (sign*d, -sign, 1),
                  6: (sign*(d+M), -sign, 1), 7: (sign*C, 0, 1)}
        determinants = []
        for q in QUADS:
            origin, *rest = q
            determinants.append(s.expand(s.Matrix([
                [points[v][k]-points[origin][k] for k in range(3)] for v in rest]).det()))
        for zero_a, zero_b in product((None, A, L), (None, C, M)):
            zero = {v: 0 for v in (zero_a, zero_b) if v is not None}
            limits = []
            for q, determinant in zip(QUADS, determinants):
                value = determinant
                if value != 0:
                    for base in zero:
                        if collapsed_edges[base] <= set(q):
                            value = s.cancel(value/base)
                            assert value.is_polynomial(*bases, d)
                    value = s.expand(value.subs(zero))
                    # Every nonzero planar bracket lost at this boundary
                    # contains a collapsed base; normalization restores it.
                    assert value != 0
                limits.append(value)
            slack = s.expand((-A-M-d if sign == 1 else d-C-L).subs(zero))
            positive = {v for v in bases if v not in zero} | {s.Integer(1)}
            survivors = 0
            for model in models:
                inequalities = {s.expand(value*orientation) for value, orientation in zip(limits, model)} - {s.Integer(0)}
                if inequalities & {-v for v in positive}:
                    continue
                survivors += 1
                assert slack in inequalities
                for value in inequalities-positive:
                    remainder = s.Poly(s.expand(value-slack), *bases, d)
                    assert not remainder.as_expr().has(d)
                    assert all(coefficient >= 0 for _, coefficient in remainder.terms())
            assert survivors == 4
            count += 1
    assert count == 18


def quadratic_cones():
    A, L, C, M, X, gap = s.symbols('A L C M X gap')
    variables = (A, L, C, M, X, gap)
    pairs_checked = rays_checked = 0
    for orientation in (1, -1):
        U = X-A-M-gap if orientation == 1 else X+C+L+gap
        e = (X, L, A-L-X, -A)
        f = tuple(orientation*v for v in (U, M, C-M-U, -C))
        for signs in product((-1, 1), repeat=4):
            h = (signs[0]*X, L, signs[1]*(A-L-X), A)
            k = (signs[2]*U, M, signs[3]*(C-M-U), C)
            polynomial = s.expand(2*sum(MASK[i, j]*(h[i]*k[j]-e[i]*f[j])
                                      for i in range(4) for j in range(4))-sum(h)*sum(k))
            inequalities = (A, L, C, M, gap, h[0], h[2], k[0], k[2])
            H = s.Matrix([[s.diff(value, v) for v in variables] for value in inequalities])
            assert H.rank() == 6  # The cone has no lineality.
            rays = set()
            for active in combinations(range(9), 5):
                kernel = H[list(active), :].nullspace()
                if len(kernel) != 1:
                    continue
                for ray in (kernel[0], -kernel[0]):
                    if any(value < 0 for value in H*ray):
                        continue
                    denominator = s.ilcm(*(value.q for value in ray))
                    integer_ray = tuple(int(value*denominator) for value in ray)
                    divisor = s.igcd(*integer_ray)
                    rays.add(tuple(value//divisor for value in integer_ray))
            assert len(rays) <= 8
            quadratic = s.hessian(polynomial, variables)/2
            assert s.expand((s.Matrix(variables).T*quadratic*s.Matrix(variables))[0]-polynomial) == 0
            for left in rays:
                for right in rays:
                    assert (s.Matrix(left).T*quadratic*s.Matrix(right))[0] >= 0
                    pairs_checked += 1
            rays_checked += len(rays)
    return rays_checked, pairs_checked


def main():
    if not __debug__:
        raise RuntimeError('run with assertions enabled')
    if len(sys.argv) > 2:
        raise SystemExit(__doc__)
    stress_identity()
    models = cap_models(Path(sys.argv[1]) if len(sys.argv) == 2 else None)
    weak_orders(models)
    trapezoid_signs(models)
    trapezoid_boundary_signs(models)
    rays, pairs = quadratic_cones()
    print('PASS exact stress mask, marked symmetry, 16 models and 112 weak angular orders')
    print('PASS both trapezoid separation inequalities, with both global orientations retained')
    print('PASS all18 one-zero-base-per-cap boundary sign checks, with virtual directions retained')
    print(f'PASS 32 rational sign cones: {rays} rays and {pairs} nonnegative bilinear pairs')
    print('Scope: excludes limits with both caps having no collinear triple; full ray 3 remains open')


if __name__ == '__main__':
    main()
