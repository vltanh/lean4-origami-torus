#!/usr/bin/env python3
"""Exact checks for the positive-weight one-flat/one-trapezoid blow-up.

Usage: python remaining_flat_blowup.py [OUTPUT_DIRECTORY]

The degenerate-norm cell cover is exhaustive.  The analytic exclusion in
remaining_flat_blowup.md covers its 24 cells with all eight limiting edge
weights positive.  The 1,268 cells with a zero weight remain outside this
theorem.  This is not a full common-line or fixed-modulus exclusion.
"""

from collections import Counter
from itertools import combinations, product
import json
from pathlib import Path
import sys

import sympy as s

import remaining_one_collinear as cover
from direct_metric import load_data
from solver_chambers import base_formula, enumerate_models, marked_symmetries
from verify_linking import SAT, lit

A, B = cover.A, cover.B
FREE = (1, 4, 5, 6, 7)
REQUIRED = (-lit((0, 1, 2, 4)), lit((0, 1, 4, 6)),
            lit((0, 3, 4, 5)), lit((1, 2, 5, 6)))


def degenerate_cover(models):
    counts = Counter()
    zero_cells = []
    for a, y, beta, witnesses in cover.sign_cells(models):
        for x in cover.ORDERS:
            if not cover.axes_compatible(x, y, beta):
                continue
            coefficients = cover.projected_coefficients(a, x)
            if any(coefficients):
                # No surviving topological cell has mixed coefficients.
                assert min(coefficients) >= 0 or max(coefficients) <= 0
                counts['strict_projection'] += 1
                continue
            counts['zero_projection'] += 1
            counts[tuple(sorted(Counter(a).values()))] += 1
            zero_cells.append({'a': a, 'x': x, 'y': y, 'beta': beta,
                               'models': [i for i in range(1888) if witnesses >> i & 1]})
    assert counts == Counter({'strict_projection': 3494, 'zero_projection': 1292,
                              (1, 3): 1148, (1, 1, 2): 144})
    positive = [row for row in zero_cells if all(
        row['a'][i] != row['a'][(i+1) % 4] and row['x'][i] != row['x'][(i+1) % 4]
        for i in range(4))]
    assert len(positive) == 24
    pairs = [next((i, j) for i, j in combinations(range(4), 2)
                  if row['a'][i] == row['a'][j])
             for row in zero_cells if sorted(Counter(row['a']).values()) == [1, 1, 2]]
    assert sum((j-i) % 4 == 2 for i, j in pairs) == 80
    assert sum((j-i) % 4 != 2 for i, j in pairs) == 64
    return zero_cells, positive


def rank_tuple(values):
    order = sorted(set(values))
    return tuple(order.index(value) for value in values)


def canonical_maps(rows, symmetries):
    permutations = [entry['permutation'] for entry in symmetries
                    if {entry['permutation'][i] for i in A} == set(A)]
    for row in rows:
        maps = []
        for permutation, sx, sy in product(permutations, (-1, 1), (-1, 1)):
            ai = [A.index(permutation[i]) for i in A]
            bi = [B.index(permutation[i]) for i in B]
            a = rank_tuple([sx*row['a'][i] for i in ai])
            x = rank_tuple([sx*row['x'][i] for i in bi])
            y = rank_tuple([sy*row['y'][i] for i in bi])
            beta = []
            for triple in cover.TRIPLES:
                mapped = [bi[i] for i in triple]
                parity = (-1)**sum(mapped[i] > mapped[j] for i, j in combinations(range(3), 2))
                beta.append(sx*sy*parity*row['beta'][cover.TRIPLES.index(tuple(sorted(mapped)))])
            if (a == (0, 1, 2, 1) and y == (0, 0, 1, 1) and beta == [1]*4
                    and x[0] == 0 and x[2] == max(x)
                    and 0 < x[1] < max(x) and 0 < x[3] < max(x)):
                maps.append({'permutation': permutation, 'horizontal_reflection': sx,
                             'normal_reflection': sy})
        assert maps, row
        row['canonical_map'] = maps[0]


def required_sign_certificate():
    variables, original, *_ = base_formula()
    assert original[0] == [1]
    # Allow either orientation of the actual moving frame.
    clauses = [list(row) for row in original[1:]]
    a, y = (0, 1, 2, 1), (0, 0, 1, 1)
    for i, j in cover.PAIRS:
        for k, l in cover.PAIRS:
            value = -cover.pair_sign(a, i, j)*cover.pair_sign(y, k, l)
            if value:
                clauses.append([value*lit((A[i], A[j], B[k], B[l]))])
    for triple in cover.TRIPLES:
        for vertex in A:
            clauses.append([-lit(tuple(B[i] for i in triple)+(vertex,))])
    # A positive leading bracket fixes its generic completion.  Every
    # other sign, including both same-cap four-brackets, remains free.
    clauses.append([-literal for literal in REQUIRED])
    assert SAT(variables, clauses).check() == -1
    return variables, clauses


def symbolic_metric():
    _, _, edges, _, _, kx, ky = load_data()
    r, u, z, t = s.symbols('r u z t')
    half = s.Rational(1, 2)
    xx = [s.Integer(0)] + list(s.symbols('x1:8'))
    gamma = [s.Integer(0)] + list(s.symbols('g1:8'))
    U = {0: s.Integer(0), 2: xx[2], 3: xx[3]}
    H = {0: s.Integer(0), 2: gamma[2], 3: gamma[3]}
    Z = {0: s.Integer(0), 2: s.Integer(0), 3: s.Integer(0)}
    for i in FREE:
        U[i], H[i], Z[i] = s.symbols(f'U{i} H{i} Z{i}')
    variables = xx[1:] + gamma[1:] + [U[i] for i in FREE] + [H[i] for i in FREE]
    levels = {i: int(i in B) for i in range(8)}
    metric_edges = [e for e in edges if e not in ((0, 2), (0, 3), (2, 3))]
    equations = []
    for i, j in metric_edges:
        du, dz = U[j]-U[i], Z[j]-Z[i]
        dx, dg, dh = xx[j]-xx[i]+kx[i, j], gamma[j]-gamma[i], H[j]-H[i]
        ell = levels[j]-levels[i]
        equations.append(s.expand(du**2+dz**2-dx**2-ell*dh-2*ky[i, j]*dg+t*(dh**2-dg**2)))
    assert len(equations) == 21 and len(variables) == 24

    # P=-U, so the limiting horizontal positions have the canonical
    # increasing order.  H is the face chart's rescaled axial correction.
    P = (0, r, 0, u, half, r, half, z)
    family_x = (0, -r, 0, -u, 0, r-half, 0, z-half)
    d = half-2*r
    g2 = r-s.Rational(1, 8)
    family_gamma = (0, r/2, g2, g2+d*u, r-s.Rational(1, 4), r/2,
                    g2+d/2, g2+d*z)
    planar = ({xx[i]: family_x[i] for i in range(1, 8)}
              | {gamma[i]: family_gamma[i] for i in range(1, 8)}
              | {U[i]: -P[i] for i in FREE}
              | {H[i]: family_gamma[i] for i in FREE})
    zero_normals = {Z[i]: 0 for i in FREE}
    assert all(s.expand(equation.subs(planar).subs(zero_normals)) == 0 for equation in equations)

    # The actual limit must be this family, rather than another planar
    # solution.  All sixteen stress residuals are affine in the fourteen
    # intrinsic unknowns.  Together with the eight known short weights
    # they have full column rank, and the displayed family solves them.
    # The omitted common long-distance term cancels in every cross
    # polarization because these sixteen baseline vertical steps have
    # the same square.
    assert all(ky[i, j]**2 == s.Rational(1, 4) for i in A for j in B)
    intrinsic_x = lambda i, j: xx[j]-xx[i]+kx[i, j]
    intrinsic_g = lambda i, j: gamma[j]-gamma[i]
    distance = lambda i, j: (intrinsic_x(i, j)**2+2*ky[i, j]*intrinsic_g(i, j)
                              +t*intrinsic_g(i, j)**2)
    weights_a = (r, half-r, half-r, r)
    weights_b = (u, half-u, half-z, z)
    stress_equations = []
    for i, (ai, aj) in enumerate(zip(A, A[1:]+A[:1])):
        for j, (bi, bj) in enumerate(zip(B, B[1:]+B[:1])):
            stress = (intrinsic_x(ai, aj)*intrinsic_x(bi, bj)
                      +t*intrinsic_g(ai, aj)*intrinsic_g(bi, bj)
                      -(distance(ai, bj)+distance(aj, bi)-distance(ai, bi)-distance(aj, bj))/2)
            target = weights_a[i]*weights_b[j]*(0 if (i < 2) == (j < 2) else 2)
            residual = s.expand(stress-target)
            assert not residual.has(t)
            stress_equations.append(residual)
    for cap, weights in ((A, weights_a), (B, weights_b)):
        stress_equations.extend(intrinsic_x(i, j)+weight
                                for (i, j), weight in zip(zip(cap, cap[1:]+cap[:1]), weights))
    intrinsic_variables = xx[1:]+gamma[1:]
    matrix, rhs = s.linear_eq_to_matrix(stress_equations, intrinsic_variables)
    assert matrix.shape == (24, 14) and matrix.rank() == 14
    intrinsic_family = s.Matrix(list(family_x[1:])+list(family_gamma[1:]))
    assert all(s.expand(value) == 0 for value in matrix*intrinsic_family-rhs)

    # Once x,gamma and U are fixed, the fourteen non-anchor cross-edge
    # equations at t=0 determine all five free zeta coordinates uniquely.
    planar_without_heights = {key: value for key, value in planar.items()
                              if key not in {H[i] for i in FREE}}
    height_equations = [s.expand(equation.subs(t, 0).subs(zero_normals).subs(planar_without_heights))
                        for equation, (i, j) in zip(equations, metric_edges) if levels[i] != levels[j]]
    height_matrix, height_rhs = s.linear_eq_to_matrix(height_equations, [H[i] for i in FREE])
    assert height_matrix.shape == (14, 5) and height_matrix.rank() == 5
    assert all(s.expand(value) == 0 for value in
               height_matrix*s.Matrix([family_gamma[i] for i in FREE])-height_rhs)
    print('PASS necessity: intrinsic stress matrix rank 14; cross-edge height matrix rank 5', flush=True)

    # Choosing x1,x3,x7 fixes the three family parameters.  All other
    # planar variables are solved by the implicit-function theorem.
    dependent = [value for value in variables if value not in (xx[1], xx[3], xx[7])]
    jacobian = s.Matrix(equations).jacobian(dependent).subs(planar).subs(t, 0)
    determinant = s.factor(jacobian.det(method='domain-ge'))
    assert determinant == 16384*r**2*z*(2*r-1)**2*(2*u-1)*(2*z-1)

    # Solve the complete quadratic metric correction, not a subset of
    # edge equations.  The mode is A flat and B6=B7 at normal height 1.
    normal_mode = {Z[i]: int(i in (6, 7)) for i in FREE}
    forcing = s.Matrix([(Z[j]-Z[i])**2 for i, j in metric_edges]).subs(normal_mode)
    quadratic = jacobian.inv(method='DM')*(-forcing)
    cubic_coefficient = s.factor(quadratic[dependent.index(U[1])]-quadratic[dependent.index(U[5])])
    expected = -r/(1-2*u)-(half-r)/(2*z)
    assert s.factor(cubic_coefficient-expected) == 0

    points = {i: (-U[i], Z[i], levels[i]-2*t*H[i]) for i in range(8)}
    forms = []
    for literal in REQUIRED:
        quad = tuple(combinations(range(8), 4))[abs(literal)-1]
        first, *rest = quad
        bracket = s.Matrix([[points[i][k]-points[first][k] for k in range(3)] for i in rest]).det()
        forms.append(s.expand(cover.sign(literal)*bracket.subs(planar)))
    numerator = 4+t*(4*r-1)**2
    denominator = 4+t*(32*r*u-8*r-8*u+1)
    polynomial_weights = ((1-2*u)*numerator, 2*u*numerator, numerator, denominator)
    combined = s.factor(sum(weight*form for weight, form in zip(polynomial_weights, forms)))
    assert s.expand(combined+4*r*(half-r)*u*t*numerator*Z[6]) == 0
    # D is bilinear in r,u.  These corner values certify D>=4-3t>0.
    assert {s.expand(denominator.subs({r: rr, u: uu}))
            for rr, uu in product((0, half), repeat=2)} == {4+t, 4-3*t}
    print('PASS exact planar family; Jacobian determinant:', determinant, flush=True)
    print('PASS exact-in-t positive Farkas identity and cubic coefficient:', expected, flush=True)
    return {'jacobian_determinant': str(determinant), 'cubic_coefficient': str(expected),
            'farkas_numerator': str(numerator), 'farkas_denominator': str(denominator)}


def main():
    if not __debug__:
        raise RuntimeError('run with assertions enabled')
    if len(sys.argv) > 2:
        raise SystemExit(__doc__)
    output = Path(sys.argv[1]) if len(sys.argv) == 2 else None
    if output:
        output.mkdir(parents=True, exist_ok=True)
    symmetries = marked_symmetries()
    variables, clauses, *_ = base_formula()
    models = enumerate_models(variables, clauses, symmetries)
    zero_cells, positive = degenerate_cover(models)
    canonical_maps(positive, symmetries)
    print('PASS degenerate norm: 3494 strict cells; 1292 zero cells; all 24 positive-weight cells canonical', flush=True)
    proof_variables, proof_clauses = required_sign_certificate()
    print(f'PASS four required weak signs: UNSAT; {proof_variables} variables, {len(proof_clauses)} clauses', flush=True)
    identities = symbolic_metric()
    if output:
        coverage = clauses + [[-(i+1)*value for i, value in enumerate(model)] for model in models]
        cover.write_cnf(output/'flat_blowup_model_coverage.cnf', variables, coverage)
        cover.write_cnf(output/'flat_blowup_required_signs.cnf', proof_variables, proof_clauses)
        (output/'flat_blowup_cells.json').write_text(json.dumps({
            'zero_cells': zero_cells, 'positive_weight_cells': positive, 'identities': identities,
        }, indent=2)+'\n')
    print('Scope: positive limiting weights in the one-flat/one-trapezoid blow-up; zero-weight cases remain open.')


if __name__ == '__main__':
    main()
