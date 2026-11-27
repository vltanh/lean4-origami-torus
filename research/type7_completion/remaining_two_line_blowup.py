#!/usr/bin/env python3
"""Exclude 16 one-zero and 32 paired-zero two-line blow-up orders.

Usage: python remaining_two_line_blowup.py [OUTPUT_DIRECTORY]

Physical lengths use the original common-line seminorm |Delta X|.
The collapsed edge is normalized at its own stretched scale. No ratio
between its length, the normal width, and 1/y^2 is assumed.
"""

from itertools import combinations, product
import json
from pathlib import Path
import sys

import sympy as s

import common_line_edge_collapse as two_line
import exhaustive_collinear_caps as collinear
from direct_metric import load_data
from remaining_flat_blowup import rank_tuple
import solver_chambers as compiler
from verify_linking import SAT, lit

A, B = collinear.A, collinear.B
REQUIRED = (lit((0, 1, 2, 4)), lit((1, 2, 3, 4)),
            -lit((1, 2, 4, 7)), lit((0, 1, 4, 5)))
FREE = (1, 4, 5, 6, 7)


def canonical_maps(rows, symmetries, target_b=(1, 2, 3, 0)):
    phase = [entry['permutation'] for entry in symmetries if entry['phase_preserving']]
    for row in rows:
        values = dict(zip(A, row['a'])) | dict(zip(B, row['b']))
        maps = []
        for permutation, reflection in product(phase, (-1, 1)):
            a = rank_tuple([reflection*values[permutation[i]] for i in A])
            b = rank_tuple([reflection*values[permutation[i]] for i in B])
            if (a, b) == ((0, 1, 1, 2), target_b):
                maps.append({'permutation': permutation, 'horizontal_reflection': reflection})
        assert maps, row
        row['canonical_map'] = maps[0]


def sign_certificate(b=(1, 2, 3, 0)):
    variables, original, *_ = compiler.base_formula()
    assert original[0] == [1]
    clauses = [list(row) for row in original[1:]]
    a = (0, 1, 1, 2)
    for i, j in combinations(range(4), 2):
        for k, l in combinations(range(4), 2):
            value = -collinear.sign(a[j]-a[i])*collinear.sign(b[l]-b[k])
            if value:
                clauses.append([value*lit((A[i], A[j], B[k], B[l]))])
    clauses.append([-literal for literal in REQUIRED])
    assert SAT(variables, clauses).check() == -1
    return variables, clauses


def exact_checks():
    _, _, edges, _, _, kx, ky = load_data()
    r, u, v, t = s.symbols('r u v t')
    half = s.Rational(1, 2)
    w = half-v
    physical = (0, r, 0, u, r, half, v, -w)
    ha, hb = (r, 0, half-r, half), (u, v-u, half, w)
    family_x = (0, -r, -r+v, -r-u+v, half-r, 0, half-r, -r)
    family_g = (0, r/2, r/2+v/2-s.Rational(1, 8),
                r/2-u/2+v/2-s.Rational(1, 8), r/2,
                s.Rational(1, 4), r/2-s.Rational(1, 8), r/2+s.Rational(1, 8))
    family_zeta = (0, r/2, family_g[2], family_g[3], r/2,
                   2*r-s.Rational(3, 4), r/2-s.Rational(1, 8), r/2+s.Rational(1, 8))
    family_u = tuple(-physical[i]+(family_x[2] if i in B else 0) for i in range(8))
    assert s.expand(family_u[3]-family_x[3]) == 0
    xx = [s.Integer(0)]+list(s.symbols('x1:8'))
    gamma = [s.Integer(0)]+list(s.symbols('g1:8'))
    X = lambda i, j: xx[j]-xx[i]+kx[i, j]
    G = lambda i, j: gamma[j]-gamma[i]
    D = lambda i, j: X(i, j)**2+2*ky[i, j]*G(i, j)+t*G(i, j)**2
    ea = tuple(physical[A[(i+1) % 4]]-physical[A[i]] for i in range(4))
    eb = tuple(physical[B[(i+1) % 4]]-physical[B[i]] for i in range(4))
    residuals = []
    for i, (ai, aj) in enumerate(zip(A, A[1:]+A[:1])):
        for j, (bi, bj) in enumerate(zip(B, B[1:]+B[:1])):
            stress = s.expand(X(ai, aj)*X(bi, bj)+t*G(ai, aj)*G(bi, bj)
                              -(D(ai, bj)+D(aj, bi)-D(ai, bi)-D(aj, bj))/2)
            assert not stress.has(t)
            residuals.append(stress-ha[i]*hb[j]+ea[i]*eb[j])
    for cap, weights in ((A, ha), (B, hb)):
        residuals.extend(X(i, j)+weight for (i, j), weight
                         in zip(zip(cap, cap[1:]+cap[:1]), weights))
    matrix, rhs = s.linear_eq_to_matrix(residuals, xx[1:]+gamma[1:])
    assert not matrix.free_symbols
    assert matrix.shape == (24, 14) and matrix.rank() == 14
    assert all(s.expand(value) == 0 for value in
               matrix*s.Matrix(list(family_x[1:])+list(family_g[1:]))-rhs)

    H = {0: s.Integer(0), 2: family_g[2], 3: family_g[3]}
    H.update({i: s.Symbol(f'H{i}') for i in FREE})
    intrinsic = {xx[i]: family_x[i] for i in range(1, 8)} | {
        gamma[i]: family_g[i] for i in range(1, 8)}
    cross = []
    for i, j in edges:
        ell = int(j in B)-int(i in B)
        if not ell or (i, j) in ((0, 2), (0, 3)):
            continue
        assert ky[i, j]**2 == s.Rational(1, 4)
        value = ((family_u[j]-family_u[i])**2-X(i, j)**2
                 -ell*(H[j]-H[i])-2*ky[i, j]*G(i, j))
        cross.append(s.expand(value.subs(intrinsic)))
    height_matrix, height_rhs = s.linear_eq_to_matrix(cross, [H[i] for i in FREE])
    assert not height_matrix.free_symbols
    assert height_matrix.shape == (14, 5) and height_matrix.rank() == 5
    assert all(s.expand(value) == 0 for value in
               height_matrix*s.Matrix([family_zeta[i] for i in FREE])-height_rhs)
    axial = s.factor(-2*family_zeta[1]+4*r*family_zeta[5])
    assert s.expand(axial-4*r*(2*r-1)) == 0

    bx, by, eps = s.symbols('bx by eps')
    points = {0: (0, 0, 0), 1: (r, 0, 0), 4: (r+eps*bx, eps*by, 0),
              5: (half, 0, 0), 2: (0, 0, 1), 3: (u, u, 1),
              6: (v, v, 1), 7: (-w, -w, 1)}
    expected = {(0, 1, 2, 4): -r*by,
                (1, 2, 3, 4): -u*(bx-by),
                (1, 2, 4, 7): -w*(bx-by)}
    for quad, value in expected.items():
        assert {1, 4} <= set(quad)
        first, *rest = quad
        determinant = s.Matrix([[points[i][k]-points[first][k] for k in range(3)]
                                for i in rest]).det()
        assert s.expand(determinant-eps*value) == 0
    ax, ay, az, bz = s.symbols('ax ay az bz')
    same_cap = s.Matrix([[ax, ay, az], [ax+bx, ay+by, az+bz], [1, 0, 0]]).det()
    assert s.expand(same_cap-ay*bz+az*by) == 0
    print('PASS necessary intrinsic and height limits: ranks 14 and 5')
    print('PASS factored direction brackets and moving height/t =', axial)
    print('PASS same-cap bracket/(t*beta) limit =', axial/u)


def main():
    if not __debug__:
        raise RuntimeError('run with assertions enabled')
    if len(sys.argv) > 2:
        raise SystemExit(__doc__)
    symmetries = compiler.marked_symmetries()
    variables, clauses, *_ = compiler.base_formula()
    models = compiler.enumerate_models(variables, clauses, symmetries)
    _, zeros = two_line.check(models)
    one = [row for row in zeros if len(row['zero_a_edges'])+len(row['zero_b_edges']) == 1]
    assert len(one) == 16
    canonical_maps(one, symmetries)
    print('PASS all 16 two-line orders with exactly one zero weight are canonical')
    proof_n, proof_c = sign_certificate()
    print(f'PASS necessary signs: UNSAT; {proof_n} variables, {len(proof_c)} clauses')
    paired = []
    phase = [entry['permutation'] for entry in symmetries if entry['phase_preserving']]
    for row in zeros:
        if len(row['zero_a_edges']) != 1 or len(row['zero_b_edges']) != 1:
            continue
        values = dict(zip(A, row['a'])) | dict(zip(B, row['b']))
        if any((rank_tuple([reflection*values[p[i]] for i in A]),
                rank_tuple([reflection*values[p[i]] for i in B]))
               == ((0, 1, 1, 2), (1, 2, 2, 0))
               for p, reflection in product(phase, (-1, 1))):
            paired.append(row)
    assert len(paired) == 32
    canonical_maps(paired, symmetries, (1, 2, 2, 0))
    pair_n, pair_c = sign_certificate((1, 2, 2, 0))
    print(f'PASS 32 paired-zero orders and their required signs: UNSAT; {len(pair_c)} clauses')
    exact_checks()
    if len(sys.argv) == 2:
        output = Path(sys.argv[1])
        output.mkdir(parents=True, exist_ok=True)
        compiler.write_cnf(output/'two_line_required_signs.cnf', proof_n, proof_c)
        compiler.write_cnf(output/'two_line_pair36_required_signs.cnf', pair_n, pair_c)
        blocked = clauses+[[-(i+1)*value for i, value in enumerate(model)] for model in models]
        compiler.write_cnf(output/'two_line_model_coverage.cnf', variables, blocked)
        (output/'two_line_one_zero_cells.json').write_text(json.dumps(one, indent=2)+'\n')
        (output/'two_line_pair36_cells.json').write_text(json.dumps(paired, indent=2)+'\n')
    print('Scope: all one-zero orders and 32 paired-zero orders; other multiple-zero patterns remain open.')


if __name__ == '__main__':
    main()
