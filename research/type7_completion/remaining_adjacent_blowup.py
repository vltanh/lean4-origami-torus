#!/usr/bin/env python3
"""Exact checks for a mixed blow-up with one collapsed adjacent A edge.

Usage: python remaining_adjacent_blowup.py [OUTPUT_DIRECTORY]

The theorem in remaining_adjacent_blowup.md covers 48 cells: exactly one
zero A weight and no zero B weight.  The other 16 adjacent-pair cells
have two zero B weights and are explicitly retained as boundary cases.
No comparison of the collapsed edge length and normal width is assumed.
"""

from itertools import combinations, product
import json
from pathlib import Path
import sys

import sympy as s

import remaining_one_collinear as cover
from remaining_flat_blowup import degenerate_cover, rank_tuple
from direct_metric import load_data
from solver_chambers import base_formula, enumerate_models, marked_symmetries
from verify_linking import SAT, lit

A, B = cover.A, cover.B
REQUIRED = (-lit((0, 1, 2, 4)), lit((1, 2, 4, 7)),
            lit((1, 4, 6, 7)), -lit((0, 1, 4, 5)))
FREE = (1, 4, 5, 6, 7)


def zero_edges(row, key):
    return tuple(i for i in range(4) if row[key][i] == row[key][(i+1) % 4])


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
            if (a == (0, 1, 1, 2) and y == (0, 0, 0, 1) and beta == [0, -1, 0, 1]
                    and x[0] == x[2] == max(x) and x[1] < max(x) and x[3] < max(x)):
                maps.append({'permutation': permutation, 'horizontal_reflection': sx,
                             'normal_reflection': sy})
        assert maps, row
        row['canonical_map'] = maps[0]


def sign_certificate():
    variables, original, *_ = base_formula()
    assert original[0] == [1]
    clauses = [list(row) for row in original[1:]]
    a, y, beta = (0, 1, 1, 2), (0, 0, 0, 1), (0, -1, 0, 1)
    for i, j in cover.PAIRS:
        for k, l in cover.PAIRS:
            value = -cover.pair_sign(a, i, j)*cover.pair_sign(y, k, l)
            if value:
                clauses.append([value*lit((A[i], A[j], B[k], B[l]))])
    for triple, value in zip(cover.TRIPLES, beta):
        if value:
            for vertex in A:
                clauses.append([-value*lit(tuple(B[i] for i in triple)+(vertex,))])
    clauses.append([-literal for literal in REQUIRED])
    assert SAT(variables, clauses).check() == -1
    return variables, clauses


def exact_checks():
    _, _, edges, _, _, kx, ky = load_data()
    r, chi, t = s.symbols('r chi t')
    half = s.Rational(1, 2)
    sigma = half-chi
    base_x = 2*chi*r+chi-r
    base_g = -chi*r+chi/2+r/2-s.Rational(1, 8)
    family_x = (0, -r, base_x, base_x-chi, half-r, 0, base_x+half-2*chi, base_x-chi)
    family_g = (0, r/2, base_g, base_g+chi/2, r/2, s.Rational(1, 4), base_g, base_g+sigma/2)
    physical_x = (0, r, 0, -chi, r, half, 0, -sigma)
    family_u = tuple(physical_x[i]+(base_x if i in B else 0) for i in range(8))
    family_h = (0, r/2-8*r*r*sigma, base_g, base_g+chi/2,
                r/2-8*r*r*sigma, s.Rational(1, 4)-2*sigma,
                base_g-8*chi*r*sigma, base_g+sigma/2+8*r*sigma*sigma-4*chi*sigma)
    xx = [s.Integer(0)]+list(s.symbols('x1:8'))
    gamma = [s.Integer(0)]+list(s.symbols('g1:8'))
    X = lambda i, j: xx[j]-xx[i]+kx[i, j]
    G = lambda i, j: gamma[j]-gamma[i]
    D = lambda i, j: X(i, j)**2+2*ky[i, j]*G(i, j)+t*G(i, j)**2
    ha = (r, 0, half-r, half)
    hb = (chi, chi, sigma, sigma)
    ea, eb = cover.edge_differences(tuple(physical_x[i] for i in A)), cover.edge_differences(tuple(physical_x[i] for i in B))
    residuals = []
    for i, (ai, aj) in enumerate(zip(A, A[1:]+A[:1])):
        for j, (bi, bj) in enumerate(zip(B, B[1:]+B[:1])):
            stress = s.expand(X(ai, aj)*X(bi, bj)+t*G(ai, aj)*G(bi, bj)
                              -(D(ai, bj)+D(aj, bi)-D(ai, bi)-D(aj, bj))/2)
            assert not stress.has(t)
            residuals.append(stress-ha[i]*hb[j]+ea[i]*eb[j])
    for cap, weights in ((A, ha), (B, hb)):
        residuals.extend(X(i, j)+weight for (i, j), weight in zip(zip(cap, cap[1:]+cap[:1]), weights))
    matrix, rhs = s.linear_eq_to_matrix(residuals, xx[1:]+gamma[1:])
    assert matrix.shape == (24, 14) and matrix.rank() == 14
    assert all(s.expand(value) == 0 for value in
               matrix*s.Matrix(list(family_x[1:])+list(family_g[1:]))-rhs)

    # All limiting heights are necessary, not a selected planar branch.
    H = {0: s.Integer(0), 2: family_g[2], 3: family_g[3]}
    H.update({i: s.Symbol(f'H{i}') for i in FREE})
    intrinsic = {xx[i]: family_x[i] for i in range(1, 8)} | {gamma[i]: family_g[i] for i in range(1, 8)}
    cross = []
    for i, j in edges:
        ell = int(j in B)-int(i in B)
        if not ell or (i, j) in ((0, 2), (0, 3)):
            continue
        residual = ((family_u[j]-family_u[i])**2-X(i, j)**2
                    -ell*(H[j]-H[i])-2*ky[i, j]*G(i, j))
        cross.append(s.expand(residual.subs(intrinsic)))
    height_matrix, height_rhs = s.linear_eq_to_matrix(cross, [H[i] for i in FREE])
    assert height_matrix.shape == (14, 5) and height_matrix.rank() == 5
    assert all(s.expand(value) == 0 for value in
               height_matrix*s.Matrix([family_h[i] for i in FREE])-height_rhs)
    axial_limit = s.factor(-2*family_h[1]+4*r*family_h[5])
    assert s.expand(axial_limit+16*r*(half-r)*sigma) == 0
    assert s.simplify(-axial_limit/sigma-16*r*(half-r)) == 0

    # Each direction implication contains the actual edge 14 as an
    # exact determinant factor, so its error is relative to that edge.
    bx, by, eps = s.symbols('bx by eps')
    points = {0: (0, 0, 0), 1: (r, 0, 0), 4: (r+eps*bx, eps*by, 0),
              5: (half, 0, 0), 2: (0, 0, 1), 3: (-chi, 0, 1),
              6: (0, 0, 1), 7: (-sigma, 1, 1)}
    expected = {(0, 1, 2, 4): -r*by,
                (1, 2, 4, 7): bx+sigma*by,
                (1, 4, 6, 7): -bx-sigma*by}
    for quad, value in expected.items():
        assert {1, 4} <= set(quad)
        first, *rest = quad
        determinant = s.Matrix([[points[i][k]-points[first][k] for k in range(3)] for i in rest]).det()
        assert s.expand(determinant-eps*value) == 0
    ax, ay, az, bz = s.symbols('ax ay az bz')
    same_cap = s.Matrix([[ax, ay, az], [ax+bx, ay+by, az+bz], [1, 0, 0]]).det()
    assert s.expand(same_cap-ay*bz+az*by) == 0
    print('PASS unique intrinsic/height limits: ranks 14 and 5', flush=True)
    print('PASS three factored direction brackets; affine height/t =', axial_limit, flush=True)
    print('PASS [0145]/(t*beta) limit =', 16*r*(half-r), flush=True)


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
    cells, _ = degenerate_cover(models)
    adjacent = [row for row in cells if len(zero_edges(row, 'a')) == 1]
    interior = [row for row in adjacent if not zero_edges(row, 'x')]
    boundary = [row for row in adjacent if zero_edges(row, 'x')]
    assert len(adjacent) == 64 and len(interior) == 48 and len(boundary) == 16
    assert all(len(zero_edges(row, 'x')) == 2 for row in boundary)
    canonical_maps(interior, symmetries)
    print('PASS 48 one-zero-edge cells canonical; 16 cells with two extra zero B edges retained', flush=True)
    proof_n, proof_c = sign_certificate()
    print(f'PASS required signs: UNSAT; {proof_n} variables, {len(proof_c)} clauses', flush=True)
    exact_checks()
    if output:
        cover.write_cnf(output/'adjacent_blowup_required_signs.cnf', proof_n, proof_c)
        coverage = clauses+[[-(i+1)*value for i, value in enumerate(model)] for model in models]
        cover.write_cnf(output/'adjacent_blowup_model_coverage.cnf', variables, coverage)
        (output/'adjacent_blowup_cells.json').write_text(json.dumps({
            'excluded_interior': interior, 'open_boundary': boundary,
        }, indent=2)+'\n')
    print('Scope: one collapsed edge in the collinear cap and four positive partner weights; other zero-weight cells remain open.')


if __name__ == '__main__':
    main()
