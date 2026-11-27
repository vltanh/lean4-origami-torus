#!/usr/bin/env python3
"""Exact checks when the unique zero weight belongs to the noncollinear cap.

Usage: python remaining_partner_blowup.py [OUTPUT_DIRECTORY]

The 32 mixed blow-up cells split into sixteen collapsed horizontal bases
and sixteen collapsed sloping legs.  A signed length defect regularizes
the metric equation at the collapsed edge.  The proof, including every
relative rate, is in remaining_partner_blowup.md.
"""

from collections import Counter
from itertools import combinations, product
import json
from pathlib import Path
import sys

import sympy as s

import remaining_flat_blowup as flat
import remaining_one_collinear as cover
from direct_metric import load_data
from solver_chambers import base_formula, enumerate_models, marked_symmetries
from verify_linking import SAT, lit

A, B, FREE = cover.A, cover.B, flat.FREE
FARKAS_SIGNS = flat.REQUIRED
BASE_DIRECTION_SIGNS = (lit((0, 1, 6, 7)), -lit((0, 4, 6, 7)), lit((0, 2, 6, 7)))


def canonical_maps(rows, symmetries):
    permutations = [entry['permutation'] for entry in symmetries
                    if {entry['permutation'][i] for i in A} == set(A)]
    counts = Counter()
    for row in rows:
        maps = []
        for permutation, sx, sy in product(permutations, (-1, 1), (-1, 1)):
            ai = [A.index(permutation[i]) for i in A]
            bi = [B.index(permutation[i]) for i in B]
            a = flat.rank_tuple([sx*row['a'][i] for i in ai])
            x = flat.rank_tuple([sx*row['x'][i] for i in bi])
            y = flat.rank_tuple([sy*row['y'][i] for i in bi])
            beta = []
            for triple in cover.TRIPLES:
                mapped = [bi[i] for i in triple]
                parity = (-1)**sum(mapped[i] > mapped[j] for i, j in combinations(range(3), 2))
                beta.append(sx*sy*parity*row['beta'][cover.TRIPLES.index(tuple(sorted(mapped)))])
            if a != (0, 1, 2, 1) or y != (0, 0, 1, 1):
                continue
            kind = None
            if x == (0, 1, 2, 2) and beta == [1, 1, 0, 0]:
                kind = 'base67'
            if x == (0, 2, 2, 1) and beta == [1, 1, 1, 1]:
                kind = 'leg36'
            if kind:
                maps.append({'kind': kind, 'permutation': permutation,
                             'horizontal_reflection': sx, 'normal_reflection': sy})
        assert maps, row
        row['canonical_map'] = maps[0]
        counts[maps[0]['kind']] += 1
    assert counts == Counter(base67=16, leg36=16)


def sign_certificate(kind):
    variables, original, *_ = base_formula()
    assert original[0] == [1]
    clauses = [list(row) for row in original[1:]]
    a, y = (0, 1, 2, 1), (0, 0, 1, 1)
    beta = (1, 1, 0, 0) if kind == 'base67' else (1, 1, 1, 1)
    required = FARKAS_SIGNS+(BASE_DIRECTION_SIGNS if kind == 'base67' else ())
    for i, j in cover.PAIRS:
        for k, l in cover.PAIRS:
            value = -cover.pair_sign(a, i, j)*cover.pair_sign(y, k, l)
            if value:
                clauses.append([value*lit((A[i], A[j], B[k], B[l]))])
    for triple, value in zip(cover.TRIPLES, beta):
        if value:
            for vertex in A:
                clauses.append([-value*lit(tuple(B[i] for i in triple)+(vertex,))])
    clauses.append([-literal for literal in required])
    assert SAT(variables, clauses).check() == -1
    return variables, clauses


def symbolic_regularization():
    _, _, edges, _, _, kx, ky = load_data()
    r, u, z, t, mu = s.symbols('r u z t mu')
    half = s.Rational(1, 2)
    xx = [s.Integer(0)]+list(s.symbols('x1:8'))
    gamma = [s.Integer(0)]+list(s.symbols('g1:8'))
    U = {0: s.Integer(0), 2: xx[2], 3: xx[3]}
    H = {0: s.Integer(0), 2: gamma[2], 3: gamma[3]}
    Z = {0: s.Integer(0), 2: s.Integer(0), 3: s.Integer(0)}
    for i in FREE:
        U[i], H[i], Z[i] = s.symbols(f'U{i} H{i} Z{i}')
    variables = xx[1:]+gamma[1:]+[U[i] for i in FREE]+[H[i] for i in FREE]
    dependent = [value for value in variables if value not in (xx[1], xx[3], xx[7])]
    levels = {i: int(i in B) for i in range(8)}
    metric_edges = [edge for edge in edges if edge not in ((0, 2), (0, 3), (2, 3))]
    equations = []
    for i, j in metric_edges:
        du, dz = U[j]-U[i], Z[j]-Z[i]
        dx, dg, dh = xx[j]-xx[i]+kx[i, j], gamma[j]-gamma[i], H[j]-H[i]
        ell = levels[j]-levels[i]
        equations.append(s.expand(du**2+dz**2-dx**2-ell*dh-2*ky[i, j]*dg+t*(dh**2-dg**2)))

    # These are actual positive short weights, so the Farkas weights
    # remain nonnegative when u approaches 1/2 from the necessary side.
    parameters = {xx[1]: -r, xx[3]: xx[2]-u, xx[7]: xx[2]+z-half}
    assert s.expand(-(xx[3]-xx[2]+kx[2, 3])).subs(parameters) == u
    assert s.expand(-(xx[2]-xx[7]+kx[7, 2])).subs(parameters) == z
    P = (0, r, 0, u, half, r, half, z)
    family_x = (0, -r, 0, -u, 0, r-half, 0, z-half)
    slope, g2 = half-2*r, r-s.Rational(1, 8)
    family_g = (0, r/2, g2, g2+slope*u, r-s.Rational(1, 4), r/2,
                g2+slope/2, g2+slope*z)
    family = ({xx[i]: family_x[i] for i in range(1, 8)}
              | {gamma[i]: family_g[i] for i in range(1, 8)}
              | {U[i]: -P[i] for i in FREE}
              | {H[i]: family_g[i] for i in FREE}
              | {Z[i]: 0 for i in FREE})
    assert all(s.expand(equation.subs(family)) == 0 for equation in equations)

    points = {i: (-U[i], Z[i], levels[i]-2*t*H[i]) for i in range(8)}
    quads = tuple(combinations(range(8), 4))
    forms = []
    for literal in FARKAS_SIGNS:
        first, *rest = quads[abs(literal)-1]
        forms.append(cover.sign(literal)*s.Matrix(
            [[points[i][k]-points[first][k] for k in range(3)] for i in rest]).det())
    mode = {Z[i]: int(i in (6, 7)) for i in FREE}
    # At the unit normal profile, the t=0 Farkas functional is exactly
    # P5-P1=U1-U5, before imposing any metric equation.
    zero_weights = (1-2*u, 2*u, 1, 1)
    assert s.expand(sum(weight*form for weight, form in zip(zero_weights, forms))
                    .subs(t, 0).subs(mode)-U[1]+U[5]) == 0

    output = {}
    cases = (
        ('leg36', (3, 6), -1, {u: half},
         16384*r**2*z*(2*r-1)**2*(2*z-1), -r, -(half-r)/(2*z)),
        ('base67', (6, 7), 1, {z: half},
         8192*r**2*(2*r-1)**2*(2*u-1), r, -r/(1-2*u)-(half-r)),
    )
    for kind, edge, direction, boundary, expected_det, expected_mu, expected_cubic in cases:
        i, j = edge
        index = metric_edges.index(edge)
        weight = -(xx[j]-xx[i]+kx[i, j])
        defect = weight-direction*(U[j]-U[i])-mu
        modified = list(equations)
        modified[index] = defect
        modified = [equation.subs(parameters) for equation in modified]
        assert all(s.expand(equation.subs(family).subs(mu, 0)) == 0 for equation in modified)
        jacobian = s.Matrix(modified).jacobian(dependent).subs(family).subs({t: 0, mu: 0}).subs(boundary)
        determinant = s.factor(jacobian.det(method='domain-ge'))
        assert s.expand(determinant-expected_det) == 0
        inverse = jacobian.inv(method='DM')
        defect_forcing = s.zeros(21, 1)
        defect_forcing[index] = 1
        linear = inverse*defect_forcing
        mu_coefficient = s.factor(linear[dependent.index(U[1])]-linear[dependent.index(U[5])])
        assert s.simplify(mu_coefficient-expected_mu) == 0
        normal_forcing = s.Matrix([
            (Z[b]-Z[a])**2 if k != index else 0 for k, (a, b) in enumerate(metric_edges)
        ]).subs(mode)
        quadratic = inverse*(-normal_forcing)
        cubic = s.factor(quadratic[dependent.index(U[1])]-quadratic[dependent.index(U[5])])
        assert s.simplify(cubic-expected_cubic) == 0
        print(f'PASS {kind}: determinant {determinant}; defect {mu_coefficient}; cubic {expected_cubic}', flush=True)
        output[kind] = {'determinant': str(determinant), 'defect_coefficient': str(mu_coefficient),
                        'cubic_coefficient': str(expected_cubic)}

    # The collapsed base's virtual direction is forced horizontal and
    # negative.  All three determinants factor the actual edge 67.
    bx, by, eps = s.symbols('bx by eps')
    limiting = {0: (0, 0, 0), 1: (r, 0, 0), 4: (half, 0, 0), 5: (r, 0, 0),
                2: (0, 0, 1), 3: (u, 0, 1), 6: (half, 1, 1),
                7: (half+eps*bx, 1+eps*by, 1)}
    for quad, expected in (((0, 1, 6, 7), -r*by),
                           ((0, 4, 6, 7), -by/2),
                           ((0, 2, 6, 7), -bx+by/2)):
        assert {6, 7} <= set(quad)
        first, *rest = quad
        determinant = s.Matrix([[limiting[i][k]-limiting[first][k] for k in range(3)] for i in rest]).det()
        assert s.expand(determinant-eps*expected) == 0
    print('PASS three exact edge-67 direction factors and signed-length definitions', flush=True)
    return output


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
    cells, _ = flat.degenerate_cover(models)
    one = [row for row in cells if all(row['a'][i] != row['a'][(i+1) % 4] for i in range(4))
           and sum(row['x'][i] == row['x'][(i+1) % 4] for i in range(4)) == 1]
    assert len(one) == 32
    canonical_maps(one, symmetries)
    print('PASS all 32 partner-collapse cells: 16 horizontal bases and 16 sloping legs', flush=True)
    certificates = {}
    for kind in ('base67', 'leg36'):
        proof_n, proof_c = sign_certificate(kind)
        certificates[kind] = (proof_n, proof_c)
        print(f'PASS {kind} required signs: UNSAT; {proof_n} variables, {len(proof_c)} clauses', flush=True)
    # These necessity checks are valid at the endpoint parameters too:
    # the stress and height coefficient matrices have constant rank.
    flat.symbolic_metric()
    identities = symbolic_regularization()
    if output:
        coverage = clauses+[[-(i+1)*value for i, value in enumerate(model)] for model in models]
        cover.write_cnf(output/'partner_blowup_model_coverage.cnf', variables, coverage)
        for kind, (proof_n, proof_c) in certificates.items():
            cover.write_cnf(output/f'partner_{kind}_required_signs.cnf', proof_n, proof_c)
        (output/'partner_blowup_cells.json').write_text(json.dumps({
            'cells': one, 'identities': identities,
        }, indent=2)+'\n')
    print('Scope: exactly one zero weight in the noncollinear blown-up cap; multiple-zero cases remain open.')


if __name__ == '__main__':
    main()
