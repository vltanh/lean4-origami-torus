#!/usr/bin/env python3
"""Exact checks for two zero weights in the noncollinear blown-up cap.

Usage: python remaining_double_partner_blowup.py [OUTPUT_DIRECTORY]

All four weights in the collinear cap remain positive. The 24 cells
split into sixteen adjacent and eight opposite collapsed-edge cases.
The uniform two-defect proof is in remaining_double_partner_blowup.md.
"""

from collections import Counter
from itertools import combinations, product
import json
from pathlib import Path
import sys

import sympy as s

import remaining_flat_blowup as flat
import remaining_one_collinear as cover
import remaining_partner_blowup as partner
from direct_metric import load_data
from solver_chambers import base_formula, enumerate_models, marked_symmetries

A, B, FREE = cover.A, cover.B, flat.FREE


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
            if x == (0, 1, 1, 1) and beta == [1, 1, 0, 0]:
                kind = 'adjacent36_67'
            if x == (0, 1, 1, 0) and beta == [1, 1, 1, 1]:
                kind = 'opposite36_72'
            if kind:
                maps.append({'kind': kind, 'permutation': permutation,
                             'horizontal_reflection': sx, 'normal_reflection': sy})
        assert maps, row
        row['canonical_map'] = maps[0]
        counts[maps[0]['kind']] += 1
    assert counts == Counter(adjacent36_67=16, opposite36_72=8), counts


def symbolic_regularization():
    _, _, edges, _, _, kx, ky = load_data()
    r, u, z, t = s.symbols('r u z t')
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
    parameters = {xx[1]: -r, xx[3]: xx[2]-u, xx[7]: xx[2]+z-half}
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
    mode = {Z[i]: int(i in (6, 7)) for i in FREE}
    expected_determinant = 8192*r**2*(2*r-1)**2
    cases = (
        ('adjacent36_67', ((3, 6, -1), (6, 7, 1)), {u: half, z: half}, (-r, r), r-half),
        ('opposite36_72', ((3, 6, -1), (7, 2, 1)), {u: half, z: 0}, (-r, r-half), 0),
    )
    result = {}
    for kind, collapsed, boundary, expected_defects, expected_cubic in cases:
        modified = list(equations)
        indices = []
        for i, j, direction in collapsed:
            index = metric_edges.index(tuple(sorted((i, j))))
            indices.append(index)
            weight = -(xx[j]-xx[i]+kx[i, j])
            modified[index] = weight-direction*(U[j]-U[i])
        modified = [equation.subs(parameters) for equation in modified]
        assert all(s.expand(equation.subs(family)) == 0 for equation in modified)
        jacobian = s.Matrix(modified).jacobian(dependent).subs(family).subs(t, 0).subs(boundary)
        determinant = s.factor(jacobian.det(method='domain-ge'))
        assert s.expand(determinant-expected_determinant) == 0
        inverse = jacobian.inv(method='DM')
        defects = []
        for index, expected in zip(indices, expected_defects):
            forcing = s.zeros(21, 1)
            forcing[index] = 1
            linear = inverse*forcing
            coefficient = s.factor(linear[dependent.index(U[1])]-linear[dependent.index(U[5])])
            assert s.simplify(coefficient-expected) == 0
            defects.append(str(coefficient))
        normal_forcing = s.Matrix([
            0 if index in indices else (Z[j]-Z[i])**2
            for index, (i, j) in enumerate(metric_edges)
        ]).subs(mode)
        quadratic = inverse*(-normal_forcing)
        cubic = s.factor(quadratic[dependent.index(U[1])]-quadratic[dependent.index(U[5])])
        assert s.simplify(cubic-expected_cubic) == 0
        print(f'PASS {kind}: determinant {determinant}; defects {defects}; cubic {cubic}', flush=True)
        result[kind] = {'determinant': str(determinant), 'defect_coefficients': defects,
                        'cubic_coefficient': str(cubic)}
    return result


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
    selected = [row for row in cells if all(row['a'][i] != row['a'][(i+1) % 4] for i in range(4))
                and sum(row['x'][i] == row['x'][(i+1) % 4] for i in range(4)) == 2]
    assert len(selected) == 24
    canonical_maps(selected, symmetries)
    print('PASS all 24 double-partner cells: 16 adjacent and 8 opposite collapsed pairs', flush=True)
    certificates = {}
    for kind, source in (('adjacent36_67', 'base67'), ('opposite36_72', 'leg36')):
        # The macro horizontal/vertical orders and nonzero B triangle
        # signs are exactly those in the existing one-edge certificate.
        proof_n, proof_c = partner.sign_certificate(source)
        certificates[kind] = (proof_n, proof_c)
        print(f'PASS {kind} required signs: UNSAT; {proof_n} variables, {len(proof_c)} clauses', flush=True)
    flat.symbolic_metric()
    identities = symbolic_regularization()
    if output:
        coverage = clauses+[[-(i+1)*value for i, value in enumerate(model)] for model in models]
        cover.write_cnf(output/'double_partner_model_coverage.cnf', variables, coverage)
        for kind, (proof_n, proof_c) in certificates.items():
            cover.write_cnf(output/f'double_partner_{kind}_required_signs.cnf', proof_n, proof_c)
        (output/'double_partner_cells.json').write_text(json.dumps({
            'cells': selected, 'identities': identities,
        }, indent=2)+'\n')
    print('Scope: positive weights in the collinear cap and exactly two zero partner weights.')


if __name__ == '__main__':
    main()
