#!/usr/bin/env python3
"""Exclude the 16 mixed three-zero cells with one adjacent A collision.

Usage: python remaining_three_adjacent_blowup.py [OUTPUT_DIRECTORY]

Two necessary cap signs and a regular three-defect metric chart give
the scale-independent contradiction in remaining_three_adjacent_blowup.md.
"""

from itertools import combinations, product
import json
from pathlib import Path
import sys

import sympy as s

import remaining_adjacent_blowup as adjacent
import remaining_cluster_blowup as cluster
import remaining_flat_blowup as flat
import remaining_one_collinear as cover
import solver_chambers as compiler
from verify_linking import SAT, lit

A, B, FREE = cover.A, cover.B, flat.FREE


def canonical_maps(rows, symmetries):
    permutations = [entry['permutation'] for entry in symmetries
                    if {entry['permutation'][i] for i in A} == set(A)]
    assert all(entry['phase_preserving'] for entry in symmetries
               if entry['permutation'] in permutations)
    for row in rows:
        maps = []
        for permutation, sx, sy in product(permutations, (-1, 1), (-1, 1)):
            transformed = cluster.transform(row, permutation, sx, sy)
            if cluster.cell_key(transformed) == (
                    (0, 1, 1, 2), (1, 0, 1, 1), (0, 0, 0, 1), (0, -1, 0, 1)):
                maps.append({'permutation': permutation, 'horizontal_reflection': sx,
                             'normal_reflection': sy})
        assert maps, row
        row['canonical_map'] = maps[0]


def cap_sign_certificate():
    """After the forced vertical edge14 direction, both caps are negative."""
    n, original, *_ = compiler.base_formula()
    assert original[0] == [1]
    clauses = [list(row) for row in original[1:]]
    r, eps = s.symbols('r eps')
    half = s.Rational(1, 2)
    points = {0: (0, 0, 0), 1: (r, 0, 0), 4: (r, eps, 0), 5: (half, 0, 0),
              2: (0, 0, 1), 3: (-half, 0, 1), 6: (0, 0, 1), 7: (0, 1, 1)}
    records = []
    for quad in compiler.Q:
        first, *rest = quad
        determinant = s.expand(s.Matrix([
            [points[i][k]-points[first][k] for k in range(3)] for i in rest]).det())
        factor = eps if {1, 4} <= set(quad) else s.Integer(1)
        quotient = s.cancel(determinant/factor)
        assert not s.denom(quotient).has(eps)
        leading = s.expand(quotient.subs(eps, 0))
        if not leading:
            continue
        assert s.Poly(leading, r).degree() <= 1
        endpoints = [leading.subs(r, value) for value in (0, half)]
        assert all(value >= 0 for value in endpoints) or all(value <= 0 for value in endpoints)
        direction = 1 if any(value > 0 for value in endpoints) else -1
        assert any(endpoints)
        clauses.append([direction*lit(quad)])
        records.append({'quad': quad, 'edge14_factored': factor == eps,
                        'leading': str(leading), 'sign': direction})
    assert SAT(n, clauses).check() == 1
    proof = clauses+[[lit((0, 1, 4, 5)), lit((2, 3, 6, 7))]]
    assert SAT(n, proof).check() == -1
    return n, proof, records


def exact_metric_checks():
    t, x, g, U, H, Z, variables, edges, equations, kx, ky = cluster.metric_system()
    r, b, z = s.symbols('r b z')
    half = s.Rational(1, 2)
    fx = (0, -r, half, 0, half-r, 0, 0, 0)
    fg = (0, r/2, s.Rational(1, 8), s.Rational(3, 8), r/2,
          s.Rational(1, 4), s.Rational(1, 8), s.Rational(1, 8))
    fu = (0, r, half, 0, r, half, half, half)
    family = ({x[i]: fx[i] for i in range(1, 8)}
              | {g[i]: fg[i] for i in range(1, 8)}
              | {U[i]: fu[i] for i in FREE}
              | {H[i]: fg[i] for i in FREE}
              | {Z[i]: 0 for i in FREE})
    assert all(s.expand(eq.subs(family)) == 0 for eq in equations)

    # The existing affine reconstruction matrices are constant, so their
    # full ranks also hold at the chi=1/2 endpoint used here.
    X = lambda i, j: x[j]-x[i]+kx[i, j]
    G = lambda i, j: g[j]-g[i]
    D = lambda i, j: X(i, j)**2+2*ky[i, j]*G(i, j)+t*G(i, j)**2
    physical = (0, r, 0, -half, r, half, 0, 0)
    weights = ((r, 0, half-r, half), (half, half, 0, 0))
    steps = [cover.edge_differences(tuple(physical[i] for i in cap)) for cap in (A, B)]
    residuals = []
    for i, (a, aa) in enumerate(zip(A, A[1:]+A[:1])):
        for j, (c, cc) in enumerate(zip(B, B[1:]+B[:1])):
            stress = s.expand(X(a, aa)*X(c, cc)+t*G(a, aa)*G(c, cc)
                              -(D(a, cc)+D(aa, c)-D(a, c)-D(aa, cc))/2)
            assert not stress.has(t)
            residuals.append(stress-weights[0][i]*weights[1][j]+steps[0][i]*steps[1][j])
    for cap, hs in zip((A, B), weights):
        residuals.extend(X(i, j)+h for (i, j), h in zip(zip(cap, cap[1:]+cap[:1]), hs))
    matrix, rhs = s.linear_eq_to_matrix(residuals, x[1:]+g[1:])
    assert not matrix.free_symbols and matrix.rank() == 14
    assert all(s.expand(value) == 0 for value in matrix*s.Matrix(fx[1:]+fg[1:])-rhs)
    cross = [eq for (i, j), eq in zip(edges, equations) if (i in B) != (j in B)]
    free_heights = [H[i] for i in FREE]
    planar_family = {key: value for key, value in family.items() if key not in free_heights}
    height_matrix, height_rhs = s.linear_eq_to_matrix(
        [s.expand(eq.subs(t, 0).subs(planar_family)) for eq in cross], [H[i] for i in FREE])
    assert not height_matrix.free_symbols and height_matrix.rank() == 5
    assert all(s.expand(value) == 0 for value in
               height_matrix*s.Matrix([fg[i] for i in FREE])-height_rhs)

    h14, h67, h72 = -X(1, 4), -X(6, 7), -X(7, 2)
    defects = (h14-U[4]+U[1], h67-U[7]+U[6], h72+U[7]-U[2])
    indices = [edges.index(edge) for edge in ((1, 4), (6, 7), (2, 7))]
    modified = list(equations)
    for index, defect in zip(indices, defects):
        modified[index] = defect
    parameters = {x[1]: -r, x[4]: half-r-b, x[7]: x[2]+z-half}
    dependent = [v for v in variables if v not in (x[1], x[4], x[7])]
    modified = [eq.subs(parameters) for eq in modified]
    base = family | {t: 0, b: 0, z: 0}
    jacobian = s.Matrix(modified).jacobian(dependent).subs(base)
    determinant = s.factor(jacobian.det(method='domain-ge'))
    assert s.expand(determinant-4096*r*(2*r-1)) == 0
    inverse = jacobian.inv(method='DM')
    targets = (H[1]-U[1]/2, H[5]-U[5]/2, h67.subs(parameters),
               U[6]-x[2], H[6]-g[2])
    gradients = [s.Matrix([target]).jacobian(dependent) for target in targets]
    expected = {
        'mu14': (-2*r, 0, 0, 0, 0),
        'mu67': (-2*r*(2*r-1), 0, half, half, -(8*r-3)/4),
        'mu72': (2*r, (2*r+1)/2, -(2*r-1)/2, (2*r+1)/2, -(2*r-3)/4),
        'b': (0, 0, 0, 0, 0),
        'z': (-4*r, -2, 0, -1, -s.Rational(3, 2)),
    }
    actual = {}
    for name, index in zip(('mu14', 'mu67', 'mu72'), indices):
        forcing = s.zeros(21, 1)
        forcing[index] = 1
        jet = inverse*forcing
        actual[name] = tuple(s.factor((gradient*jet)[0]) for gradient in gradients)
    for name, parameter in (('b', b), ('z', z)):
        jet = -inverse*s.Matrix(modified).diff(parameter).subs(base)
        actual[name] = tuple(s.factor((gradient*jet)[0]+s.diff(target, parameter).subs(base))
                             for target, gradient in zip(targets, gradients))
    for name in expected:
        assert all(s.simplify(a-e) == 0 for a, e in zip(actual[name], expected[name]))

    # Factoring the actual edge14 leaves only edge-relative error terms.
    u1, u5, z1, z5, du, dz, th1, th5, dth = s.symbols('u1 u5 z1 z5 du dz th1 th5 dth')
    raw = -2*t*s.Matrix([[u1, z1, th1+u1/2], [du, dz, dth+du/2],
                         [u5, z5, th5+u5/2]]).det()
    cap = 2*t*(dz*(u5*th1-u1*th5)+z5*(u1*dth-th1*du)+z1*(du*th5-u5*dth))
    assert s.expand(raw-cap) == 0
    for name, expected_coefficient in (('mu67', r*(1-2*r)), ('mu72', r*(1-2*r)/2)):
        assert s.simplify(half*actual[name][0]-r*actual[name][1]-expected_coefficient) == 0
    assert half*(-s.Rational(3, 2))+s.Rational(1, 4)*(-1) == -1
    print('PASS exact all-t corner family and constant necessity ranks 14/5', flush=True)
    print('PASS three-defect Jacobian determinant', determinant, flush=True)
    print('PASS all first derivatives; positive A-cap coefficients and final B-cap coefficient +1', flush=True)
    return {name: list(map(str, values)) for name, values in actual.items()}


def main():
    if not __debug__:
        raise RuntimeError('run with assertions enabled')
    if len(sys.argv) > 2:
        raise SystemExit(__doc__)
    symmetries = compiler.marked_symmetries()
    variables, clauses, *_ = compiler.base_formula()
    models = compiler.enumerate_models(variables, clauses, symmetries)
    all_cells, _ = flat.degenerate_cover(models)
    rows = [row for row in all_cells if len(adjacent.zero_edges(row, 'a')) == 1
            and len(adjacent.zero_edges(row, 'x')) == 2]
    assert len(rows) == 16
    canonical_maps(rows, symmetries)
    first_n, first_c = adjacent.sign_certificate()
    second_n, second_c, records = cap_sign_certificate()
    coefficients = exact_metric_checks()
    if len(sys.argv) == 2:
        output = Path(sys.argv[1])
        output.mkdir(parents=True, exist_ok=True)
        compiler.write_cnf(output/'three_adjacent_required_signs.cnf', first_n, first_c)
        compiler.write_cnf(output/'three_adjacent_negative_caps.cnf', second_n, second_c)
        coverage = clauses+[[-(i+1)*value for i, value in enumerate(model)] for model in models]
        compiler.write_cnf(output/'three_adjacent_model_coverage.cnf', variables, coverage)
        (output/'three_adjacent_cells.json').write_text(json.dumps({
            'cells': rows, 'direction_links': records, 'derivatives': coefficients,
        }, indent=2)+'\n')
    print('PASS all 16 adjacent-A/two-zero-B mixed orders; both cap-sign implications UNSAT')
    print('Scope: the 16 asymptotic cells only; no fixed-height or Lean exclusion.')


if __name__ == '__main__':
    main()
