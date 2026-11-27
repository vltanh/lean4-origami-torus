#!/usr/bin/env python3
"""Exclude the remaining 16 two-line blow-up orders with one zero per cap.

Usage: python exhaustive_two_single_blowup.py [OUTPUT_DIRECTORY]

Only the collapsed edge 67 needs its own normalized direction.  Its
forced direction and the forced sign of 2367 contradict an exact metric
cap determinant.  No edge-length or width/height comparison is assumed.
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
from verify_nonparallel_corner import allowed_sum

A, B = collinear.A, collinear.B
FREE = (1, 4, 5, 6, 7)


def canonical_maps(rows, symmetries):
    phase = [entry['permutation'] for entry in symmetries if entry['phase_preserving']]
    selected, other = [], []
    for row in rows:
        values = dict(zip(A, row['a'])) | dict(zip(B, row['b']))
        maps = []
        for permutation, reflection in product(phase, (-1, 1)):
            a = rank_tuple([reflection*values[permutation[i]] for i in A])
            b = rank_tuple([reflection*values[permutation[i]] for i in B])
            if (a, b) == ((0, 1, 1, 2), (2, 0, 1, 1)):
                maps.append({'permutation': permutation, 'horizontal_reflection': reflection})
        if maps:
            selected.append(dict(row, canonical_map=maps[0]))
        else:
            other.append(row)
    assert len(selected) == 16 and len(other) == 32
    return selected, other


def fixed_sign(polynomial, r, u):
    """Exact sign on the whole open rectangle, not a sampled sign."""
    coefficient, factors = s.factor_list(polynomial)
    answer = int(s.sign(coefficient))
    signs = {r: 1, u: 1, 2*r-1: -1, 2*u-1: -1}
    for factor, exponent in factors:
        assert factor in signs, (polynomial, factor)
        answer *= signs[factor]**exponent
    assert answer in (-1, 1)
    return answer


def sign_certificate():
    variables, original, *_ = compiler.base_formula()
    assert original[0] == [1]
    clauses = [list(row) for row in original[1:]]
    trits = {key: (variables+2*i+1, variables+2*i+2)
             for i, key in enumerate(('dx', 'dy', 'dF'))}
    variables += 6
    clauses.extend([[-positive, -negative] for positive, negative in trits.values()])
    clauses.append(list(trits['dx'])+list(trits['dy']))

    def deny(key, value):
        positive, negative = trits[key]
        return [-positive] if value == 1 else [-negative] if value == -1 else [positive, negative]

    # dF+dy=dx.  These are necessary ternary signs of actual real numbers.
    clauses.extend(deny('dF', a)+deny('dy', b)+deny('dx', total)
                   for a, b, total in product((-1, 0, 1), repeat=3)
                   if not allowed_sum(a, b, total))
    r, u, eps, dx, dy = s.symbols('r u eps dx dy')
    half = s.Rational(1, 2)
    points = {0: (0, 0, 0), 1: (r, 0, 0), 4: (r, 0, 0), 5: (half, 0, 0),
              2: (0, 0, 1), 3: (-half, -half, 1), 6: (-u, -u, 1),
              7: (-u+eps*dx, -u+eps*dy, 1)}
    forms = {'dx': dx, 'dy': dy, 'dF': dx-dy}
    constants, links = [], []
    for index, quad in enumerate(compiler.Q, 1):
        first, *rest = quad
        polynomial = s.expand(s.Matrix(
            [[points[i][k]-points[first][k] for k in range(3)] for i in rest]).det())
        constant = polynomial.subs(eps, 0)
        if constant:
            direction = fixed_sign(constant, r, u)
            clauses.append([direction*index])
            constants.append((quad, constant))
        elif {6, 7} <= set(quad):
            linear = polynomial.coeff(eps, 1)
            if not linear:
                continue
            matches = []
            for key, form in forms.items():
                factor = s.cancel(linear/form)
                if not factor.has(dx, dy):
                    matches.append((key, s.factor(factor)))
            assert len(matches) == 1, (quad, linear)
            key, factor = matches[0]
            direction = fixed_sign(factor, r, u)
            positive, negative = trits[key]
            clauses.extend([[-positive, direction*index], [-negative, -direction*index]])
            links.append((quad, key, str(factor)))
    assert len(constants) == 25 and len(links) == 13
    assert SAT(variables, clauses).check() == 1
    # Negation of: dx<0, dy=0, chi2367<0.  The direction is independently
    # normalized, and every linked determinant factors the actual edge 67.
    required = [-trits['dx'][1], *trits['dy'], lit((2, 3, 6, 7))]
    proof = clauses+[required]
    assert SAT(variables, proof).check() == -1
    return variables, proof, links


def exact_checks():
    _, _, edges, _, _, kx, ky = load_data()
    r, u, t = s.symbols('r u t')
    half = s.Rational(1, 2)
    physical = (0, r, 0, -half, r, half, -u, -u)
    ha, hb = (r, 0, half-r, half), (half, half-u, 0, u)
    family_x = (0, -r, half-u, -u, half-r, 0, 0, 0)
    family_g = (0, r/2, s.Rational(1, 8)-u/2, s.Rational(3, 8)-u/2,
                r/2, s.Rational(1, 4), s.Rational(1, 8), s.Rational(1, 8))
    family_zeta = (0, r/2-4*r*u, family_g[2], family_g[3], r/2-4*r*u,
                   s.Rational(1, 4)-2*u, 4*u**2-2*u+s.Rational(1, 8),
                   4*u**2-2*u+s.Rational(1, 8))
    family_u = tuple(physical[i]+(family_x[2] if i in B else 0) for i in range(8))
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
        value = ((family_u[j]-family_u[i])**2-X(i, j)**2
                 -ell*(H[j]-H[i])-2*ky[i, j]*G(i, j))
        cross.append(s.expand(value.subs(intrinsic)))
    height_matrix, height_rhs = s.linear_eq_to_matrix(cross, [H[i] for i in FREE])
    assert height_matrix.shape == (14, 5) and height_matrix.rank() == 5
    assert all(s.expand(value) == 0 for value in
               height_matrix*s.Matrix([family_zeta[i] for i in FREE])-height_rhs)

    h, gamma23, U62, Z6, H62, dU, dZ, dH = s.symbols('h gamma23 U62 Z6 H62 dU dZ dH')
    determinant = s.Matrix([[-h, 0, -2*t*gamma23], [U62, Z6, -2*t*H62],
                            [dU, dZ, -2*t*dH]]).det()
    expected = 2*t*(Z6*(h*dH+gamma23*dU)-dZ*(h*H62+gamma23*U62))
    assert s.expand(determinant-expected) == 0
    coefficient = s.factor(half*(family_zeta[6]-family_g[2])
                           +(family_g[3]-family_g[2])*(family_u[6]-family_u[2]))
    assert s.expand(coefficient+u*(1-2*u)) == 0
    # The exact shear/scaling used in the proof has positive determinant.
    delta, H2, q = s.symbols('delta H2 q')
    transformation = s.Matrix([[1, 0, -q], [1, 1/delta, -q], [0, 0, 1/H2]])
    assert transformation.det() == 1/(H2*delta)
    print('PASS necessary intrinsic and height limits: ranks 14 and 5')
    print('PASS exact [2367] identity; coefficient =', coefficient)
    print('PASS positive coordinate change determinant = 1/(H2*delta)')


def main():
    if not __debug__:
        raise RuntimeError('run with assertions enabled')
    if len(sys.argv) > 2:
        raise SystemExit(__doc__)
    symmetries = compiler.marked_symmetries()
    variables, clauses, *_ = compiler.base_formula()
    models = compiler.enumerate_models(variables, clauses, symmetries)
    _, zeros = two_line.check(models)
    double = [row for row in zeros if len(row['zero_a_edges']) == len(row['zero_b_edges']) == 1]
    assert len(double) == 48
    selected, other = canonical_maps(double, symmetries)
    print('PASS all 16 selected two-line double-single orders have checked canonical maps')
    proof_n, proof_c, links = sign_certificate()
    print(f'PASS virtual67 direction and negative cap: UNSAT; {proof_n} variables, {len(proof_c)} clauses')
    exact_checks()
    if len(sys.argv) == 2:
        output = Path(sys.argv[1])
        output.mkdir(parents=True, exist_ok=True)
        compiler.write_cnf(output/'two_single_virtual67.cnf', proof_n, proof_c)
        coverage = clauses+[[-(i+1)*value for i, value in enumerate(model)] for model in models]
        compiler.write_cnf(output/'two_single_model_coverage.cnf', variables, coverage)
        (output/'two_single_cells.json').write_text(json.dumps({
            'excluded_cells': selected, 'other_one_zero_each_cells': other,
            'factored_edge67_links': links,
        }, indent=2)+'\n')
    print('Scope: the selected 16 two-line orders; this is an asymptotic, not fixed-height, exclusion.')


if __name__ == '__main__':
    main()
