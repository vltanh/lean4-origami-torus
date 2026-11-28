#!/usr/bin/env python3
"""Exclude 16 split-pair / positive-partner two-line blow-up orders.

The coincident nonedge 26 has a forced second-order displacement.  Its
separately normalized direction contradicts the necessary orientation
formula, without comparing either collapsed edge length to the width.
Usage: python remaining_split_blowup.py [OUTPUT_DIRECTORY]
"""

from itertools import combinations, product
import json
from pathlib import Path
import sys

import sympy as s

import common_line_edge_collapse as two_line
from direct_metric import load_data
from remaining_flat_blowup import rank_tuple
from remaining_one_v import DirectionalModel
import solver_chambers as chambers
from verify_linking import SAT

A, B = (0, 1, 4, 5), (2, 3, 6, 7)
FREE = (1, 4, 5, 6, 7)
HALF = s.Rational(1, 2)


def canonical_cells(rows, symmetries):
    phase = [entry['permutation'] for entry in symmetries if entry['phase_preserving']]
    result = []
    for row in rows:
        values = dict(zip(A, row['a'])) | dict(zip(B, row['b']))
        maps = []
        for permutation, reflection in product(phase, (-1, 1)):
            aa = rank_tuple([reflection * values[permutation[i]] for i in A])
            bb = rank_tuple([reflection * values[permutation[i]] for i in B])
            if (aa, bb) == ((0, 0, 1, 1), (1, 0, 1, 2)):
                maps.append({'permutation': permutation, 'horizontal_reflection': reflection})
        if maps:
            result.append(dict(row, canonical_map=maps[0]))
    assert len(result) == 16
    assert all(sorted((len(row['zero_a_edges']), len(row['zero_b_edges']))) == [0, 2]
               for row in result)
    return result


def interval_sign(expression, variable):
    """Exact sign of an affine coefficient throughout 0 < u < 1/2."""
    expression = s.cancel(expression)
    assert expression.is_polynomial(variable)
    assert s.Poly(expression, variable).degree() <= 1
    assert expression.free_symbols <= {variable}
    endpoints = (expression.subs(variable, 0), expression.subs(variable, HALF))
    assert any(endpoints)
    if all(value >= 0 for value in endpoints):
        return 1
    assert all(value <= 0 for value in endpoints)
    return -1


def direction_formula(nonedge=False):
    """Checked leading determinants, including separate positive edge factors."""
    n, original, *_ = chambers.base_formula()
    assert original[0] == [1]
    model = DirectionalModel.__new__(DirectionalModel)
    model.n, model.clauses, model.trits = n, [list(row) for row in original[1:]], {}
    u, epsilon, eta, kappa = s.symbols('u epsilon eta kappa')
    aa, ab, ba, bb, dx, dy = s.symbols('aa ab ba bb dx dy')
    # aa/ab and ba/bb are components in the A-line/B-line basis.
    forms = {'dx': dx, 'dy': dy, 'F': dy-2*dx} if nonedge else {
        'aa': aa, 'ab': ab, 'ba': ba, 'bb': bb}
    for key in forms:
        model.trits[key] = (model.n+1, model.n+2)
        model.n += 2
        model.clauses.append([-model.n+1, -model.n])
    if nonedge:
        model.clauses.append(list(model.trits['dx']) + list(model.trits['dy']))
        model.clauses.append(model.deny('dx', 1))
        # F + 2 dx = dy; a positive scalar preserves a trit.
        model.clauses += model.sum_clauses('F', 'dx', 'dy')
        first, second = (-1, 0), (1, 0)
    else:
        for x, y in (('aa', 'ab'), ('ba', 'bb')):
            model.clauses.append(list(model.trits[x]) + list(model.trits[y]))
        first, second = (ab+aa/2, aa), (bb+ba/2, ba)
    points = {
        0: (0, 0, 0), 1: (epsilon*first[0], epsilon*first[1], 0),
        4: (HALF, 1, 0), 5: (HALF+eta*second[0], 1+eta*second[1], 0),
        2: (0, 0, 1), 3: (-u, 0, 1),
        6: (kappa*dx, kappa*dy, 1) if nonedge else (0, 0, 1),
        7: (HALF-u, 0, 1),
    }
    counts = {'constant': 0, 'direction': 0, 'zero': 0}
    for index, quad in enumerate(chambers.Q, 1):
        origin, *rest = quad
        raw = s.expand(s.Matrix([[points[v][axis]-points[origin][axis]
                                  for axis in range(3)] for v in rest]).det())
        factors = [(epsilon, {0, 1}), (eta, {4, 5})]
        if nonedge:
            factors.append((kappa, {2, 6}))
        for scale, pair in factors:
            if pair <= set(quad):
                raw = s.cancel(raw/scale)
                assert raw.is_polynomial(u, epsilon, eta, kappa, *forms.values())
        leading = s.expand(raw.subs({epsilon: 0, eta: 0, kappa: 0}))
        if not leading:
            counts['zero'] += 1
            continue
        if leading.free_symbols <= {u}:
            model.clauses.append([index*interval_sign(leading, u)])
            counts['constant'] += 1
            continue
        matches = []
        for key, form in forms.items():
            coefficient = s.cancel(leading/form)
            if coefficient.free_symbols <= {u}:
                matches.append((key, coefficient))
        assert len(matches) == 1, (quad, leading, matches)
        key, coefficient = matches[0]
        model.bracket_link(index, key, interval_sign(coefficient, u))
        counts['direction'] += 1
    if not nonedge:
        # A disjunction saying at least one forced direction is absent.
        expected = {'aa': 0, 'ab': -1, 'ba': 0, 'bb': 1}
        model.clauses.append(sum((model.deny(key, value) for key, value in expected.items()), []))
    assert SAT(model.n, model.clauses).check() == -1
    return model.n, model.clauses, counts


def exact_checks():
    _, _, edges, _, _, kx, ky = load_data()
    a, b, u, t = s.symbols('a b u t')
    x = [s.Integer(0)] + list(s.symbols('x1:8'))
    g = [s.Integer(0)] + list(s.symbols('g1:8'))
    U, H, Z = {0: s.Integer(0), 2: x[2], 3: x[3]}, {0: s.Integer(0), 2: g[2], 3: g[3]}, {0: 0, 2: 0, 3: 0}
    for i in FREE:
        U[i], H[i], Z[i] = s.symbols(f'U{i} H{i} Z{i}')
    variables = x[1:] + g[1:] + [U[i] for i in FREE] + [H[i] for i in FREE]
    dependent = [v for v in variables if v not in (x[1], x[3], x[5])]
    parameters = {x[1]: -a, x[3]: x[2]-u, x[5]: x[4]-b}
    fx = (0, -a, u-a, -a, b-a, -a, HALF-u-a, -a)
    fg = (0, -a*(4*u-1)/2, -(4*a-1)*(4*u-1)/8,
          -(16*a*u-4*a-8*u+1)/8, -(4*u-1)*(2*a+2*b-1)/4,
          -(2*a-1)*(4*u-1)/4, -(4*a-1)*(4*u-1)/8,
          -(16*a*u-4*a-1)/8)
    fu = (0, -a, u-a, -a, HALF-a-b, HALF-a, u-a, HALF-a)
    family = dict(zip(x, fx)) | dict(zip(g, fg)) | {
        U[i]: fu[i] for i in FREE} | {H[i]: fg[i] for i in FREE} | {Z[i]: 0 for i in FREE}
    metric_edges = [edge for edge in edges if edge not in ((0, 2), (0, 3), (2, 3))]
    equations = []
    for i, j in metric_edges:
        ell = int(j in B)-int(i in B)
        du, dz, dh, dg = U[j]-U[i], Z[j]-Z[i], H[j]-H[i], g[j]-g[i]
        dx = x[j]-x[i]+kx[i, j]
        equations.append(s.expand(du**2+dz**2-dx**2-ell*dh-2*ky[i, j]*dg+t*(dh**2-dg**2)))
    assert len(equations) == len(dependent) == 21
    assert all(s.expand(eq.subs(family)) == 0 for eq in equations)
    regular = list(equations)
    defect_edges = ((0, 1), (4, 5))
    regular[metric_edges.index((0, 1))] = a+U[1]
    regular[metric_edges.index((4, 5))] = b-U[5]+U[4]
    regular = [value.subs(parameters) for value in regular]
    jacobian = s.Matrix(regular).jacobian(dependent).subs(family).subs({a: 0, b: 0, t: 0})
    assert s.factor(jacobian.det(method='domain-ge')) == -4096*u*(2*u-1)**2
    inverse = jacobian.inv(method='DM')
    responses = []
    for edge in defect_edges:
        rhs = s.zeros(21, 1)
        rhs[metric_edges.index(edge)] = 1
        responses.append(inverse*rhs)
    mode = {Z[i]: int(i in (4, 5)) for i in FREE}
    force = s.Matrix([0 if edge in defect_edges else (Z[edge[1]]-Z[edge[0]])**2
                      for edge in metric_edges]).subs(mode)
    responses.append(-inverse*force)
    for expression, expected in (
            (U[6]-x[2], ((1-2*u)/2, u, -HALF)),
            (H[6]-g[2], ((2*u-1)/4, u/2, -(4*u-1)/4))):
        assert s.expand(expression.subs(family)) == 0
        gradient = s.Matrix([expression]).jacobian(dependent)
        actual = tuple(s.factor((gradient*response)[0]) for response in responses)
        assert all(s.expand(left-right) == 0 for left, right in zip(actual, expected))

    # Independently force the corner intrinsic/height values from the
    # affine stress equations, rather than assuming the displayed family.
    physical = (0, 0, 0, -u, HALF, HALF, 0, HALF-u)
    ha, hb = (0, HALF, 0, HALF), (u, u, HALF-u, HALF-u)
    X = lambda i, j: x[j]-x[i]+kx[i, j]
    G = lambda i, j: g[j]-g[i]
    D = lambda i, j: X(i, j)**2+2*ky[i, j]*G(i, j)+t*G(i, j)**2
    linear = []
    for ai, (i, j) in enumerate(zip(A, A[1:]+A[:1])):
        for bi, (k, l) in enumerate(zip(B, B[1:]+B[:1])):
            stress = s.expand(X(i, j)*X(k, l)+t*G(i, j)*G(k, l)
                              -(D(i, l)+D(j, k)-D(i, k)-D(j, l))/2)
            linear.append(stress-ha[ai]*hb[bi]+(physical[j]-physical[i])*(physical[l]-physical[k]))
    for cap, weights in ((A, ha), (B, hb)):
        linear += [X(i, j)+weight for (i, j), weight in zip(zip(cap, cap[1:]+cap[:1]), weights)]
    matrix, rhs = s.linear_eq_to_matrix(linear, x[1:]+g[1:])
    corner = {key: s.sympify(value).subs({a: 0, b: 0}) for key, value in family.items()}
    assert matrix.shape == (24, 14) and matrix.rank() == 14 and not matrix.free_symbols
    assert all(s.expand(value) == 0 for value in matrix*s.Matrix([corner[v] for v in x[1:]+g[1:]])-rhs)
    cross = [equation for edge, equation in zip(metric_edges, equations)
             if (edge[0] in B) != (edge[1] in B)]
    without_heights = {key: value for key, value in corner.items() if key not in {H[i] for i in FREE}}
    height_matrix, height_rhs = s.linear_eq_to_matrix(
        [s.expand(value.subs(without_heights).subs(t, 0)) for value in cross], [H[i] for i in FREE])
    assert height_matrix.rank() == 5 and not height_matrix.free_symbols
    assert all(s.expand(value) == 0 for value in height_matrix*s.Matrix([corner[H[i]] for i in FREE])-height_rhs)
    print('PASS exact all-t family, corner necessity ranks 14/5, and nonsingular 21-variable chart')
    print('PASS nonedge26 displacement coefficient -1/2 and bounded relative axial correction')


def main():
    if len(sys.argv) > 2:
        raise SystemExit(__doc__)
    output = Path(sys.argv[1]) if len(sys.argv) == 2 else None
    symmetries = chambers.marked_symmetries()
    n, clauses, *_ = chambers.base_formula()
    models = chambers.enumerate_models(n, clauses, symmetries)
    _, zeros = two_line.check(models)
    cells = canonical_cells(zeros, symmetries)
    first = direction_formula()
    second = direction_formula(nonedge=True)
    exact_checks()
    print(f'PASS 16 checked order maps; direction implications UNSAT ({first[0]} variables), '
          f'virtual nonedge26 UNSAT ({second[0]} variables)')
    if output:
        output.mkdir(parents=True, exist_ok=True)
        for name, formula in (('split_required_directions', first), ('split_nonedge26', second)):
            chambers.write_cnf(output/(name+'.cnf'), formula[0], formula[1])
        blocked = clauses + [[-(i+1)*value for i, value in enumerate(model)] for model in models]
        chambers.write_cnf(output/'split_model_coverage.cnf', n, blocked)
        (output/'split_cells.json').write_text(json.dumps(cells, indent=2)+'\n')
    print('Scope: these 16 unbounded-sequence blow-up orders; no explicit height or full marking exclusion.')


if __name__ == '__main__':
    if not __debug__:
        raise RuntimeError('run with assertions enabled')
    main()
