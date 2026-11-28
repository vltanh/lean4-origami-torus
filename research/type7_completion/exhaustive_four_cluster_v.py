#!/usr/bin/env python3
"""Exact checks for the two vertical-V four-zero endpoint exclusions.

Usage: python exhaustive_four_cluster_v.py [OUTPUT_DIRECTORY]

The uniform analytic argument is in exhaustive_four_cluster_v.md.  This
module checks the necessary sign implications, the two exact all-t
references, their regularized Jacobians, and every derivative used there.
"""

from pathlib import Path
import json
import sys

import sympy as s

import remaining_cluster_blowup as cluster
from solver_chambers import write_cnf
from verify_linking import lit


ROWS = {
    'opposite': {'a': (0, 0, 0, 1), 'x': (1, 0, 1, 1),
                 'y': (0, 0, 0, 1), 'beta': (0, -1, 0, 1)},
    'complementary': {'a': (0, 0, 0, 1), 'x': (1, 0, 0, 0),
                      'y': (1, 1, 0, 1), 'beta': (1, 0, -1, 0)},
}


def sign_implication(geometry, kind):
    model = cluster.Model(geometry, ROWS[kind], -1)
    required = {'ax': 1, 'ay': 0, 'bx': 0, 'by': 1}
    signs = [-lit((0, 1, 4, 5)), -lit((2, 3, 6, 7)),
             lit((1, 4, 6, 7))]
    signs.append(lit((1, 2, 4, 7)) if kind == 'opposite'
                 else -lit((1, 3, 4, 6)))
    violation = [-value for value in signs]
    violation += sum((model.deny(key, value) for key, value in required.items()), [])
    model.clauses.append(violation)
    assert cluster.proves_unsat(model.n, model.clauses), kind
    return model.n, model.clauses


def metric_checks(kind):
    t, x, g, U, H, Z, variables, edges, equations, kx, ky = cluster.metric_system()
    a, b, k = s.symbols('a b k')
    p, mb, mc, md = s.symbols('p mb mc md')
    half, eighth = s.Rational(1, 2), s.Rational(1, 8)
    X = lambda i, j: x[j]-x[i]+kx[i, j]
    G = lambda i, j: g[j]-g[i]
    D = lambda i, j: X(i, j)**2+2*ky[i, j]*G(i, j)+t*G(i, j)**2
    h67 = -X(6, 7)
    if kind == 'opposite':
        fx = (0, -a, half, 0, half-a, 0, 0, 0)
        fg = (0, a/2, eighth, 3*eighth, a/2, s.Rational(1, 4), eighth, eighth)
        fu = (0, a, half, 0, a, half, half, half)
        fh = fg
        shift = s.Integer(0)
        parameters = {x[1]: -a, x[4]: half-a-b, x[7]: x[2]+k-half}
        zero_edges = ((0, 1), (1, 4), (6, 7), (2, 7))
        defects = (a-U[1], b-U[4]+U[1], h67-U[7]+U[6], k+U[7]-U[2])
        targets = (h67, U[6]-x[2], H[6]-g[2])
        expected = {
            'k': (0, -1, -s.Rational(3, 2)),
            'mc': (half, half, s.Rational(3, 4)),
            'md': (half, half, s.Rational(3, 4)),
        }
        expected_mixed = {b: 0, k: 0, mb: -2, mc: 2, md: 1}
        physical = (0, a, 0, -half, a, half, 0, 0)
        weights = ((a, 0, half-a, half), (half, half, 0, 0))
    else:
        assert kind == 'complementary'
        q0 = (4-3*t)/(4+t)
        v0 = (t-12)/(2*(4+t))
        fx = (0, -a, 0, -half, half-a, 0, 0, 0)
        fg = (0, a/2, -eighth, eighth, a/2, s.Rational(1, 4), eighth, eighth)
        fu = (0, a*q0, 0, -half, a*q0, q0/2, -half, -half)
        fh = (0, a*v0, -eighth, eighth, a*v0, v0/2, eighth, eighth)
        shift = 4*a*t/(4+t)
        parameters = {x[1]: -a, x[4]: half-a-b, x[6]: x[3]+half-k}
        zero_edges = ((0, 1), (1, 4), (3, 6), (6, 7))
        defects = (a-U[1]-shift, b-U[4]+U[1], k+U[6]-U[3], h67-U[7]+U[6])
        targets = (h67, U[7]-x[3], H[7]-g[3])
        expected = {
            'k': (0, -1, half),
            'mc': (0, 1, -s.Rational(3, 2)),
            'md': (half, -half, s.Rational(1, 4)),
        }
        expected_mixed = {b: 0, k: 2, mb: 0, mc: -1, md: 2}
        physical = (0, a, 0, -half, a, half, -half, -half)
        weights = ((a, 0, half-a, half), (half, 0, 0, half))
        assert s.factor(q0*q0+t*v0*v0-1-t/4) == 0
    family = ({x[i]: fx[i] for i in range(1, 8)}
              | {g[i]: fg[i] for i in range(1, 8)}
              | {U[i]: fu[i] for i in cluster.FREE}
              | {H[i]: fh[i] for i in cluster.FREE}
              | {Z[i]: 0 for i in cluster.FREE})
    assert all(s.factor(eq.subs(family)) == 0 for eq in equations)
    assert all(s.factor(defect.subs(family).subs({b: 0, k: 0})) == 0
               for defect in defects)

    # The limiting metric branch is forced by the same constant linear
    # stress and cross-height reconstruction used in the preceding strata.
    steps = [cluster.cover.edge_differences(tuple(physical[i] for i in cap))
             for cap in (cluster.A, cluster.B)]
    residuals = []
    for i, (v, vv) in enumerate(zip(cluster.A, cluster.A[1:]+cluster.A[:1])):
        for j, (w, ww) in enumerate(zip(cluster.B, cluster.B[1:]+cluster.B[:1])):
            stress = s.expand(X(v, vv)*X(w, ww)+t*G(v, vv)*G(w, ww)
                              -(D(v, ww)+D(vv, w)-D(v, w)-D(vv, ww))/2)
            assert not stress.has(t)
            residuals.append(stress-weights[0][i]*weights[1][j]+steps[0][i]*steps[1][j])
    for cap, hs in zip((cluster.A, cluster.B), weights):
        residuals += [X(i, j)+h for (i, j), h in zip(zip(cap, cap[1:]+cap[:1]), hs)]
    matrix, rhs = s.linear_eq_to_matrix(residuals, x[1:]+g[1:])
    assert not matrix.free_symbols and matrix.rank() == 14
    assert all(s.expand(v) == 0 for v in matrix*s.Matrix(fx[1:]+fg[1:])-rhs)
    heights = [H[i] for i in cluster.FREE]
    reduced_family = {key: val for key, val in family.items() if key not in heights}
    hm, hr = s.linear_eq_to_matrix([
        eq.subs(t, 0).subs(reduced_family).subs(t, 0)
        for (i, j), eq in zip(edges, equations) if (i in cluster.B) != (j in cluster.B)
    ], heights)
    assert not hm.free_symbols and hm.rank() == 5
    assert all(s.factor(v.subs(t, 0)) == 0 for v in
               hm*s.Matrix([fh[i] for i in cluster.FREE])-hr)

    dependent = [v for v in variables if v not in parameters]
    indices = [edges.index(edge) for edge in zero_edges]
    modified = list(equations)
    for index, defect, variable in zip(indices, defects, (p, mb, mc, md)):
        modified[index] = defect-variable
    modified = [eq.subs(parameters) for eq in modified]
    corner = {a: 0, b: 0, k: 0, t: 0, p: 0, mb: 0, mc: 0, md: 0}
    at_corner = lambda expression: expression.subs(family).subs(corner)
    jacobian = at_corner(s.Matrix(modified).jacobian(dependent))
    determinant = jacobian.det(method='domain-ge')
    assert determinant == 2048
    inverse = jacobian.inv(method='DM')
    pars = (a, b, k, t, p, mb, mc, md)
    jets = {var: -inverse*at_corner(s.Matrix(modified).diff(var)) for var in pars}
    targets = tuple(target.subs(parameters) for target in targets)
    gradients = [at_corner(s.Matrix([target]).jacobian(dependent)) for target in targets]
    actual = {}
    for name in expected:
        var = {'k': k, 'mc': mc, 'md': md}[name]
        actual[name] = tuple(s.factor((gradient*jets[var])[0]+at_corner(s.diff(target, var)))
                             for target, gradient in zip(targets, gradients))
        assert actual[name] == expected[name], (kind, name, actual[name])

    # W vanishes on the exact reference and on a=p=Z1=0.  Its mixed
    # derivatives are consequently the first derivatives of its a-factor.
    W = H[1]-U[1]*H[5]/U[5]
    assert s.factor(W.subs(family)) == 0
    gradient = at_corner(s.Matrix([W]).jacobian(dependent))
    hessian = at_corner(s.hessian(W, dependent))
    equation_hessians = [at_corner(s.hessian(eq, dependent)) for eq in modified]
    mixed = {}
    for var, coefficient in expected_mixed.items():
        va, vv = jets[a], jets[var]
        forcing = s.Matrix([
            (va.T*hh*vv)[0]
            + sum(va[j]*at_corner(s.diff(eq, dependent[j], var))
                  + vv[j]*at_corner(s.diff(eq, dependent[j], a)) for j in range(21))
            + at_corner(s.diff(eq, a, var))
            for eq, hh in zip(modified, equation_hessians)
        ])
        value = s.factor((gradient*(-inverse*forcing))[0]+(va.T*hessian*vv)[0])
        assert value == coefficient, (kind, var, value, coefficient)
        mixed[str(var)] = str(value)

    E = dict(zip(edges, equations))
    assert s.expand(E[1, 3]-E[0, 1]-(H[1]-g[1])*(1-2*t*g[3])
                    +2*x[3]*(U[1]-x[1])) == 0
    collapsed = E[1, 3].subs({x[1]: 0, U[1]: 0, Z[1]: 0})
    assert s.expand(collapsed-(H[1]-g[1])*(1+t*(H[1]+g[1]-2*g[3]))) == 0
    intrinsic_stress = s.expand(X(0, 1)*X(3, 6)+t*G(0, 1)*G(3, 6)
                               -(D(0, 6)+D(1, 3)-D(0, 3)-D(1, 6))/2)
    assert s.expand(intrinsic_stress+g[1]+x[1]/2) == 0
    print(f'PASS {kind}: exact all-t reference, ranks14/5, determinant2048, relative-cap jets', flush=True)
    return {'determinant': int(determinant),
            'targets': {key: list(map(str, value)) for key, value in actual.items()},
            'mixed_W': mixed, 'normalized_01_defect_shift': str(shift)}


def main():
    if not __debug__:
        raise RuntimeError('run with assertions enabled')
    if len(sys.argv) > 2:
        raise SystemExit(__doc__)
    output = Path(sys.argv[1]) if len(sys.argv) == 2 else None
    if output:
        output.mkdir(parents=True, exist_ok=True)
    geometry = cluster.Geometry()
    records = {}
    for kind in ROWS:
        n, clauses = sign_implication(geometry, kind)
        if output:
            write_cnf(output/f'four_cluster_v_{kind}.cnf', n, clauses)
        records[kind] = metric_checks(kind)
    if output:
        (output/'four_cluster_v_identities.json').write_text(json.dumps(records, indent=2)+'\n')
    print('PASS both vertical-V four-zero endpoints and their checked mirror images')


if __name__ == '__main__':
    main()
