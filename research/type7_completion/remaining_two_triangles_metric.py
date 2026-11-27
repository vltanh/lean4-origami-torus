#!/usr/bin/env python3
"""Exact metric checks for the final ray-3 triangle-pair blow-up.

The sign/shape cover and uniform argument are in
remaining_two_triangles_blowup.py/.md. This helper independently forces
the corner data, checks its all-t planar reference, and derives the
vanishing first variation used by that argument.
"""

import sympy as s

import remaining_cluster_blowup as cluster

A, B, FREE = cluster.A, cluster.B, cluster.FREE


def exact_checks():
    t, x, g, U, H, Z, variables, edges, equations, kx, ky = cluster.metric_system()
    half = s.Rational(1, 2)
    X = lambda i, j: x[j]-x[i]+kx[i, j]
    G = lambda i, j: g[j]-g[i]
    D = lambda i, j: X(i, j)**2+ky[i, j]**2/t+2*ky[i, j]*G(i, j)+t*G(i, j)**2
    physical = (0, half, 0, -half, 0, 0, -half, -half)
    weights = ((half, half, 0, 0), (half, 0, 0, half))
    rings = [tuple(zip(cap, cap[1:]+cap[:1])) for cap in (A, B)]
    residuals = []
    for ai, (i, j) in enumerate(rings[0]):
        for bi, (k, l) in enumerate(rings[1]):
            stress = s.expand(X(i, j)*X(k, l)+t*G(i, j)*G(k, l)
                              -(D(i, l)+D(j, k)-D(i, k)-D(j, l))/2)
            assert not stress.has(t)
            residuals.append(stress-weights[0][ai]*weights[1][bi]
                             +(physical[j]-physical[i])*(physical[l]-physical[k]))
    for ring, hs in zip(rings, weights):
        residuals.extend(X(i, j)+h for (i, j), h in zip(ring, hs))
    matrix, rhs = s.linear_eq_to_matrix(residuals, x[1:]+g[1:])
    assert matrix.shape == (24, 14) and not matrix.free_symbols and matrix.rank() == 14
    intrinsic = matrix.gauss_jordan_solve(rhs)[0]
    corner = dict(zip(x[1:]+g[1:], intrinsic))
    fx = (0, -half, 0, -half, -half, -half, 0, 0)
    fg = (0, s.Rational(1, 4), -s.Rational(1, 8), s.Rational(1, 8),
          0, 0, s.Rational(1, 8), s.Rational(1, 8))
    assert tuple(intrinsic) == fx[1:]+fg[1:]
    corner |= {U[i]: physical[i] for i in FREE} | {Z[i]: 0 for i in FREE}
    cross = [s.expand(eq.subs(t, 0).subs(corner))
             for (i, j), eq in zip(edges, equations) if (i in B) != (j in B)]
    heights = [H[i] for i in FREE]
    height_matrix, height_rhs = s.linear_eq_to_matrix(cross, heights)
    assert height_matrix.shape == (14, 5) and not height_matrix.free_symbols
    assert height_matrix.rank() == 5
    height_values = height_matrix.gauss_jordan_solve(height_rhs)[0]
    assert tuple(height_values) == (-s.Rational(3, 4), 0, 0,
                                   s.Rational(1, 8), s.Rational(1, 8))
    corner |= dict(zip(heights, height_values))

    # The naive constant corner has O(t) metric residuals. These two
    # rational corrections give an exact reference for every t near zero.
    reference = corner | {U[1]: (4-3*t)/(2*t+8), H[1]: (t-12)/(4*t+16)}
    assert all(s.cancel(eq.subs(reference)) == 0 for eq in equations)

    a, b, c = s.symbols('a b c')
    h45, h50, h36, h67 = (-X(4, 5), -X(5, 0), -X(3, 6), -X(6, 7))
    defects = (h45+U[5]-U[4], h50+U[5], h36+U[6]-U[3], h67-U[7]+U[6])
    indices = [edges.index(edge) for edge in ((4, 5), (0, 5), (3, 6), (6, 7))]
    assert all(s.cancel(defect.subs(reference)) == 0 for defect in defects)
    parameters = {x[5]: b+kx[5, 0],
                  x[4]: a+b+kx[5, 0]+kx[4, 5],
                  x[7]: x[6]-kx[6, 7]-c}
    assert s.expand(h45.subs(parameters)-a) == 0
    assert s.expand(h50.subs(parameters)-b) == 0
    assert s.expand(h67.subs(parameters)-c) == 0
    dependent = [value for value in variables if value not in parameters]
    regular = list(equations)
    for index, defect in zip(indices, defects):
        regular[index] = defect
    regular = [s.expand(eq.subs(parameters)) for eq in regular]
    base = corner | {a: 0, b: 0, c: 0, t: 0}
    jacobian = s.Matrix(regular).jacobian(dependent).subs(base)
    assert jacobian.shape == (21, 21) and jacobian.det() == 2048
    inverse = jacobian.inv()

    functional = h50+h36-U[5]-(U[6]-U[3])
    assert s.cancel(functional.subs(reference)) == 0
    expression = functional.subs(parameters)
    gradient = s.Matrix([expression]).jacobian(dependent).subs(base)
    derivatives = {}
    for parameter in (a, b, c):
        tangent = -inverse*s.Matrix(regular).diff(parameter).subs(base)
        value = s.factor((gradient*tangent)[0]+s.diff(expression, parameter).subs(base))
        assert value == 0
        derivatives[str(parameter)] = str(value)
    for edge, index in zip(((4, 5), (0, 5), (3, 6), (6, 7)), indices):
        forcing = s.zeros(21, 1)
        forcing[index] = 1
        value = s.factor((gradient*inverse*forcing)[0])
        assert value == 0
        derivatives['mu'+''.join(map(str, edge))] = str(value)
    # Normal dependence is even, so bounded quadratic normal corrections
    # suffice: their size is o(M) from delta <= C min(h50,h36).
    assert all(s.diff(eq, Z[i]).subs(base) == 0 for eq in regular for i in FREE)

    levels = {i: int(i in B) for i in range(8)}
    points = {i: s.Matrix((U[i], Z[i], levels[i]-2*t*H[i])) for i in range(8)}
    bracket = s.Matrix.hstack(points[3], points[4], points[7]-points[3]).det()
    factored = ((1-2*t*g[3])*(U[4]*Z[7]-Z[4]*(U[7]-x[3]))
                +2*t*x[3]*(H[4]*Z[7]-Z[4]*(H[7]-g[3])))
    assert s.expand(bracket-factored) == 0
    print('PASS triangle corner necessity ranks 14/5 and exact all-t reference', flush=True)
    print('PASS regular Jacobian determinant 2048 and all seven total F derivatives zero', flush=True)
    print('PASS exact [0347] factorization through the two short nonedge paths', flush=True)
    return {
        'intrinsic_x': list(map(str, fx)), 'intrinsic_gamma': list(map(str, fg)),
        'reference_U1': str(reference[U[1]]), 'reference_H1': str(reference[H[1]]),
        'jacobian_determinant': 2048, 'functional_derivatives': derivatives,
        'bracket_0347': str(factored),
    }


if __name__ == '__main__':
    if not __debug__:
        raise RuntimeError('run with assertions enabled')
    exact_checks()
