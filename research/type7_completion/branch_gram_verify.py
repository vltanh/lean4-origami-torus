#!/usr/bin/env python3
"""Independent source and exact-coordinate checks for branch_gram_chart.

This checks algebra and the unchanged whole-branch cover. It does not
turn a solver verdict into a proof or claim any branch infeasible.
"""

import argparse
from fractions import Fraction as F
from itertools import combinations, permutations
import json
from pathlib import Path
import time

import sympy as s

import branch_gram_chart as chart


def det(matrix):
    total = F(0)
    for permutation in permutations(range(len(matrix))):
        value = F(chart.parity(permutation))
        for i, j in enumerate(permutation):
            value *= matrix[i][j]
        total += value
    return total


def dot(a, b):
    return sum((x*y for x, y in zip(a, b)), F(0))


def sub(a, b):
    return tuple(x-y for x, y in zip(a, b))


def affine(points, support, axes):
    first, *rest = support
    return det([[points[i][axis]-points[first][axis] for axis in axes] for i in rest])


def symbolic_source():
    """Universal identities, independent of any selected numerical point."""
    a, b, c, z = s.symbols('a b c z')
    p, q, r, t = s.symbols('p q r t')
    Fz = a*z*z+b*z+c
    # The only division suppressed by quadratic multiplication is by a>0.
    reduced = (a*p*r-c*q*t)+(a*(p*t+q*r)-b*q*t)*z
    assert s.expand(a*(p+q*z)*(r+t*z)-reduced-q*t*Fz) == 0
    # The compiler must recognize its own quotient relation as literal zero;
    # retaining an unsimplified high-degree identity obscures the projection.
    dag = chart.DAG()
    aa, bb, cc = [dag.variable(name) for name in ('A', 'B', 'C')]
    algebra = chart.QuadraticAlgebra(dag, aa, bb, cc)
    zz = chart.Element(F(0), F(1))
    relation = algebra.add(algebra.scale(aa, algebra.mul(zz, zz)),
                           algebra.scale(bb, zz), chart.Element(cc))
    assert relation.constant == relation.linear == 0
    G = s.Matrix(3, 3, lambda i, j: s.Symbol(f'g{min(i,j)}{max(i,j)}'))
    H = G.adjugate()
    g = G.det()
    assert (G*H-g*s.eye(3)).applyfunc(s.expand) == s.zeros(3)
    u = s.Matrix(s.symbols('u0:3'))
    ones = s.ones(3, 1)
    Uz = u+z*ones/2
    A, B, C = (ones.T*H*ones)[0]/4, (ones.T*H*u)[0]-g, (u.T*H*u)[0]
    assert s.expand((Uz.T*H*Uz)[0]-g*z-(A*z*z+B*z+C)) == 0
    # F'=-g lambda_0. No division is used to check this identity.
    assert s.expand(2*A*z+B-(ones.T*H*Uz)[0]+g) == 0
    known, edge = s.symbols('known edge')
    v = s.Matrix(s.symbols('v0:3'))
    for k in range(3):
        R = (H*Uz)[k]
        N = 2*(Uz.T*H*v)[0]-g*(z+known-edge)
        V = R*v-N*s.eye(3)[:, k]/2
        assert s.expand(2*(Uz.T*H*V)[0]-g*R*(z+known-edge)) == 0
    return {'quadratic_reduction_identities': 1, 'quotient_relation_cancels': True,
            'Gram_inverse_identity': 1,
            'seed_quadratic_and_derivative_identities': 2, 'propagation_identities': 3}


FIXTURES = (
    ((0, 0, 0), (2, 0, 0), (0, 3, 0), (0, 0, 5),
     (1, 2, 3), (-2, 1, 4), (3, -1, 2), (2, 2, -2)),
    # 0145 is coplanar. Nonclique zero determinants must remain zero.
    ((0, 0, 0), (2, 0, 0), (0, 3, 0), (0, 0, 5),
     (1, 1, 2), (2, 1, 2), (3, -1, 2), (2, 2, -2)),
    ((1, -2, 1), (4, 0, -1), (-1, 3, 2), (2, 1, 6),
     (3, -1, 4), (-2, -3, 1), (4, 3, 2), (2, 4, -3)),
)


def coordinate_replay(plan):
    d = chart.DAG()
    D = {edge: d.variable('d'+''.join(map(str, edge))) for edge in chart.EDGES}
    seed = d.variable('zseed')
    result = chart.metric_chart(d, D, plan, seed)
    # Append numerator expressions before evaluating the scalar DAG.
    ring = result['ring']
    expressions = {name: ring.numerator(value, seed) for name, value in result['minors'].items()}
    equations = [ring.numerator(value, seed) for value in result['metric_equations']]
    counts = {'fixtures': 0, 'minor_checks': 0, 'zero_full_minors': 0, 'missing_distance_checks': 0}
    for input_points in FIXTURES:
        points = [tuple(map(F, point)) for point in input_points]
        a0, *rest = plan['anchors']
        basis = [sub(points[i], points[a0]) for i in rest]
        G = [[dot(u, v) for v in basis] for u in basis]
        g = det(G)
        if not g:
            continue
        # Each propagation denominator is the matching nonclique bracket.
        b0 = plan['leaves'][0]
        if any(not affine(points, (a0, *[a for a in rest if a != rest[k]], b0), (0, 1, 2))
               for k in range(3)):
            continue
        data = {D[edge]: dot(sub(points[edge[1]], points[edge[0]]),
                            sub(points[edge[1]], points[edge[0]])) for edge in chart.EDGES}
        data[seed] = dot(sub(points[b0], points[a0]), sub(points[b0], points[a0]))
        values = d.evaluate(data)
        def scalar(value):
            return value if isinstance(value, F) else values[value]
        A, B, C = map(scalar, result['quadratic'])
        z = data[seed]
        assert A > 0 and g == scalar(result['g']) > 0 and A*z*z+B*z+C == 0
        def evaluate(value):
            return (scalar(value.constant)+scalar(value.linear)*z)/A**value.exponent
        U = [[dot(vector, sub(points[i], points[a0])) for vector in basis] for i in chart.V]
        reflected_U = [row[:2]+[F(plan['orientation'])*row[2]] for row in U]
        for i in chart.V:
            denominator = evaluate(result['denominators'][i])
            assert denominator != 0
            assert [evaluate(value)/denominator for value in result['numerators'][i]] == U[i]
        for edge, (numerator, denominator) in result['nonedges'].items():
            actual = dot(sub(points[edge[1]], points[edge[0]]), sub(points[edge[1]], points[edge[0]]))
            assert evaluate(numerator)/evaluate(denominator) == actual
            counts['missing_distance_checks'] += 1
        assert all(scalar(expression) == 0 for expression in equations)
        for name, value in result['minors'].items():
            support_text, axes_text = name[1:].split('c')
            support, axes = tuple(map(int, support_text)), tuple(map(int, axes_text))
            minor = affine(reflected_U, support, axes)
            denominator_square = F(1)
            for i in support:
                denominator_square *= evaluate(result['denominators'][i])**2
            assert denominator_square > 0
            assert scalar(expressions[name]) == minor*denominator_square*A**value.exponent
            counts['minor_checks'] += 1
            if len(support) == 4 and minor == 0:
                counts['zero_full_minors'] += 1
        # Check the seed-side binding against an independently computed
        # barycentric determinant, without assuming this fixture's branch.
        lam0 = affine(points, (b0, *rest), (0, 1, 2))/affine(points, plan['anchors'], (0, 1, 2))
        assert 2*A*z+B == -g*lam0
        counts['fixtures'] += 1
    assert counts['fixtures'] >= 1
    return counts


def verify(manifest_path):
    start = time.monotonic()
    manifest = json.loads(manifest_path.read_text())
    assert len(manifest['branches']) == 268
    identities = symbolic_source()
    plans = [chart.star_plan(manifest, branch) for branch in manifest['branches']]
    for branch, plan in zip(manifest['branches'], plans):
        assert all(q in branch['strict'] for q in plan['strict_propagation_minors'])
        signs = dict(zip(manifest['cliques'], branch['pattern']))
        first, second = plan['seed_root_cliques']
        expected = -chart.parity(first)*chart.parity(second)
        expected *= (1 if signs[''.join(map(str, sorted(first)))] == '+' else -1)
        expected *= (1 if signs[''.join(map(str, sorted(second)))] == '+' else -1)
        assert expected == plan['seed_root_sign']
    distinct = {tuple(plan['anchors']): plan for plan in plans}
    # Both orientation signs act by an invertible reflection and are
    # checked separately even where a selected plan uses only one sign.
    totals = {'fixtures': 0, 'minor_checks': 0, 'zero_full_minors': 0, 'missing_distance_checks': 0}
    for plan in distinct.values():
        for sign in (-1, 1):
            result = coordinate_replay({**plan, 'orientation': sign})
            for key, count in result.items():
                totals[key] += count
    assert totals['zero_full_minors'] > 0
    return {'original_branches': 268, 'star_plans_checked': 268,
            'ordered_anchor_plans': len(distinct), **identities, **totals,
            'seconds': time.monotonic()-start, 'excluded_branches': 0}


if __name__ == '__main__':
    if not __debug__:
        raise RuntimeError('run with assertions enabled')
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('manifest', type=Path)
    args = parser.parse_args()
    print(json.dumps(verify(args.manifest), indent=2))
