#!/usr/bin/env python3
"""One spatial unknown for each of the original 268 Type-7 K4 branches.

The 14 intrinsic coordinates and one missing squared distance are free.
All other spatial coordinates are rational functions of that distance.
An exact quadratic algebra makes all metric residuals and all actual
coordinate-minor sign tests affine in the spatial unknown.  Every
denominator discarded from a sign test is proved strictly positive.

This is a necessary-system rewrite, not an infeasibility certificate.
It preserves the original branch IDs and never subdivides a branch.
"""

import argparse
from dataclasses import dataclass
from fractions import Fraction as F
import hashlib
from itertools import combinations, permutations, product
import json
from pathlib import Path
import re

import exhaustive_remaining_axis as axis
import solver_remaining_chambers as common

V = tuple(range(8))
EDGES = tuple(e for e in combinations(V, 2) if e[1]-e[0] != 4)
PARTNER = tuple((i+4) % 8 for i in V)


def parity(values):
    return -1 if sum(a > b for i, a in enumerate(values) for b in values[i+1:]) % 2 else 1


def rational(value):
    value = F(value)
    numerator = str(value.numerator) if value >= 0 else f'(- {-value.numerator})'
    return numerator if value.denominator == 1 else f'(/ {numerator} {value.denominator})'


class DAG:
    """Hash-consed expressions with local rational-term cancellation.

    Sums and products are flattened, and equal summands are collected.
    Rational scaling of a sum is distributed; products of nonconstant
    sums are deliberately never expanded.
    """

    def __init__(self):
        self.nodes = []
        self.cache = {}
        self.operations = {}
        self.variables = []

    def variable(self, name):
        assert name not in self.variables
        self.variables.append(name)
        return name

    def node(self, operation, arguments):
        key = operation, tuple(arguments)
        if key not in self.cache:
            name = f'gg{len(self.nodes)}'
            self.nodes.append((name, operation, tuple(arguments)))
            self.operations[name] = operation, tuple(arguments)
            self.cache[key] = name
        return self.cache[key]

    def add(self, *arguments):
        constant, coefficients = F(0), {}

        def collect(value, coefficient=F(1)):
            nonlocal constant
            if isinstance(value, F):
                constant += coefficient*value
                return
            operation, children = self.operations.get(value, (None, ()))
            if operation == '+':
                for child in children:
                    collect(child, coefficient)
                return
            if operation == '*':
                factors = []
                for child in children:
                    if isinstance(child, F):
                        coefficient *= child
                    else:
                        factors.append(child)
                if len(factors) == 1:
                    collect(factors[0], coefficient)
                    return
                value = self.node('*', factors)
            coefficients[value] = coefficients.get(value, F(0))+coefficient

        for value in arguments:
            collect(value)
        rest = [self.mul(coefficient, value) for value, coefficient in coefficients.items()
                if coefficient]
        if constant:
            rest.append(constant)
        if not rest:
            return F(0)
        if len(rest) == 1:
            return rest[0]
        return self.node('+', sorted(rest, key=str))

    def mul(self, *arguments):
        constant, rest = F(1), []

        def collect(value):
            nonlocal constant
            if isinstance(value, F):
                constant *= value
            else:
                operation, children = self.operations.get(value, (None, ()))
                if operation == '*':
                    for child in children:
                        collect(child)
                else:
                    rest.append(value)

        for value in arguments:
            collect(value)
        if not constant:
            return F(0)
        if constant != 1 and len(rest) == 1:
            operation, children = self.operations.get(rest[0], (None, ()))
            if operation == '+':
                return self.add(*(self.mul(constant, child) for child in children))
        if constant != 1:
            rest.append(constant)
        if not rest:
            return F(1)
        if len(rest) == 1:
            return rest[0]
        return self.node('*', sorted(rest, key=str))

    def neg(self, value):
        return self.mul(F(-1), value)

    def sub(self, a, b):
        return self.add(a, self.neg(b))

    def power(self, value, exponent):
        assert exponent >= 0
        if exponent == 0:
            return F(1)
        if exponent == 1:
            return value
        return self.mul(*(value for _ in range(exponent)))

    def det(self, matrix):
        n = len(matrix)
        return self.add(*(self.mul(F(parity(p)), *(matrix[i][p[i]] for i in range(n)))
                          for p in permutations(range(n))))

    def text(self, value):
        return rational(value) if isinstance(value, F) else value

    def reachable(self, roots):
        """Arithmetic nodes transitively needed by the supplied scalar roots."""
        needed, todo = set(), list(roots)
        while todo:
            value = todo.pop()
            if value in needed or value not in self.operations:
                continue
            needed.add(value)
            todo.extend(self.operations[value][1])
        return needed

    def lines(self, roots=None):
        needed = None if roots is None else self.reachable(roots)
        return [f'(define-fun {name} () Real ({operation} '
                + ' '.join(self.text(value) for value in arguments)+'))'
                for name, operation, arguments in self.nodes
                if needed is None or name in needed]

    def evaluate(self, assignments):
        values = {name: F(value) for name, value in assignments.items()}
        for name, operation, arguments in self.nodes:
            arguments = [value if isinstance(value, F) else values[value] for value in arguments]
            if operation == '+':
                values[name] = sum(arguments, F(0))
            else:
                assert operation == '*'
                result = F(1)
                for value in arguments:
                    result *= value
                values[name] = result
        return values

    def degree_bounds(self):
        """Formal total-degree upper bounds, without relying on cancellation."""
        degrees = {name: 1 for name in self.variables}
        for name, operation, arguments in self.nodes:
            entries = [0 if isinstance(value, F) else degrees[value] for value in arguments]
            degrees[name] = max(entries) if operation == '+' else sum(entries)
        return degrees


@dataclass(frozen=True)
class Element:
    """(constant + linear*z)/A**exponent in the seed quadratic algebra."""
    constant: object
    linear: object = F(0)
    exponent: int = 0


class QuadraticAlgebra:
    def __init__(self, dag, a, b, c):
        self.d, self.a, self.b, self.c = dag, a, b, c

    def add(self, *values):
        exponent = max((value.exponent for value in values), default=0)
        return Element(*(self.d.add(*(
            self.d.mul(getattr(value, field), self.d.power(self.a, exponent-value.exponent))
            for value in values)) for field in ('constant', 'linear')), exponent)

    def neg(self, value):
        return Element(self.d.neg(value.constant), self.d.neg(value.linear), value.exponent)

    def sub(self, a, b):
        return self.add(a, self.neg(b))

    def mul(self, a, b):
        d = self.d
        if a.linear == F(0) or b.linear == F(0):
            return Element(d.mul(a.constant, b.constant),
                           d.add(d.mul(a.constant, b.linear), d.mul(a.linear, b.constant)),
                           a.exponent+b.exponent)
        bb = d.mul(a.linear, b.linear)
        return Element(d.sub(d.mul(self.a, a.constant, b.constant), d.mul(self.c, bb)),
                       d.sub(d.mul(self.a, d.add(d.mul(a.constant, b.linear),
                                                d.mul(a.linear, b.constant))), d.mul(self.b, bb)),
                       a.exponent+b.exponent+1)

    def scale(self, scalar, value):
        return self.mul(Element(scalar), value)

    def prod(self, values):
        result = Element(F(1))
        for value in values:
            result = self.mul(result, value)
        return result

    def det(self, matrix):
        n = len(matrix)
        return self.add(*(self.scale(F(parity(p)), self.prod(matrix[i][p[i]] for i in range(n)))
                          for p in permutations(range(n))))

    def numerator(self, value, seed):
        return self.d.add(value.constant, self.d.mul(value.linear, seed))


def star_plan(manifest, branch):
    """Choose one star whose three actual nonclique minors are proved strict."""
    strict = set(branch['strict'])
    choices = []
    for anchors in product(*[(i, i+4) for i in range(4)]):
        leaves = tuple(PARTNER[i] for i in anchors)
        for seed in range(4):
            minors = [''.join(map(str, sorted([a for k, a in enumerate(anchors) if k != j]
                                              + [leaves[seed]])))
                      for j in range(4) if j != seed]
            if all(minor in strict for minor in minors):
                choices.append((anchors, seed, minors))
    if not choices:
        raise ValueError('no proved-strict propagation star; do not discard a zero case')
    original, seed, minors = min(choices)
    ordered = (original[seed],)+tuple(a for i, a in enumerate(original) if i != seed)
    signs = dict(zip(manifest['cliques'], branch['pattern']))
    anchor_sign = (1 if signs[''.join(map(str, sorted(ordered)))] == '+' else -1)*parity(ordered)
    replacement = (PARTNER[ordered[0]], *ordered[1:])
    replacement_sign = (1 if signs[''.join(map(str, sorted(replacement)))] == '+' else -1)*parity(replacement)
    return {'anchors': ordered, 'leaves': tuple(PARTNER[i] for i in ordered),
            'orientation': anchor_sign, 'strict_propagation_minors': minors,
            'seed_root_sign': -anchor_sign*replacement_sign,
            'seed_root_cliques': [ordered, replacement]}


def metric_chart(dag, distances, plan, seed):
    """Build Gram completion and sign-safe affine minors in one quadratic algebra."""
    A, B = plan['anchors'], plan['leaves']
    d = dag
    def distance(i, j):
        return F(0) if i == j else distances[tuple(sorted((i, j)))]
    G = [[d.mul(F(1, 2), d.sub(d.add(distance(A[0], A[i+1]), distance(A[0], A[j+1])),
                                           distance(A[i+1], A[j+1]))) for j in range(3)] for i in range(3)]
    g = d.det(G)
    H = [[d.mul(F((-1)**(i+j)), d.det([[G[k][ell] for ell in range(3) if ell != i]
                                      for k in range(3) if k != j])) for j in range(3)] for i in range(3)]
    u0 = [d.mul(F(1, 2), d.sub(distance(A[0], A[i+1]), distance(A[i+1], B[0])))
          for i in range(3)]
    def bilinear(left, right):
        return d.add(*(d.mul(left[i], H[i][j], right[j]) for i in range(3) for j in range(3)))
    qa = d.mul(F(1, 4), d.add(*(value for row in H for value in row)))
    qb = d.sub(bilinear([F(1)]*3, u0), g)
    qc = bilinear(u0, u0)
    ring = QuadraticAlgebra(d, qa, qb, qc)
    seed_u = [Element(value, F(1, 2)) for value in u0]
    numerators = {A[0]: [Element(F(0))]*3,
                  **{A[i+1]: [Element(G[j][i]) for j in range(3)] for i in range(3)},
                  B[0]: seed_u}
    denominators = {i: Element(F(1)) for i in (*A, B[0])}
    nonedges = {tuple(sorted((A[0], B[0]))): (Element(F(0), F(1)), Element(F(1)))}
    cross_identities = []
    for k in range(3):
        leaf = B[k+1]
        known = distance(A[0], leaf)
        base = [d.mul(F(1, 2), d.sub(d.add(distance(A[0], A[i+1]), known),
                                    F(0) if i == k else distance(A[i+1], leaf))) for i in range(3)]
        denominator = ring.add(*(ring.scale(H[k][i], seed_u[i]) for i in range(3)))
        n = ring.sub(ring.scale(F(2), ring.add(*(
            ring.scale(d.mul(H[i][j], base[j]), seed_u[i]) for i in range(3) for j in range(3)))),
            Element(d.mul(g, d.sub(known, distance(B[0], leaf))), g))
        vector = [ring.sub(ring.scale(base[i], denominator),
                           ring.scale(F(1, 2), n) if i == k else Element(F(0))) for i in range(3)]
        numerators[leaf], denominators[leaf] = vector, denominator
        nonedges[tuple(sorted((A[k+1], leaf)))] = n, denominator
        cross_identities.append((leaf, n, denominator))

    def gram(left, right):
        return ring.add(*(ring.scale(H[i][j], ring.mul(left[i], right[j]))
                          for i in range(3) for j in range(3)))
    equations = []
    for leaf in B[1:]:
        equations.append(ring.sub(gram(numerators[leaf], numerators[leaf]),
            ring.scale(d.mul(g, distance(A[0], leaf)), ring.mul(denominators[leaf], denominators[leaf]))))
    for leaf, other in combinations(B[1:], 2):
        equations.append(ring.sub(ring.scale(F(2), gram(numerators[leaf], numerators[other])),
            ring.scale(d.mul(g, d.sub(d.add(distance(A[0], leaf), distance(A[0], other)),
                                              distance(leaf, other))), ring.mul(denominators[leaf], denominators[other]))))
    # Reflection by the known ordered anchor sign preserves the original
    # normalized [0123]>0 convention. Lower-dimensional minors are recomputed.
    numerator_coordinates = {i: [*numerators[i][:2], ring.scale(F(plan['orientation']), numerators[i][2])]
                             for i in V}
    minors = {}
    for size in (2, 3, 4):
        for support in combinations(V, size):
            for axes in combinations(range(3), size-1):
                matrix = [[*(numerator_coordinates[i][axis] for axis in axes), denominators[i]]
                          for i in support]
                homogeneous = ring.scale(F((-1)**(size-1)), ring.det(matrix))
                # homogeneous/Πden is the actual affine minor. Multiplying
                # once more by Πden clears its denominator by a positive square.
                positive_cleared = ring.mul(homogeneous, ring.prod(denominators[i] for i in support))
                name = 'a'+''.join(map(str, support))+'c'+''.join(map(str, axes))
                minors[name] = positive_cleared
    assert len(minors) == 322 and len(equations) == 6 and len(nonedges) == 4
    return {'G': G, 'H': H, 'g': g, 'quadratic': (qa, qb, qc), 'ring': ring,
            'numerators': numerators, 'denominators': denominators, 'nonedges': nonedges,
            'metric_equations': equations, 'minors': minors, 'cross_identities': cross_identities}


def generate_parts(manifest, branch, mark, y, *, all_heights=False):
    assert mark in (1, 2) and y >= 32
    d = DAG()
    x = [F(0)]+[d.variable(f'x{i}') for i in V[1:]]
    v = [F(0)]+[d.variable(f'v{i}') for i in V[1:]]
    seed = d.variable('zseed')
    t = d.variable('t') if all_heights else F(1, y*y)
    plan = star_plan(manifest, branch)
    shifts, faces, edges = axis.case_data(mark)
    assert tuple(edges) == EDGES
    tests, distances, directions = [], {}, {}
    def require(operator, left, right=F(0)):
        tests.append(f'({operator} {d.text(left)} {d.text(right)})')
    def abslt(value, bound):
        require('<', value, bound)
        require('>', value, d.neg(bound))
    def direction(i, j, m, n):
        return d.add(d.sub(x[j], x[i]), F(m)+F(n, 2)), d.add(d.sub(v[j], v[i]), F(n))
    def norm(dx, dy):
        return d.add(d.mul(t, dx, dx), d.mul(dy, dy))
    if all_heights:
        require('>', t)
        require('<=', t, F(1, y*y))
    require('>=', v[1], F(1, 8))
    for i, j in EDGES:
        dx, dy = direction(i, j, *shifts[i, j])
        directions[i, j] = dx, dy
        directions[j, i] = d.neg(dx), d.neg(dy)
        distances[i, j] = norm(dx, dy)
        require('>', distances[i, j])
        abslt(dx, F(1, 2))
        for sign in (-1, 1):
            abslt(d.add(dy, d.mul(F(sign, 2), t, dx)), d.add(F(1, 2), d.mul(F(1, 8), t)))
    # Each cyclic triangle has period (-1,0). Its three horizontal
    # displacements sum to -1 and are individually in (-1/2,1/2),
    # so all three are negative. These are already in the axis source.
    for i in V:
        triangle = (i, (i+1) % 8, (i+2) % 8)
        triangle_edges = tuple(zip(triangle, triangle[1:]+triangle[:1]))
        assert tuple(sum(shifts[edge][k] for edge in triangle_edges) for k in (0, 1)) == (-1, 0)
        require('<', directions[i, (i+1) % 8][0])
    areas = []
    for i, j, k in faces:
        u, w = directions[i, j], directions[i, k]
        areas.append(d.sub(d.mul(u[0], w[1]), d.mul(w[0], u[1])))
    area_sum = d.add(*areas)
    tests.append('(or '+ ' '.join('(and '+ ' '.join(
        [f'({">" if sign == 1 else "<"} {d.text(area)} 0)' for area in areas]
        + [f'(= {d.text(area_sum)} {rational(2*sign)})'])+')' for sign in (1, -1))+')')
    chart = metric_chart(d, distances, plan, seed)
    ring = chart['ring']
    G, qa, qb, qc = chart['G'], *chart['quadratic']
    require('>', G[0][0])
    require('>', d.det([row[:2] for row in G[:2]]))
    require('>', chart['g'])
    require('>', qa)
    require('=', d.add(d.mul(qa, seed, seed), d.mul(qb, seed), qc))
    # F'(z)=-g*lambda_0(seed). Both lambda_0's numerator and its
    # denominator are strict K4 brackets with signs fixed in this branch.
    require('>', d.mul(F(plan['seed_root_sign']), d.add(d.mul(F(2), qa, seed), qb)))
    for leaf in plan['leaves'][1:]:
        denominator = chart['denominators'][leaf]
        assert denominator.exponent == 0
        require('distinct', ring.numerator(denominator, seed))
    for equation in chart['metric_equations']:
        require('=', ring.numerator(equation, seed))
    # Preserve all original necessary nonedge contractions without guessing
    # the sign of any propagation denominator.
    for (i, j), (numerator, denominator) in sorted(chart['nonedges'].items()):
        product_nr = ring.mul(numerator, denominator)
        rr = ring.mul(denominator, denominator)
        require('>', ring.numerator(product_nr, seed))
        for m in range(-4, 5):
            for n in range(-3, 4):
                upper = norm(*direction(i, j, m, n))
                require('<=', ring.numerator(ring.sub(product_nr, ring.scale(upper, rr)), seed))
    definitions = {name: f'(define-fun {name} () Real {d.text(ring.numerator(value, seed))})'
                   for name, value in chart['minors'].items()}
    scalar_roots = set(re.findall(r'\bgg\d+\b', '\n'.join([*tests, *definitions.values()])))
    needed = d.reachable(scalar_roots)
    prefix = '\n'.join(['(set-logic QF_NRA)',
                        *[f'(declare-fun {name} () Real)' for name in d.variables],
                        *d.lines(roots=scalar_roots), *[f'(assert {test})' for test in tests]])+'\n'
    degrees = d.degree_bounds()
    def degree(expression):
        return 0 if isinstance(expression, F) else degrees[expression]
    metadata = {'mark': mark, 'minimum_y': y, 'all_heights': all_heights,
                'real_variables': len(d.variables), 'dag_nodes': len(needed),
                'constructed_dag_nodes': len(d.nodes),
                'plan': plan, 'seed_quadratic': [d.text(value) for value in chart['quadratic']],
                'metric_affine_equations': 6, 'actual_affine_minors': 322,
                'maximum_positive_scaling_exponent': max(value.exponent for value in chart['minors'].values()),
                'formal_total_degree_bound': max(degrees[name] for name in needed),
                'seed_coefficient_degree_bounds': [degree(value) for value in chart['quadratic']],
                'metric_affine_coefficient_degree_bound': max(degree(coefficient)
                    for value in chart['metric_equations'] for coefficient in (value.constant, value.linear)),
                'minor_affine_coefficient_degree_bound': max(degree(coefficient)
                    for value in chart['minors'].values() for coefficient in (value.constant, value.linear)),
                'scope': 'necessary rewrite; no branch excluded'}
    assert len(d.variables) == (16 if all_heights else 15)
    return (prefix, definitions, metadata)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('manifest', type=Path, help='existing axis_chambers.json')
    parser.add_argument('output', type=Path)
    parser.add_argument('--mark', type=int, choices=(1, 2), required=True)
    parser.add_argument('--y', type=int, default=32)
    parser.add_argument('--all-heights', action='store_true')
    parser.add_argument('--branch', type=int, action='append', help='existing zero-based branch ID')
    args = parser.parse_args()
    data = args.manifest.read_bytes()
    manifest = json.loads(data)
    assert len(manifest['branches']) == 268
    plans = [star_plan(manifest, branch) for branch in manifest['branches']]
    args.output.mkdir(parents=True, exist_ok=True)
    selected = args.branch if args.branch is not None else range(268)
    records = []
    for index in selected:
        assert 0 <= index < 268
        branch = manifest['branches'][index]
        parts = generate_parts(manifest, branch, args.mark, args.y, all_heights=args.all_heights)
        query = common.generate_query(parts, manifest['cliques'], branch)
        name = f'ray{args.mark}_axis_k4_{index:03d}.smt2'
        (args.output/name).write_text(query)
        records.append({'branch_id': index, 'pattern': branch['pattern'], 'file': name,
                        'sha256': hashlib.sha256(query.encode()).hexdigest(), 'bytes': len(query),
                        **parts[2]})
        print(json.dumps({'branch_id': index, 'bytes': len(query), **parts[2]}), flush=True)
    result = {'source_manifest_sha256': hashlib.sha256(data).hexdigest(),
              'original_branch_count': 268, 'all_branch_star_plans': plans,
              'queries': records, 'excluded_branches': [],
              'status': 'No SAT, UNSAT, or full-branch exclusion is claimed.'}
    (args.output/'branch_gram_manifest.json').write_text(json.dumps(result, indent=2)+'\n')


if __name__ == '__main__':
    if not __debug__:
        raise RuntimeError('run with assertions enabled')
    main()
