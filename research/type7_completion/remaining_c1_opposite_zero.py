#!/usr/bin/env python3
"""Exclude nonparallel cap directions in the ray-2 C1 opposite-zero orbit.

The zero edges are 23 and 07. Relative short-edge estimates and finite
nested sections reduce the argument to four independently replayable
CNFs. Parallel cap directions and other zero-edge orbits remain open.
"""

import argparse
from functools import lru_cache
from itertools import combinations, product
import json
from pathlib import Path
import time

import sympy as S

import remaining_c1_flat_positive_stretch as signs
import remaining_c1_sections as sections
import remaining_c1_short_edges as short_edges
import solver_remaining_c1_collinear as trits
import solver_remaining_chambers as shared
from solver_chambers import write_cnf
from solver_sat import FastSAT


A, B = signs.A, signs.B
HALF = S.Rational(1, 2)
NODES = (3, 4, 6, 8, 9)
PATTERNS = ((-1, 0, 1), (0, 0, 1), (0, 1, 1))


def metric_and_section_checks():
    h5, uv = S.symbols('h5 UdotV')
    rho5 = B*h5+(1-B)*h5
    assert S.expand(rho5-h5) == 0
    sigma5 = (1-B)*(1-h5)+B*(HALF-h5)
    lower_dot_residual = -(B-2*h5)*uv+HALF*sigma5-(HALF-h5)
    assert S.expand(lower_dot_residual+(B-2*h5)*(uv+S.Rational(1, 4))) == 0

    w, u, v = [S.Matrix(S.symbols(f'{name}x {name}y')) for name in ('W', 'U', 'V')]
    t = S.Symbol('t')
    p3 = w/A
    p4 = p3+u
    p5 = B*p4+(1-B)*v
    q = t*p4+(1-t)*v
    j = t/B*p5
    a_vertices = [(1-t)*v+t*p3, (1-t/B)*v+t/B*p5,
                  t/B*p5, t/B*p5, t*p4, (1-t)*v+t*p4]
    expected_a = [q-t*u, q, j, j, q-(1-t)*v, q]
    for actual, expected in zip(a_vertices, expected_a):
        sections.equal_vectors(actual, expected)
    sections.equal_vectors(j, q-(1-t/B)*v)
    b_vertices = [t*p3, t*p3, t*p3, S.zeros(2, 1),
                  (1-t/A)*v, S.zeros(2, 1)]
    expected_b = [t/A*w, t/A*w, t/A*w, S.zeros(2, 1),
                  (1-t/A)*v, S.zeros(2, 1)]
    for actual, expected in zip(b_vertices, expected_b):
        sections.equal_vectors(actual, expected)
    assert S.expand(t*HALF+(1-t)*HALF-HALF) == 0
    assert S.cancel(t/A*HALF+(1-t/A)*HALF-HALF) == 0
    # The noncollinear A tree has corner q(t), which cannot vanish at
    # two distinct heights: its constant coefficient is the nonzero V.
    for coordinate in q:
        assert S.Poly(S.expand(coordinate), t).degree() <= 1
    assert q.subs(t, 0) == v
    return {'zero_Y5_factor': True, 'backtracked_A_vertices': 6,
            'backtracked_B_vertices': 6, 'two_tree_lengths': '1/2',
            'original_annulus_source': sections.section_checks()}


@lru_cache(maxsize=1)
def normalized_forms():
    first_length, second_length = S.symbols('h k')
    crosses = {pair: S.Symbol('C'+''.join(map(str, pair)))
               for pair in combinations(NODES, 2)}
    vectors = {0: {}, 1: {}, 2: {3: 1}, 3: {3: 1, 8: first_length},
               4: {4: 1}, 5: {4: B, 6: 1-B}, 6: {6: 1}, 7: {9: second_length}}
    heights = (0, A/2, HALF, HALF, HALF, B/2, 0, 0)

    def cross(i, j):
        total = 0
        for a, x in vectors[i].items():
            for b, y in vectors[j].items():
                if a != b:
                    total += x*y*(1 if a < b else -1)*crosses[tuple(sorted((a, b)))]
        return total

    def origin(i, j, k):
        return heights[i]*cross(j, k)-heights[j]*cross(i, k)+heights[k]*cross(i, j)

    # Independently bind the alternating area expansion to direct
    # three-dimensional determinants in arbitrary transverse vectors.
    coordinate_vectors = {i: S.Matrix(S.symbols(f'x{i} y{i}')) for i in NODES}
    points = []
    for i in range(8):
        transverse = sum((value*coordinate_vectors[node] for node, value in vectors[i].items()),
                         S.zeros(2, 1))
        points.append(transverse.col_join(S.Matrix([heights[i]])))
    substitution = {variable: S.det(S.Matrix.hstack(coordinate_vectors[i], coordinate_vectors[j]))
                    for (i, j), variable in crosses.items()}
    records = []
    for quad in trits.QUADS:
        i, j, k, l = quad
        polynomial = S.expand(origin(j, k, l)-origin(i, k, l)
                              +origin(i, j, l)-origin(i, j, k))
        direct = S.det(S.Matrix.hstack(*(points[v]-points[i] for v in quad[1:])))
        assert S.expand(polynomial.subs(substitution)-direct) == 0
        first = {2, 3} <= set(quad)
        second = {0, 7} <= set(quad)
        divisor = (first_length if first else 1)*(second_length if second else 1)
        divided = S.cancel(polynomial/divisor)
        assert S.denom(divided).free_symbols.isdisjoint({first_length, second_length})
        expression = S.expand(divided.subs({first_length: 0, second_length: 0}))
        coefficients = {pair: expression.coeff(variable) for pair, variable in crosses.items()}
        assert S.expand(expression-sum(coefficients[pair]*variable
                                        for pair, variable in crosses.items())) == 0
        records.append((quad, coefficients, int(first)+int(second)))
    assert len(records) == 70
    assert sum(degree == 2 for _, _, degree in records) == 1
    return tuple(records)


class DoubleVirtualModel(trits.ActualBracketModel):
    """All bracket signs share one generic completion, at their own scales."""

    def __init__(self):
        self.n, base, *_ = shared.base_formula()
        assert base[0] == [1]
        self.clauses = [list(row) for row in base[1:]]
        self.trits = {}
        self.crosses = {pair: self.new_trit() for pair in combinations(NODES, 2)}

        def cross(i, j, sign=1):
            if i == j:
                return None
            if i > j:
                return cross(j, i, -sign)
            pair = self.crosses[i, j]
            return pair if sign > 0 else pair[::-1]

        self.cross = cross
        products = {}

        def multiply(left, right):
            key = tuple(sorted((left, right)))
            if key not in products:
                result = self.new_trit()
                products[key] = result
                for x, y, z in product((-1, 0, 1), repeat=3):
                    if x*y != z:
                        self.clauses.append(self.deny(left, x)+self.deny(right, y)
                                            +self.deny(result, z))
            return products[key]

        for i, j, k, l in combinations(NODES, 4):
            self.sumzero((multiply(cross(i, j), cross(k, l)),
                          multiply(cross(i, k, -1), cross(j, l)),
                          multiply(cross(i, l), cross(j, k))))
        self.omitted = []
        for quad, coefficients, _ in normalized_forms():
            bits = self.new_trit()
            self.trits[quad] = bits
            literal = shared.common.lit(quad)
            self.clauses.extend(([-bits[0], literal], [-bits[1], -literal]))
            terms = [bits[::-1]]
            for pair, coefficient in coefficients.items():
                sign = signs.coefficient_sign(coefficient)
                if sign is None:
                    self.omitted.append(quad)
                    break
                if sign:
                    terms.append(cross(*pair, sign))
            else:
                self.sumzero(terms)
        assert len(self.omitted) == 1
        # Orient the plane so that cross(U,V)>0, where U=P4-P3,V=P6.
        uv = self.new_trit()
        self.sumzero((uv[::-1], cross(4, 6), cross(3, 6, -1)))
        self.clauses.append([uv[0]])
        # U,V span the transverse plane. Each virtual unit direction
        # therefore has a nonzero cross with at least one of P3,P4,P6.
        for new in (8, 9):
            self.clauses.append([bit for i in (3, 4, 6) for bit in cross(i, new)])

    def positive_parallel_directions(self):
        # w=2(P4-P3), v=2P6. Positive coefficient magnitudes are relaxed.
        for i in NODES:
            self.sumzero([pair for pair in
                          (self.cross(i, 8, -1), self.cross(i, 4), self.cross(i, 3, -1))
                          if pair is not None])
            self.sumzero([pair for pair in (self.cross(i, 9, -1), self.cross(i, 6))
                          if pair is not None])
        self.clauses.append([self.cross(8, 9)[0]])


def factored_sign(expression):
    constant, factors = S.factor_list(expression)
    result = int(S.sign(constant))
    for factor, power in factors:
        sign = signs.coefficient_sign(factor)
        assert sign is not None
        result *= sign**power
    return int(result)


def negative_macro(branch):
    """Check W=-U or W=-V using only strict original limiting minors."""
    xi = S.Symbol('xi')
    u = S.Matrix([1, 0]) if branch == 'minus_U' else S.Matrix([xi, -1])
    v = S.Matrix([xi, 1]) if branch == 'minus_U' else S.Matrix([1, 0])
    w = -u if branch == 'minus_U' else -v
    p3, p4 = w/A, w/A+u
    p5 = B*p4+(1-B)*v
    transverse = [S.zeros(2, 1), S.zeros(2, 1), p3, p3, p4, p5, v, S.zeros(2, 1)]
    heights = (0, A/2, HALF, HALF, HALF, B/2, 0, 0)
    points = [point.col_join(S.Matrix([height])) for point, height in zip(transverse, heights)]
    n, base, *_ = shared.base_formula()
    assert base[0] == [1]
    clauses = [list(row) for row in base[1:]]
    units = []
    for quad in trits.QUADS:
        polynomial = S.cancel(A*S.det(S.Matrix.hstack(*(points[i]-points[quad[0]]
                                                        for i in quad[1:]))))
        assert not polynomial.has(xi)
        sign = factored_sign(polynomial)
        if sign:
            literal = sign*shared.common.lit(quad)
            clauses.append([literal])
            units.append(literal)
    assert len(units) == 32
    return n, clauses, units


def build(directory):
    started = time.monotonic()
    directory.mkdir(parents=True, exist_ok=True)
    checks = metric_and_section_checks()
    relative = short_edges.relative_metric_checks()
    short_edges.determinant_checks()
    obligations = []

    def export(filename, n, clauses, claim, **extra):
        with FastSAT(n, clauses) as solver:
            assert solver.check() == -1, filename
        write_cnf(directory/filename, n, clauses)
        obligations.append({'file': filename, 'claim': claim, 'variables': n,
                            'clauses': len(clauses), **extra})

    model = DoubleVirtualModel()
    triples = (model.cross(3, 8), model.cross(3, 9), model.cross(8, 9))
    violations = [sum((model.deny(pair, sign) for pair, sign in zip(triples, pattern)), [])
                  for pattern in PATTERNS]
    export('c1_opposite_zero_cross_patterns.cnf', model.n, model.clauses+violations,
           'the three normalized cross signs lie in the exact three-pattern cover',
           patterns=PATTERNS, omitted_variable_sign_relations=model.omitted)
    model.positive_parallel_directions()
    export('c1_opposite_zero_positive_parallel.cnf', model.n, model.clauses,
           'w=2U and v=2V are impossible')
    for branch in ('minus_U', 'minus_V'):
        n, clauses, units = negative_macro(branch)
        export(f'c1_opposite_zero_{branch}.cnf', n, clauses,
               'alpha P3='+('-U' if branch == 'minus_U' else '-V')+' is impossible',
               strict_original_minors=units)
    packet = {'domain': 'ray2, interior C1, h2=h7=0, E3 and P6 nonparallel',
              'checks': checks, 'relative_short_edge_source': relative,
              'normalized_determinants': 70, 'cross_patterns': PATTERNS,
              'unsat_obligations': obligations, 'relative_rate_assumptions': [],
              'parallel_EF_excluded': False, 'other_zero_edge_orbits_excluded': False,
              'height_endpoints_excluded': False, 'seconds': time.monotonic()-started}
    (directory/'c1_opposite_zero.json').write_text(json.dumps(packet, indent=2)+'\n')
    return packet


if __name__ == '__main__':
    if not __debug__:
        raise RuntimeError('run with assertions enabled')
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('output', type=Path)
    result = build(parser.parse_args().output)
    print(json.dumps({'unsat_obligations': len(result['unsat_obligations']),
                      'normalized_determinants': 70, 'parallel_EF_excluded': False,
                      'seconds': result['seconds']}))
