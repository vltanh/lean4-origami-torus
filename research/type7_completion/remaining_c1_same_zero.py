#!/usr/bin/env python3
"""Exclude the interior parameter of the ray-2 C1 EE zero-edge orbit.

The domain is h2=h6=0 and 0<h0<1/2, with both height parameters
interior. Five exported CNFs need independent RUP replay. The two
scalar endpoints h0=0,1/2 remain outside this exclusion.
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
import remaining_c1_zero_common as zero_common
import solver_remaining_c1_collinear as trits
import solver_remaining_chambers as shared
from solver_chambers import write_cnf
from solver_sat import FastSAT


A, B = signs.A, signs.B
HALF = S.Rational(1, 2)
NODES = tuple(range(4))  # P3, U=P4-P3, V=P6=P7, R5
PAIRS = tuple(combinations(NODES, 2))
REMAINING_PATTERN = (0, 1, -1, -1, 1, 1)


def section_checks():
    """Bind both triangle-plus-segment limits and their line identities."""
    source = sections.section_checks()
    p, u, v, r = [S.Matrix(S.symbols(f'{name}x {name}y'))
                  for name in ('P', 'U', 'V', 'R')]
    t = S.Symbol('section_t')
    p5 = B*p+(1-B)*v+r
    s = (t-A)/(1-A)
    h, j = s*p, s*(p+u)
    high_b = [t*p, t*p, (1-t)*v+t*p, h, j, h]
    lam = (1-t)/(1-A)
    triangle_b = [h, h+lam*A*p, h+lam*(A*p+(1-A)*v)]
    for actual, expected in zip(triangle_b,
                                (high_b[3], high_b[0], high_b[2])):
        sections.equal_vectors(actual, expected)
    x, y = (1-t)*v+t*p, (1-t)*v+t*(p+u)
    j3 = (1-t)/(1-B)*p5+(t-B)/(1-B)*p
    j4 = (1-t)/(1-B)*p5+(t-B)/(1-B)*(p+u)
    sections.equal_vectors(y-x, t*u)
    sections.equal_vectors(j4-j3, (t-B)/(1-B)*u)
    sections.equal_vectors(j3-x, (1-t)/(1-B)*r)

    corner = (1-t/B)*v+t/B*p5
    end = t/B*p5
    low_a = [x, corner, end, corner, y, y]
    assert low_a[1] == low_a[3]
    assert low_a[4] == low_a[5]
    # Its triangle converges to V and its backtracked segment to [V,0].
    assert all(point.subs(t, 0) == v for point in (x, corner, y))
    assert end.subs(t, 0) == S.zeros(2, 1)
    low_b = [t*p, t*p, (1-t)*v+t*p,
             (1-t/A)*v, (1-t/A)*v, S.zeros(2, 1)]
    sections.equal_vectors(low_b[2]-low_b[1], (1-t)*v)
    sections.equal_vectors(low_b[3]-low_b[5], (1-t/A)*v)
    # Bind the specialized lists themselves, not only the imported
    # generic section identities, to their original edge intersections.
    high_a = [x, j3, j3, j4, y, y]
    points = [S.zeros(2, 1), S.zeros(2, 1), p, p, p+u, p5, v, v]
    heights = (0, A, 1, 1, 1, B, 0, 0)
    edge_cycles = (
        ((0, 3), (0, 2), (2, 7), (1, 7), (1, 6), (0, 1)),
        ((0, 3), (0, 2), (2, 7), (1, 2), (1, 4), (1, 3)),
        ((3, 6), (5, 6), (0, 5), (5, 7), (4, 7), (4, 6)),
        ((3, 6), (3, 5), (2, 5), (4, 5), (4, 7), (4, 6)),
    )
    _, _, original_faces, *_ = shared.base_formula()
    face_set = {tuple(sorted(face)) for face in original_faces}
    specialized_faces = set()
    for polygon, edges in zip((low_b, high_b, low_a, high_a), edge_cycles):
        for index, (point, (i, j0)) in enumerate(zip(polygon, edges)):
            sections.equal_vectors(point, points[i]+(t-heights[i])/(heights[j0]-heights[i])
                                   *(points[j0]-points[i]))
            face = tuple(sorted(set(edges[index]) | set(edges[(index+1) % 6])))
            assert len(face) == 3 and face in face_set
            specialized_faces.add(face)
    assert specialized_faces == face_set
    return {'original_section_source': source,
            'specialized_edge_intersection_bindings': 24,
            'specialized_source_faces': len(specialized_faces),
            'upper_outer_triangle_and_backtracked_segment': True,
            'lower_outer_triangle_and_backtracked_segment': True,
            'supporting_line_contradictions': ['R5 parallel U', 'P3 parallel V'],
            'strict_Gram_identities': zero_common.scalar_checks()}


@lru_cache(maxsize=None)
def normalized_forms(eta, theta):
    """All seventy signs, with independent h2 and h6 normalizations.

    The virtual unit directions are 2 eta U and 2 theta V. The formal
    O(t h) axial errors are retained before the edge factors are divided.
    """
    assert eta in (-1, 1) and theta in (-1, 1)
    h, k, t, aa, cc = S.symbols('h k t axial23 axial67')
    crosses = {pair: S.Symbol('C%d%d' % pair) for pair in PAIRS}
    vectors = [{}, {}, {0: 1, 1: -2*eta*h}, {0: 1}, {0: 1, 1: 1},
               {0: B, 2: 1-B, 3: 1}, {2: 1}, {2: 1+2*theta*k}]
    heights = (0, A/2, HALF-t*h*aa, HALF, HALF, B/2, 0, t*k*cc)

    def cross(i, j):
        return sum(x*y*(1 if a < b else -1)*crosses[tuple(sorted((a, b)))]
                   for a, x in vectors[i].items()
                   for b, y in vectors[j].items() if a != b)

    def origin(i, j, k0):
        return heights[i]*cross(j, k0)-heights[j]*cross(i, k0)+heights[k0]*cross(i, j)

    coordinate_vectors = {i: S.Matrix(S.symbols(f'x{i} y{i}')) for i in NODES}
    points = [sum((value*coordinate_vectors[node] for node, value in vector.items()),
                  S.zeros(2, 1)).col_join(S.Matrix([height]))
              for vector, height in zip(vectors, heights)]
    substitution = {variable: S.det(S.Matrix.hstack(coordinate_vectors[i], coordinate_vectors[j]))
                    for (i, j), variable in crosses.items()}
    records = []
    for quad in trits.QUADS:
        i, j, k0, l = quad
        polynomial = S.expand(origin(j, k0, l)-origin(i, k0, l)
                              +origin(i, j, l)-origin(i, j, k0))
        direct = S.det(S.Matrix.hstack(*(points[v]-points[i] for v in quad[1:])))
        assert S.expand(polynomial.subs(substitution)-direct) == 0
        first, second = {2, 3} <= set(quad), {6, 7} <= set(quad)
        divisor = (h if first else 1)*(k if second else 1)
        divided = S.cancel(polynomial/divisor)
        assert S.denom(divided).free_symbols.isdisjoint({h, k})
        edge_limit = S.expand(divided.subs({h: 0, k: 0}))
        expression = S.expand(edge_limit.subs(t, 0))
        assert S.expand(edge_limit-expression).subs(t, 0) == 0
        coefficients = {pair: expression.coeff(variable) for pair, variable in crosses.items()}
        assert S.expand(expression-sum(coefficients[pair]*variable
                                      for pair, variable in crosses.items())) == 0
        records.append((quad, coefficients, int(first)+int(second)))
    assert len(records) == 70
    assert sum(degree == 2 for _, _, degree in records) == 1
    return tuple(records)


class NormalizedModel(trits.ActualBracketModel):
    def __init__(self, eta, theta):
        self.n, base, *_ = shared.base_formula()
        assert base[0] == [1]
        self.clauses = [list(row) for row in base[1:]]
        self.trits = {}
        self.crosses = {pair: self.new_trit() for pair in PAIRS}

        def cross(i, j, sign=1):
            if i > j:
                return cross(j, i, -sign)
            bits = self.crosses[i, j]
            return bits if sign > 0 else bits[::-1]

        def multiply(left, right):
            result = self.new_trit()
            for x, y, z in product((-1, 0, 1), repeat=3):
                if x*y != z:
                    self.clauses.append(self.deny(left, x)+self.deny(right, y)
                                        +self.deny(result, z))
            return result

        self.sumzero((multiply(cross(0, 1), cross(2, 3)),
                      multiply(cross(0, 2, -1), cross(1, 3)),
                      multiply(cross(0, 3), cross(1, 2))))
        for quad, coefficients, _ in normalized_forms(eta, theta):
            bits = self.new_trit()
            self.trits[quad] = bits
            literal = shared.common.lit(quad)
            self.clauses.extend(([-bits[0], literal], [-bits[1], -literal]))
            terms = [bits[::-1]]
            for pair, coefficient in coefficients.items():
                sign = signs.coefficient_sign(coefficient)
                assert sign is not None
                if sign:
                    terms.append(cross(*pair, sign))
            self.sumzero(terms)
        # Both are nonzero by the strict Gram identities. Ambient
        # orientation can and is chosen to make the first positive.
        self.clauses.append([cross(0, 2)[0]])
        self.clauses.append(list(cross(1, 3)))


def metric_crosses():
    """Resolve the surviving orientation with the two exact circles."""
    q, k = S.symbols('q k')
    r = k/(2*(1+k))
    rho = A/2+(1-A)*r
    rho5 = B*r+(1-B)/2
    projection = A/2-(1+A)*r
    # U=(1/2,0), P=-rho/A, V_y<0, R_y>0. Divide the
    # second coordinate by g=2 sqrt(A r(1/2-r))>0.
    points = [S.Matrix([-rho/A, 0]), S.Matrix([HALF, 0]),
              S.Matrix([-projection/(2*rho), -1/(2*rho)]),
              S.Matrix([2*r-rho5, q])]
    # q^2=(1-beta)/alpha. The positive common cross-product multiplier
    # is 4 alpha rho (1+k)^2 after the transverse change above.
    scale = 4*A*rho*(1+k)**2
    values = {pair: S.factor((scale*S.det(S.Matrix.hstack(points[pair[0]], points[pair[1]])))
                             .subs(B, 1-A*q*q)) for pair in PAIRS}
    expected = {(0, 1): 0, (0, 2): (A+k)*(1+k),
                (0, 3): -(A+k)**2*q, (1, 2): -A*(1+k)**2,
                (1, 3): A*(A+k)*q*(1+k),
                (2, 3): A*(1+q)*(k-A*q)*(1+k)}
    assert all(S.cancel(values[pair]-expected[pair]) == 0 for pair in PAIRS)
    assert S.cancel(rho-(A+k)/(2*(1+k))) == 0
    return q, k, expected


class FactorModel(trits.ActualBracketModel):
    """Keep identical polynomial factors coupled, including their zeros."""

    def __init__(self):
        q, k, crosses = metric_crosses()
        self.n, base, *_ = shared.base_formula()
        assert base[0] == [1]
        self.clauses = [list(row) for row in base[1:]]
        self.trits, self.factors = {}, {}
        # k>alpha q follows from the strictly positive C23 in the
        # normalized sign cover. No other sign is imposed on a
        # polynomial whose sign can vary in the parameter domain.
        known = {A: 1, q: 1, k: 1, A+k: 1, A-1: -1, k+1: 1,
                 q+1: 1, A*q+1: 1, A*q-k: -1, A*q-k-q-1: -1}
        assert S.expand(A*q-k-q-1-((A-1)*q-k-1)) == 0
        records = []
        for quad, coefficients, _ in normalized_forms(1, -1):
            polynomial = S.factor(sum(coefficient*crosses[pair]
                                      for pair, coefficient in coefficients.items()).subs(B, 1-A*q*q))
            constant, factors = S.factor_list(polynomial)
            sign, unknown = int(S.sign(constant)), []
            if not sign:
                records.append({'quad': quad, 'polynomial': '0'})
                continue
            assert S.expand(polynomial-constant*S.prod(factor**power for factor, power in factors)) == 0
            for factor, power in factors:
                if factor in known:
                    sign *= known[factor]**power
                elif -factor in known:
                    sign *= (-known[-factor])**power
                else:
                    assert power == 1
                    if factor not in self.factors:
                        self.factors[factor] = self.new_trit()
                    unknown.append(self.factors[factor])
            literal = shared.common.lit(quad)
            if not unknown:
                self.clauses.append([sign*literal])
            else:
                assert len(unknown) == 1
                positive, negative = unknown[0]
                self.clauses.extend(([-positive, sign*literal], [-negative, -sign*literal]))
            records.append({'quad': quad, 'polynomial': str(polynomial)})
        assert len(self.factors) == 5
        self.records = records


def build(directory):
    started = time.monotonic()
    directory.mkdir(parents=True, exist_ok=True)
    source_checks = section_checks()
    relative = short_edges.relative_metric_checks()
    obligations = []

    def export(filename, model, claim, extra_clauses=()):
        clauses = model.clauses+list(extra_clauses)
        with FastSAT(model.n, clauses) as solver:
            assert solver.check() == -1, filename
        write_cnf(directory/filename, model.n, clauses)
        obligations.append({'file': filename, 'claim': claim,
                            'variables': model.n, 'clauses': len(clauses)})

    for eta, theta in ((-1, -1), (-1, 1), (1, 1)):
        model = NormalizedModel(eta, theta)
        export(f'c1_same_zero_direction_{eta}_{theta}.cnf', model,
               f'the parallel virtual directions ({eta},{theta}) are impossible')
    model = NormalizedModel(1, -1)
    violation = sum((model.deny(model.crosses[pair], sign)
                     for pair, sign in zip(PAIRS, REMAINING_PATTERN)), [])
    export('c1_same_zero_remaining_pattern.cnf', model,
           'the remaining parallel directions force the six exact cross signs', [violation])
    factors = FactorModel()
    export('c1_same_zero_metric_factors.cnf', factors,
           'the remaining cross pattern contradicts the exact two-circle factors')
    packet = {'domain': 'ray2 C1; h2=h6=0; 0<h0<1/2; 0<alpha,beta<1',
              'source_checks': source_checks, 'relative_short_edge_source': relative,
              'normalized_determinants_per_direction': 70,
              'independent_double_normalization': [2, 3, 6, 7],
              'remaining_cross_pairs': PAIRS, 'remaining_cross_signs': REMAINING_PATTERN,
              'metric_factor_polynomials': [str(factor) for factor in factors.factors],
              'factored_normalized_determinants': factors.records,
              'unsat_obligations': obligations, 'relative_rate_assumptions': [],
              'scalar_EE_endpoints_excluded': False, 'height_endpoints_excluded': False,
              'seconds': time.monotonic()-started}
    (directory/'c1_same_zero.json').write_text(json.dumps(packet, indent=2)+'\n')
    return packet


if __name__ == '__main__':
    if not __debug__:
        raise RuntimeError('run with assertions enabled')
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('output', type=Path)
    result = build(parser.parse_args().output)
    print(json.dumps({'unsat_obligations': len(result['unsat_obligations']),
                      'EE_interior_excluded': True, 'scalar_EE_endpoints_excluded': False,
                      'seconds': result['seconds']}))
