#!/usr/bin/env python3
"""Exclude nonparallel cap lines in ray-2 C1 zero-edge orbits EB and ED.

All seven exported CNFs require independent RUP replay. Parallel cap
lines and the other zero-edge strata are outside this package's claim.
"""

import argparse
from functools import lru_cache
from itertools import combinations, product
import json
from pathlib import Path
import time

import sympy as S

import remaining_c1_flat_positive_stretch as signs
import remaining_c1_one_collinear as one_collinear
import remaining_c1_sections as sections
import remaining_c1_short_edges as short_edges
import solver_remaining_c1_collinear as trits
import solver_remaining_chambers as shared
from solver_chambers import write_cnf
from solver_sat import FastSAT

A, B, L = signs.A, signs.B, signs.X
HALF = S.Rational(1, 2)
NODES = tuple(range(4))  # P3, U=P4-P3, V=half the lower unit vector, R5
PAIRS = tuple(combinations(NODES, 2))
PATTERNS = {
    ('B', 1): ((1, -1, -1, 1, 1, 0),),
    ('D', -1): ((1, 0, 0, 1, -1, 0),),
    ('D', 1): ((1, 0, 0, 1, 0, 0), (0, -1, 1, 1, -1, -1)),
}


def source_and_metric_checks():
    a, b, ell, c, r, rho, d = S.symbols('a b ell c r rho d')
    q = 1-b
    m = HALF-r-ell
    # In EB, R=2 rho V, so the two dot identities give these equations.
    h4, h5 = HALF-d, HALF-r-ell+d
    rho_definition = b*(HALF-h4)+(1-b)*h5
    sigma = (1-b)*(1-h5)+b*h4
    assert S.expand(rho_definition-d-q*m) == 0
    first = d-rho*(1+c)/2
    radius = rho-rho_definition
    assert S.expand(2*(first+radius)-(rho*(1-c)-2*q*m)) == 0
    lower = ell*(b*c/2-rho+sigma)-(r+ell-d)
    # On the radius equation, sigma=1-b/2-rho.
    closed_lower = ell*(1-b*(1-c)/2-2*rho)-(r+ell-d)
    assert S.expand(lower-closed_lower-ell*radius) == 0
    assert S.expand(2*(closed_lower-first)
                    -(rho*(1+c-4*ell)-b*ell*(1-c)-2*r)) == 0

    denominator = 2-b*(1+c)-4*q*ell
    assert S.expand(denominator-b*(1-c)-2*q*(1-2*ell)) == 0
    radius_value = q*(1-2*ell+b*ell*(1-c))/denominator
    r_value = HALF-ell-radius_value*(1-c)/(2*q)
    assert S.cancel(radius_value*(1+c-4*ell)-b*ell*(1-c)-2*r_value) == 0
    z = (1-c)/2
    gap = 8*q*ell*(1-2*ell)+4*b*z*(1-(1-2*ell)*z)
    assert S.cancel(4*denominator*((1+c)/4-r_value)-gap) == 0

    # Exact endpoint values for the concave function giving cone1^2.
    r_min = a*(1+c)/(2*((1+a)-(1-a)*c))
    r_max = (1+c)/4
    function = 16*r*(HALF-r)/(a*(1-c*c))
    first_radius = a/2+(1-a)*r
    first_projection = (1+a)*r-a/2
    assert S.expand(first_radius**2-first_projection**2-4*a*r*(HALF-r)) == 0
    cone_x, cone_y = S.symbols('cone_x cone_y')
    first_norm_squared = a*a*(cone_x**2+cone_y**2+2*cone_x*cone_y*c)/4
    first_projection_in_cone = -a*(cone_x*c+cone_y)/2
    assert S.expand(first_norm_squared-first_projection_in_cone**2
                    -a*a*cone_x**2*(1-c*c)/4) == 0
    assert S.cancel(a*a*(1-c*c)*function/4-4*a*r*(HALF-r)) == 0
    assert S.cancel(r_max-r_min-(1-a)*(1-c*c)/(4*((1+a)-(1-a)*c))) == 0
    rho_min = a/2+(1-a)*r_min
    assert S.cancel(function.subs(r, r_min)-(2*rho_min/a)**2) == 0
    assert S.cancel(function.subs(r, r_max)-1/a) == 0
    assert S.cancel(S.diff(function, r, 2)+32/(a*(1-c*c))) == 0

    # ED: P=-anchor*U and |aP|=a/2+(1-a)r.
    anchor = (a+2*(1-a)*r)/a
    assert S.cancel(anchor-1-2*(1-a)*r/a) == 0
    # The collinear first-circle boundary has exactly two endpoints.
    k, p = S.symbols('k p')
    rr = HALF-(1-a)*p
    projection = p/k-(HALF+(1-a)*p)
    assert S.factor(rr**2-projection**2
                    -p*(k-p)*(1-2*(1-a)*k)/k**2) == 0
    assert S.cancel(projection.subs(p, 0)+rr.subs(p, 0)) == 0
    assert S.cancel(projection.subs(p, k)-rr.subs(p, k)) == 0

    # Equal-height B has the repeated pair B1=B2. A has four positive
    # edges, and its distinguished vertex A1 cannot be flat.
    triangle = (S.zeros(2, 1), S.Matrix([1, 0]), S.Matrix([0, -1]))
    bb = [triangle[0], triangle[1], triangle[1], triangle[2]]
    fraction = S.Symbol('fraction')
    matches = []
    for flat, rotation in product((0, 2, 3), range(3)):
        aa = [None]*4
        for index, vertex in enumerate(i for i in range(4) if i != flat):
            aa[vertex] = triangle[(index+rotation) % 3]
        aa[flat] = (1-fraction)*aa[(flat-1) % 4]+fraction*aa[(flat+1) % 4]
        closure = aa[0]+aa[2]-aa[3]-bb[1]+bb[2]-bb[3]
        solutions = list(S.linsolve(list(closure), (fraction,)))
        assert not solutions or solutions in ([(S.Integer(0),)], [(S.Integer(1),)])
        matches.append({'flat_A': flat, 'rotation': rotation,
                        'solutions': [[str(value) for value in row] for row in solutions]})
    return {'original_section_source': sections.section_checks(),
            'general_zero_edge_spur_source': one_collinear.zero_edge_spur_checks(),
            'strict_corner_source': sections.metric_checks(),
            'equal_height_triangle_matches': matches,
            'EB_radius_and_two_dot_source_checks': True,
            'EB_strict_height_gap_decomposition': str(gap),
            'EB_concave_cone_coefficient_checks': True,
            'EB_cone_coefficient_Gram_binding': True,
            'ED_anchor_bound_and_closed_circle_endpoints': True}


@lru_cache(maxsize=None)
def normalized_forms(order, eta):
    assert order in ('B', 'D') and eta in (-1, 1)
    h, t, axial = S.symbols('h t axial23')
    k, ell, direction = (HALF, L, 1) if order == 'B' else (L, HALF-L, -1)
    crosses = {pair: S.Symbol('C%d%d' % pair) for pair in PAIRS}
    vectors = [{}, {}, {0: 1, 1: -2*eta*h}, {0: 1}, {0: 1, 1: 1},
               {0: B, 2: 2*(1-B)*(k-direction*ell), 3: 1},
               {2: 2*(k-direction*ell)}, {2: 2*k}]
    heights = (0, A/2, HALF-t*h*axial, HALF, HALF, B/2, 0, 0)

    def cross(i, j):
        return sum(x*y*(1 if a < b else -1)*crosses[tuple(sorted((a, b)))]
                   for a, x in vectors[i].items() for b, y in vectors[j].items() if a != b)

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
        divided = S.cancel(polynomial/(h if {2, 3} <= set(quad) else 1))
        assert h not in S.denom(divided).free_symbols
        edge_limit = S.expand(divided.subs(h, 0))
        expression = S.expand(edge_limit.subs(t, 0))
        coefficients = {pair: expression.coeff(variable) for pair, variable in crosses.items()}
        assert S.expand(expression-sum(coefficients[pair]*variable
                                      for pair, variable in crosses.items())) == 0
        records.append((quad, coefficients))
    return tuple(records)


class NormalizedModel(trits.ActualBracketModel):
    def __init__(self, order, eta):
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
                    self.clauses.append(self.deny(left, x)+self.deny(right, y)+self.deny(result, z))
            return result

        self.sumzero((multiply(cross(0, 1), cross(2, 3)),
                      multiply(cross(0, 2, -1), cross(1, 3)),
                      multiply(cross(0, 3), cross(1, 2))))
        self.omitted = []
        for quad, coefficients in normalized_forms(order, eta):
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
        assert len(self.omitted) == (1 if order == 'B' else 0)
        self.clauses.append([cross(1, 2)[0]])  # oriented independent U,V
        self.clauses.append(list(cross(0, 1))+list(cross(0, 2)))  # |P|>0


class FactorModel(trits.ActualBracketModel):
    def __init__(self, order):
        x, y, z = S.symbols('cone1 cone2 radius')
        self.n, base, *_ = shared.base_formula()
        assert base[0] == [1]
        self.clauses = [list(row) for row in base[1:]]
        self.trits, self.factors = {}, {}
        if order == 'B':
            # P=-xU-yV, R=zV; x>1 and y,z>0.
            crosses = {(0, 1): y, (0, 2): -x, (0, 3): -x*z,
                       (1, 2): 1, (1, 3): z, (2, 3): 0}
        else:
            # P=-xU, R=yU-zV; x>1 and y,z>0.
            crosses = {(0, 1): 0, (0, 2): -x, (0, 3): x*z,
                       (1, 2): 1, (1, 3): -z, (2, 3): -y}

        def factor_sign(polynomial):
            if polynomial == x-1:
                return 1
            coefficient_signs = set()
            for _, coefficient in S.Poly(polynomial, x, y, z).terms():
                sign = signs.coefficient_sign(coefficient)
                if sign is None:
                    return None
                if sign:
                    coefficient_signs.add(sign)
            return (next(iter(coefficient_signs)) if len(coefficient_signs) == 1
                    else 0 if not coefficient_signs else None)

        def multiply(left, right):
            result = self.new_trit()
            for a, b, c in product((-1, 0, 1), repeat=3):
                if a*b != c:
                    self.clauses.append(self.deny(left, a)+self.deny(right, b)+self.deny(result, c))
            return result

        self.records = []
        for quad, coefficients in normalized_forms(order, 1):
            polynomial = S.factor(sum(coefficient*crosses[pair]
                                      for pair, coefficient in coefficients.items()))
            self.records.append({'quad': quad, 'polynomial': str(polynomial)})
            constant, factors = S.factor_list(polynomial)
            sign, unknown = int(S.sign(constant)), []
            if not sign:
                continue
            assert S.expand(polynomial-constant*S.prod(factor**power for factor, power in factors)) == 0
            for factor, power in factors:
                known = factor_sign(factor)
                if known is not None:
                    sign *= known**power
                else:
                    assert power == 1
                    if factor not in self.factors:
                        self.factors[factor] = self.new_trit()
                    unknown.append(self.factors[factor])
            literal = shared.common.lit(quad)
            if not unknown:
                self.clauses.append([sign*literal])
            else:
                bits = unknown[0]
                for pair in unknown[1:]:
                    bits = multiply(bits, pair)
                self.clauses.extend(([-bits[0], sign*literal], [-bits[1], -sign*literal]))
        if order == 'B':
            first = -A*y+2*A*L-A-2*L+1
            second = A*y+A-1
            assert S.expand(first+second-2*L*(A-1)) == 0
            self.clauses.append([self.factors[first][1], self.factors[second][1]])
        assert len(self.factors) == (7 if order == 'B' else 8)


def zero_radius_model():
    """The last ED endpoint has P=-V/alpha and R=0."""
    n, base, *_ = shared.base_formula()
    assert base[0] == [1]
    clauses = [list(row) for row in base[1:]]
    crosses = {(0, 1): 1, (0, 2): 0, (0, 3): 0,
               (1, 2): A, (1, 3): 0, (2, 3): 0}
    omitted, units = [], []
    for quad, coefficients in normalized_forms('D', 1):
        polynomial = S.factor(sum(coefficient*crosses[pair]
                                  for pair, coefficient in coefficients.items()))
        constant, factors = S.factor_list(polynomial)
        sign = int(S.sign(constant))
        for factor, power in factors:
            known = signs.coefficient_sign(factor)
            if known is None:
                omitted.append(quad)
                break
            sign *= known**power
        else:
            if sign:
                literal = int(sign*shared.common.lit(quad))
                clauses.append([literal])
                units.append(literal)
    assert len(omitted) == 2
    return n, clauses, units, omitted


def build(directory):
    started = time.monotonic()
    directory.mkdir(parents=True, exist_ok=True)
    checks = source_and_metric_checks()
    relative = short_edges.relative_metric_checks()
    obligations = []

    def export(filename, n, clauses, claim, **extra):
        with FastSAT(n, clauses) as solver:
            assert solver.check() == -1, filename
        write_cnf(directory/filename, n, clauses)
        obligations.append({'file': filename, 'claim': claim,
                            'variables': n, 'clauses': len(clauses), **extra})

    for order, eta in product(('B', 'D'), (-1, 1)):
        model = NormalizedModel(order, eta)
        if (order, eta) == ('B', -1):
            extra = []
            claim = 'the negative virtual direction in EB is impossible'
        else:
            patterns = PATTERNS[order, eta]
            extra = [sum((model.deny(model.crosses[pair], sign)
                          for pair, sign in zip(PAIRS, pattern)), []) for pattern in patterns]
            claim = 'the six actual cross signs lie in the displayed complete cover'
        export(f'c1_single_zero_{order}_{eta}_cover.cnf', model.n,
               model.clauses+extra, claim, patterns=PATTERNS.get((order, eta), ()),
               omitted_variable_sign_relations=model.omitted)
    factor_records = {}
    for order in ('B', 'D'):
        model = FactorModel(order)
        # Deterministic order only: the source ordering elicited a
        # non-RUP Z3 trace in ED. Reversal preserves every clause and
        # lets the unchanged independent checker accept the new trace.
        clauses = model.clauses if order == 'B' else list(reversed(model.clauses))
        export(f'c1_single_zero_{order}_factors.cnf', model.n, clauses,
               'the remaining cone pattern with first coefficient greater than one is impossible')
        factor_records[order] = {'free_factors': [str(value) for value in model.factors],
                                 'determinants': model.records}
    n, clauses, units, omitted = zero_radius_model()
    export('c1_single_zero_D_zero_radius.cnf', n, clauses,
           'the zero-radius ED endpoint is impossible', strict_normalized_minors=units,
           omitted_variable_sign_minors=omitted)
    packet = {'domain': 'ray2 C1; upper E; lower B or D; nonparallel cap lines; interior heights',
              'source_checks': checks, 'relative_short_edge_source': relative,
              'normalized_determinants_per_case': 70, 'factor_records': factor_records,
              'unsat_obligations': obligations, 'relative_rate_assumptions': [],
              'parallel_EB_ED_excluded': False, 'height_endpoints_excluded': False,
              'seconds': time.monotonic()-started}
    (directory/'c1_single_zero_nonparallel.json').write_text(json.dumps(packet, indent=2)+'\n')
    return packet


if __name__ == '__main__':
    if not __debug__:
        raise RuntimeError('run with assertions enabled')
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('output', type=Path)
    result = build(parser.parse_args().output)
    print(json.dumps({'unsat_obligations': len(result['unsat_obligations']),
                      'nonparallel_EB_ED_excluded': True,
                      'parallel_EB_ED_excluded': False, 'seconds': result['seconds']}))
