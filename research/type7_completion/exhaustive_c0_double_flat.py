#!/usr/bin/env python3
"""Exclude the negative-core nonparallel double coincidence in C0.

An exact relative estimate normalizes both shrinking diagonals. One
zero-safe four-cell CNF, two circle identities and a divided cap tilt
exclude the whole stated stratum at every interior height order.
"""

import argparse
from itertools import combinations, product
import json
from pathlib import Path

import sympy as s

import exhaustive_c0_collinear as boundary
import exhaustive_c0_double_coincidence as upper
import exhaustive_c0_flat_common as common
import exhaustive_c0_turning as turning
import exhaustive_remaining_axis as axis
import remaining_c0_height_order as metric
import solver_remaining_c1_geometry as geometry
from solver_chambers import write_cnf
from solver_sat import FastSAT

HALF = s.Rational(1, 2)


def relative_lower_checks():
    t, ell, b, h0, length, a, g = s.symbols('t ell b h0 M a g')
    norm, other_norm, dot, z5, horizontal, vertical = s.symbols('R2 S2 dot z5 X05 V05')
    e01 = ell**2-b**2-t*h0**2
    e06 = t*norm+t*t*a*a-t*length*length-t*t*g*g
    e16 = t*norm+(t*a-ell)**2-t*(h0-length)**2-(t*g-b)**2
    polar = ell*a-b*g-h0*length
    assert s.expand(e01+e06-e16-2*t*polar) == 0
    e05 = t*other_norm+z5*z5-t*horizontal**2-vertical**2
    e56 = (t*(norm+other_norm-2*dot)+(t*a-z5)**2
           -t*(-length-horizontal)**2-(t*g-vertical)**2)
    second = dot+a*z5+length*horizontal-g*vertical
    assert s.expand(e05+e06-e56-2*t*second) == 0
    norm_identity = ell**2*norm-(b*length-t*h0*g)**2
    witness = ell**2*(e06/t)+(length**2+t*g*g)*e01 \
        -t*polar*(ell*a+b*g+h0*length)
    assert s.expand(norm_identity-witness) == 0
    coefficient = b*z5/ell-vertical
    rhs = -dot-length*(horizontal+h0*z5/ell)
    assert s.cancel(coefficient*g-rhs-second+z5*polar/ell) == 0
    shifts, _, _ = axis.case_data(1)
    for tri in ((0, 1, 6), (0, 5, 6)):
        i, j, k = tri
        assert tuple(shifts[i, j][a]+shifts[j, k][a]-shifts[i, k][a]
                     for a in (0, 1)) == (0, 0)
    h = s.symbols('h0:8')
    X = geometry.horizontal_displacements(h)
    assert s.expand(X[0, 6]-(h[6]+h[7]-1)) == 0
    assert s.expand(X[0, 1]+X[1, 6]-X[0, 6]) == 0
    assert s.expand(X[0, 5]+X[5, 6]-X[0, 6]) == 0
    return {'finite_polarization_identities': 2,
            'finite_relative_norm_identity': True, 'nonzero_limit_coefficient': '2v'}


def circle_and_tilt_checks():
    u, v, D, p, q, g = s.symbols('u v D p q g')
    lu, lv = 1-2*u, 1-2*v
    r, ss = HALF-p-lu*D, HALF-g-2*v*D
    budget = {D: HALF-p-q-g}
    assert s.expand((r-q-g-2*u*D).subs(budget)) == 0
    assert s.expand((ss-p-q-lv*D).subs(budget)) == 0
    e4, e5, f4, f5 = s.symbols('e4 e5 f4 f5')
    js = (lv*e4-lu*e5)/2-(lv*r+lu*ss)/2+lv*(HALF-p)
    jw = (v*f4-u*f5)/2-(v*r+u*ss)/2+u*(HALF-g)
    first = lu*(ss+e5)-lv*(r+e4)-2*lu*lv*D
    second = v*(r-f4)-u*(ss-f5)-4*u*v*D
    assert s.expand(first+2*js) == 0
    assert s.expand(second+2*jw) == 0

    # The upper virtual direction is now w=-2P2=+e. The same four
    # finite source polarizations as in the positive-core packet give
    # A/2+a2=-h0 after division by the positive diagonal length L.
    h0, h3, eP4, A, G, a2, g2, ell_u = s.symbols('h0 h3 eP4 A G a2 g2 ell_u')
    r1 = A-G+2*h0
    r2 = eP4-ell_u*A/2+h3-ell_u*G/2
    r3 = a2-g2+h0
    r4 = -eP4/2-ell_u*a2/2-h3/2-ell_u*g2/2
    assert s.expand(ell_u*(A+2*a2+2*h0)+r2+2*r4-ell_u*(r1+2*r3)/2) == 0
    half_tangent = s.Symbol('tau')
    cosine = (1-half_tangent**2)/(1+half_tangent**2)
    sine = 2*half_tangent/(1+half_tangent**2)
    assert s.cancel(1-cosine-half_tangent*sine) == 0
    assert s.cancel(half_tangent*(1+cosine)-sine) == 0
    return {'full_circle_source': metric.metric_bindings(), 'core_source': turning.verify(),
            'strict_circle_differences': ['2(1-2u)(1-2v)D', '4uvD'],
            'divided_upper_tilt': '-h0<0', 'half_angle_bindings': 2}


class DoubleVirtual(common.FlatModel):
    """The macro configuration and both separately normalized diagonals."""

    def __init__(self):
        super().__init__('d', 'd', boundary.height_relations())
        self.clauses.append([self.bits((0, 1, 2, 7))[1]])
        # The radii r>=2uD and s>=(1-2v)D are strictly positive.
        for i in (4, 5):
            self.clauses.append(list(self.bits((0, 1, 2, i)))
                                +list(self.bits((0, 1, i, 7))))
        nodes = (2, 4, 5, 7, 8, 9)  # 8=P3/L and 9=P6/M.
        self.virtual = {(i, j): self.new_trit()
                        for i, j in combinations(nodes, 2) if j >= 8}

        def cross(i, j, sign=1):
            if i == j:
                return None
            if i > j:
                return cross(j, i, -sign)
            pair = self.virtual[i, j] if j >= 8 else self.bits((0, 1, i, j))
            return pair if sign > 0 else pair[::-1]

        self.cross = cross
        for w in (8, 9):
            self.clauses.append(list(cross(2, w))+list(cross(7, w)))
        products = {}

        def multiply(left, right):
            key = tuple(sorted((left, right)))
            if key not in products:
                result = self.new_trit()
                products[key] = result
                for a, b, c in product((-1, 0, 1), repeat=3):
                    if a*b != c:
                        self.clauses.append(self.deny(left, a)+self.deny(right, b)
                                            +self.deny(result, c))
            return products[key]

        vectors = {i: s.Matrix(s.symbols(f'x{i} y{i}')) for i in nodes}
        plane_cross = lambda a, b: s.det(s.Matrix.hstack(vectors[a], vectors[b]))
        for i, j, k, l in combinations(nodes, 4):
            assert s.expand(plane_cross(i, j)*plane_cross(k, l)
                            -plane_cross(i, k)*plane_cross(j, l)
                            +plane_cross(i, l)*plane_cross(j, k)) == 0
            self.sumzero((multiply(cross(i, j), cross(k, l)),
                          multiply(cross(i, k, -1), cross(j, l)),
                          multiply(cross(i, l), cross(j, k))))

        u, v, alpha, beta = s.symbols('u v alpha beta')
        heights = (0, HALF, HALF, HALF, u, v, 0, 0)
        projected = {0: None, 1: None, 2: (2, 1), 3: (8, alpha),
                     4: (4, 1), 5: (5, 1), 6: (9, beta), 7: (7, 1)}
        crosses = {pair: s.Symbol('C'+''.join(map(str, pair)))
                   for pair in combinations(nodes, 2)}
        cross_values = {value: plane_cross(*pair) for pair, value in crosses.items()}

        def ci(i, j):
            if projected[i] is None or projected[j] is None:
                return s.Integer(0)
            a, p = projected[i]
            b, q = projected[j]
            if a == b:
                return s.Integer(0)
            return p*q*(1 if a < b else -1)*crosses[tuple(sorted((a, b)))]

        def origin(i, j, k):
            return heights[i]*ci(j, k)-heights[j]*ci(i, k)+heights[k]*ci(i, j)

        points = []
        for i in range(8):
            point = s.zeros(2, 1) if projected[i] is None else \
                projected[i][1]*vectors[projected[i][0]]
            points.append(point.col_join(s.Matrix([heights[i]])))
        count = 0
        for quad in common.QUADS:
            powers = (int({1, 3} <= set(quad)), int({0, 6} <= set(quad)))
            if powers == (0, 0):
                continue
            i, j, k, l = quad
            polynomial = s.expand(origin(j, k, l)-origin(i, k, l)
                                  +origin(i, j, l)-origin(i, j, k))
            direct = s.det(s.Matrix.hstack(*(points[a]-points[i] for a in quad[1:])))
            assert s.expand(direct-polynomial.subs(cross_values)) == 0
            poly = s.Poly(polynomial, alpha, beta)
            assert all(a >= powers[0] and b >= powers[1]
                       for (a, b), coefficient in poly.terms() if coefficient)
            expression = s.expand(polynomial/alpha**powers[0]/beta**powers[1])
            expression = s.expand(expression.subs({alpha: 0, beta: 0}))
            assert not expression.has(alpha, beta, s.zoo, s.nan)
            normalized = self.new_trit()
            forms = [normalized[::-1]]
            for pair, variable in crosses.items():
                coefficient = expression.coeff(variable)
                assert s.Poly(coefficient, u, v).total_degree() <= 1
                corners = [coefficient.subs({u: a, v: b})
                           for a, b in product((0, HALF), repeat=2)]
                if all(value == 0 for value in corners):
                    continue
                sign = 1 if all(value >= 0 for value in corners) else -1
                assert all(sign*value >= 0 for value in corners)
                forms.append(cross(*pair, sign))
            self.sumzero(forms)
            literal = boundary.shared.common.lit(quad)
            self.clauses.extend(([-normalized[0], literal], [-normalized[1], -literal]))
            count += 1
        assert count == 29
        self.normalized_brackets = count


def build(directory):
    directory.mkdir(parents=True, exist_ok=True)
    checks = {'upper_relative': upper.metric_checks(),
              'lower_relative': relative_lower_checks(), 'circle_and_tilt': circle_and_tilt_checks()}
    model = DoubleVirtual()
    c24, c25, c45, c47, c57 = [model.bits((0, 1)+pair)
                               for pair in ((2, 4), (2, 5), (4, 5), (4, 7), (5, 7))]
    ds, dw = model.bits((2, 3, 4, 5)), model.bits((4, 5, 6, 7))
    w2, w7 = model.cross(2, 8), model.cross(7, 8)
    # Negate the four complete analytic alternatives. Weak signs are
    # negated by the opposite strict trit; zero is never assigned a sign.
    complement = [[c47[0], c47[1], c24[0]],
                  [c24[0], c25[0], c47[1], c57[1], c45[0], dw[1]],
                  [c24[1], c25[1], c47[1], c57[1], c45[0], ds[1], dw[1]],
                  [-c25[1], w2[0], w2[1], -w7[1],
                   -boundary.shared.common.lit((1, 2, 3, 5))]]
    clauses = model.clauses+complement
    with FastSAT(model.n, clauses) as solver:
        assert solver.check() == -1
    filename = 'c0_double_flat_four_cell_cover.cnf'
    write_cnf(directory/filename, model.n, clauses)
    packet = {'checks': checks, 'normalized_brackets': model.normalized_brackets,
              'analytic_cells': ['positive_f_ray', 'positive_cone_e_f',
                                 'positive_cone_minus_f_e', 'positive_e_virtual_tilt'],
              'unsat_obligations': [{'file': filename, 'variables': model.n,
                                    'clauses': len(clauses)}],
              'excluded': 'interior ray1 C0, P1=P3 and P0=P6, actual C27<0',
              'height_order_restriction': None, 'relative_rate_assumptions': [],
              'remaining_nonparallel_flat_pairs_after_both_orientations': ['bd', 'da'],
              'whole_flat_C0_exclusion_claimed': False}
    (directory/'double_flat.json').write_text(json.dumps(packet, indent=2)+'\n')
    return packet


if __name__ == '__main__':
    if not __debug__:
        raise RuntimeError('run with assertions enabled')
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('output', type=Path)
    result = build(parser.parse_args().output)
    print(json.dumps({'unsat_obligations': len(result['unsat_obligations']),
                      'excluded': result['excluded']}), flush=True)
