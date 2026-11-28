#!/usr/bin/env python3
"""Exclude the last nonparallel both-flat ray-1 C0 orders bd and da.

One independently normalized diagonal, a three-cell exact sign cover,
two strict circle differences and the upper-b cap tilt close bd.
The checked marked reflection closes da. Every height order is kept.
"""

import argparse
from itertools import combinations, product
import json
from pathlib import Path

import sympy as s

import exhaustive_c0_collinear as boundary
import exhaustive_c0_double_flat as double
import exhaustive_c0_flat_common as common
import exhaustive_c0_turning as turning
import remaining_c0_height_order as metric
import solver_remaining_c1_geometry as geometry
import solver_remaining_limit as reduction
from solver_chambers import write_cnf
from solver_sat import FastSAT

HALF = s.Rational(1, 2)


def metric_checks():
    u, v, length = s.symbols('u v L')
    lu, hh = 1-2*u, HALF-length
    d = list(s.symbols('d0:8'))
    d[1], d[2], d[6], d[7] = length, s.Integer(0), s.Integer(0), s.Integer(0)
    d[5] = HALF-sum(d[:5])
    D = d[0]+length
    h = [HALF-value for value in d]
    points = [s.zeros(2, 1), s.zeros(2, 1), s.Matrix([-hh, 0]),
              s.Matrix([length, 0])]
    points += [s.Matrix(s.symbols(f'x{i} y{i}')) for i in range(4, 8)]
    X = geometry.horizontal_displacements(h)
    residuals = []
    for i, j in reduction.EDGES:
        delta = points[j]-points[i]
        residuals.append(s.expand(delta.dot(delta)-X[i, j]**2))
    matrix = reduction.original_system((HALF, HALF, HALF, 1-u, -v, 0))
    equations = s.Matrix(residuals+[0]*5)+matrix*s.Matrix(reduction.AUXILIARIES)

    def eq(edge):
        return equations[reduction.EDGES.index(edge)]

    H = reduction.H
    q14, q24 = reduction.QMAP[1, 4], reduction.QMAP[2, 4]
    intrinsic_tilt = (length*q24-HALF*q14)/(2*lu)
    correction = hh*H[3]+length*H[2]-HALF*H[1]
    tilt = intrinsic_tilt+correction
    witness = lu*(hh*eq((0, 3))+length*eq((0, 2))-HALF*eq((0, 1))) \
        -HALF*eq((1, 4))+length*eq((2, 4))+hh*eq((3, 4))
    assert s.cancel(2*lu*(tilt+length*(HALF-D))-witness) == 0

    # The common core row gives d0=hh*(1-e.f)/2. Thus D<1/2
    # whenever the cap lines are nonparallel, in either orientation.
    cosine = s.Symbol('cosine')
    core = (-X[0, 1]**2-(hh**2-X[0, 2]**2)
            -(HALF**2-X[1, 7]**2)
            +(hh**2+HALF**2+hh*cosine-X[2, 7]**2))
    assert s.expand(core-2*(d[0]-hh*(1-cosine)/2)) == 0
    assert s.expand((HALF-D-hh*(1+cosine)/2).subs(d[0], hh*(1-cosine)/2)) == 0

    # Bounded product variables bound all three intrinsic cap rates.
    t, g1, g2, g3 = s.symbols('t gamma1 gamma2 gamma3')
    lifts = [0, HALF+t*g1, HALF+t*g2, HALF+t*g3, 1-u, -v, t*g3, 0]
    products = reduction.axis.product_polynomials(lifts)
    assert s.expand(products[0, 5]/t-4*v*g3-4*t*g3*g3) == 0
    assert s.expand(products[1, 4]/t-2*lu*(g1-g3)+4*t*g3*(g1-g3)) == 0
    assert s.expand(products[2, 4]/t-2*lu*(g2-g3)+4*t*g3*(g2-g3)) == 0
    assert s.cancel(hh*(g3-g1)+length*(g2-g1)-intrinsic_tilt.subs(
        {q14: 2*lu*(g1-g3), q24: 2*lu*(g2-g3)})) == 0

    # Exact finite determinant, followed only then by the upper-b limit.
    z1, z5, a2, a3, gamma, c25 = s.symbols('z1 z5 a2 a3 Gamma C25')
    P2, P3, P5 = [s.Matrix(s.symbols(f'P{i}x P{i}y')) for i in (2, 3, 5)]
    cross = lambda a, b: s.det(s.Matrix.hstack(a, b))
    B, C25, C35 = cross(P2, P3), cross(P2, P5), cross(P3, P5)
    determinant = s.det(s.Matrix.hstack(P2.col_join(s.Matrix([t*a2])),
                                        P3.col_join(s.Matrix([t*a3])),
                                        P5.col_join(s.Matrix([z5-z1]))))
    assert s.expand(determinant-(z5-z1)*B-t*(a2*C35-a3*C25)) == 0
    assert s.cancel((-length*a2/hh-a3)*c25+(hh*a3+length*a2)*c25/hh) == 0
    return {'full_circle_source': metric.metric_bindings(),
            'full_core_source': turning.verify(),
            'circle_specializations': double.circle_and_tilt_checks()['strict_circle_differences'],
            'upper_b_tilt_source_identity': '-L*(1/2-D)<0',
            'bounded_intrinsic_rate_bindings': 3,
            'finite_determinant_identity': True,
            'relative_lower': double.relative_lower_checks(),
            'marked_reflection': boundary.symmetry_checks()}


class AsymmetricVirtual(common.FlatModel):
    """Upper b, lower coincidence, and the separately normalized 06."""

    def __init__(self):
        super().__init__('b', 'd', boundary.height_relations())
        self.clauses.append(list(self.bits((0, 1, 2, 7))))
        nodes = (2, 4, 5, 7, 9)  # Q2=-E, Q4, Q5, Q7=F, z=P6/M.
        self.virtual = {(i, 9): self.new_trit() for i in nodes[:-1]}

        def cross(i, j, sign=1):
            if i == j:
                return None
            if i > j:
                return cross(j, i, -sign)
            pair = self.virtual[i, j] if j == 9 else self.bits((3, 6, i, j), -1)
            return pair if sign > 0 else pair[::-1]

        self.cross = cross
        # The metric radii are positive, and Q2,Q7 are independent.
        for i in (4, 5):
            self.clauses.append(list(cross(2, i))+list(cross(i, 7)))
        self.clauses.append(list(cross(2, 9))+list(cross(7, 9)))
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
        plane_cross = lambda i, j: s.det(s.Matrix.hstack(vectors[i], vectors[j]))
        for i, j, k, l in combinations(nodes, 4):
            assert s.expand(plane_cross(i, j)*plane_cross(k, l)
                            -plane_cross(i, k)*plane_cross(j, l)
                            +plane_cross(i, l)*plane_cross(j, k)) == 0
            self.sumzero((multiply(cross(i, j), cross(k, l)),
                          multiply(cross(i, k, -1), cross(j, l)),
                          multiply(cross(i, l), cross(j, k))))

        length, u, v, beta = s.symbols('L u v beta')
        heights = (0, HALF, HALF, HALF, u, v, 0, 0)
        coefficients = [{}, {}, {2: 1-2*length}, {2: -2*length},
                        {4: 1, 2: -4*u*length}, {5: 1, 2: -4*v*length},
                        {9: beta}, {7: 1}]
        points = []
        for i, coeff in enumerate(coefficients):
            point = sum((value*vectors[j] for j, value in coeff.items()), s.zeros(2, 1))
            points.append(point.col_join(s.Matrix([heights[i]])))
        crosses = {pair: s.Symbol('C'+''.join(map(str, pair)))
                   for pair in combinations(nodes, 2)}
        cross_values = {symbol: plane_cross(*pair) for pair, symbol in crosses.items()}

        def ci(i, j):
            result = 0
            for a, p in coefficients[i].items():
                for b, q in coefficients[j].items():
                    if a != b:
                        result += p*q*(1 if a < b else -1)*crosses[tuple(sorted((a, b)))]
            return s.expand(result)

        def origin(i, j, k):
            return heights[i]*ci(j, k)-heights[j]*ci(i, k)+heights[k]*ci(i, j)

        for i, j in combinations(nodes[:-1], 2):
            determinant = s.det(s.Matrix.hstack(points[6]-points[3],
                                                points[i]-points[3], points[j]-points[3]))
            assert s.expand(determinant.subs(beta, 0)+plane_cross(i, j)/2) == 0

        counts = {'macro_links': 0, 'normalized_06_links': 0, 'skipped_height_order_links': []}
        for quad in common.QUADS:
            i, j, k, l = quad
            polynomial = s.expand(origin(j, k, l)-origin(i, k, l)
                                  +origin(i, j, l)-origin(i, j, k))
            direct = s.det(s.Matrix.hstack(*(points[a]-points[i] for a in quad[1:])))
            assert s.expand(direct-polynomial.subs(cross_values)) == 0
            divided = {0, 6} <= set(quad)
            if divided:
                assert polynomial.subs(beta, 0) == 0
                polynomial = s.expand(polynomial/beta)
                trit = self.new_trit()
            else:
                trit = self.bits(quad)
            expression = s.expand(polynomial.subs(beta, 0))
            forms, uniform = [trit[::-1]], True
            for pair, variable in crosses.items():
                coefficient = s.expand(expression.coeff(variable))
                if coefficient == 0:
                    continue
                assert all(all(power <= 1 for power in monomial)
                           for monomial, value in s.Poly(coefficient, length, u, v).terms())
                corners = [coefficient.subs({length: a, u: b, v: c})
                           for a, b, c in product((0, HALF), repeat=3)]
                sign = 1 if all(value >= 0 for value in corners) else -1
                if not all(sign*value >= 0 for value in corners):
                    uniform = False
                    break
                assert any(sign*value > 0 for value in corners)
                forms.append(cross(*pair, sign))
            if uniform:
                self.sumzero(forms)
                counts['normalized_06_links' if divided else 'macro_links'] += 1
            else:
                assert not divided
                counts['skipped_height_order_links'].append(quad)
            if divided:
                literal = boundary.shared.common.lit(quad)
                self.clauses.extend(([-trit[0], literal], [-trit[1], -literal]))
        assert counts == {'macro_links': 53, 'normalized_06_links': 15,
                          'skipped_height_order_links': [(1, 4, 5, 7), (2, 4, 5, 7)]}
        self.counts = counts


def build(directory):
    directory.mkdir(parents=True, exist_ok=True)
    checks = metric_checks()
    model = AsymmetricVirtual()
    c24, c25, c45, c47, c57 = [model.cross(*pair)
                               for pair in ((2, 4), (2, 5), (4, 5), (4, 7), (5, 7))]
    ds, dw = model.bits((2, 3, 4, 5)), model.bits((4, 5, 6, 7))
    complements = [
        [-c25[1], -boundary.shared.common.lit((1, 2, 3, 5))],
        [c47[0], c57[0], -c45[0], dw[0]],
        [c24[1], c25[1], c47[1], c57[1], c45[0], ds[1], dw[1]],
    ]
    obligations = []
    for name, extra in (
        ('negative_core', [[model.bits((0, 1, 2, 7))[0]]]),
        ('three_cell_cover', complements),
    ):
        clauses = model.clauses+extra
        with FastSAT(model.n, clauses) as solver:
            assert solver.check() == -1, name
        filename = f'c0_flat_asymmetric_{name}.cnf'
        write_cnf(directory/filename, model.n, clauses)
        obligations.append({'file': filename, 'variables': model.n, 'clauses': len(clauses)})
    packet = {'checks': checks, 'source_links': model.counts,
              'unsat_obligations': obligations,
              'analytic_cells': ['upper_b_tilt', 'left_of_f_strict_turn', 'minus_f_e_wedge'],
              'excluded_order_pairs': ['bd', 'da'],
              'height_order_restriction': None, 'relative_rate_assumptions': [],
              'combined_nonparallel_both_flat_interior_C0_exclusion': True,
              'common_line_or_height_boundary_exclusion_claimed': False}
    (directory/'flat_asymmetric.json').write_text(json.dumps(packet, indent=2)+'\n')
    return packet


if __name__ == '__main__':
    if not __debug__:
        raise RuntimeError('run with assertions enabled')
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('output', type=Path)
    result = build(parser.parse_args().output)
    print(json.dumps({'unsat_obligations': len(result['unsat_obligations']),
                      'excluded_order_pairs': result['excluded_order_pairs']}), flush=True)
