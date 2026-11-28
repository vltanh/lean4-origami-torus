#!/usr/bin/env python3
"""Exclude the positive-edge, two-collinear-cap ray-2 C1 stratum.

Exact scalar sign classification leaves twenty families.  Every family
has an impossible nontrivial normal stretch after independent RUP replay.
The classification assumes h2,h3,h6,h7>0 and 0<alpha,beta<1; zero cap
edges and height endpoints are not excluded by this package.
"""

import argparse
from functools import lru_cache
from itertools import combinations, product
import json
from pathlib import Path
import time

import sympy as S

import remaining_c1_flat_reduction as reduction
import solver_remaining_c1_collinear as trits
import solver_remaining_c1_flat_stretch as previous_stretch
import solver_remaining_c1_geometry as metric
import solver_remaining_limit as source_metric
import solver_remaining_chambers as shared
from solver_chambers import write_cnf
from solver_sat import FastSAT


A, B, X, Y = S.symbols('alpha beta x y')
HALF = S.Rational(1, 2)
PARAMETERS = (A, B, X, Y)
WIDTHS = (1, 1, HALF, HALF)
BITS = tuple(product((0, 1), repeat=4))
UPPER = {'A': (HALF, X, 1), 'B': (X, HALF, 1),
         'C': (HALF, HALF, 1), 'D': (X, HALF - X, -1)}
LOWER = {'A': (Y, HALF, 1), 'B': (HALF, Y, 1),
         'C': (HALF, HALF, 1), 'D': (Y, HALF - Y, -1)}
NORMAL_VERTICES = (2, 4, 5, 6, 7)
NORMALS = S.symbols('n2 n4 n5 n6 n7')
QUADS = trits.QUADS
QUAD_INDEX = {quad: i for i, quad in enumerate(QUADS)}


def pair_type(radius_sign, relative_direction):
    if radius_sign == -1:
        return 0 if relative_direction == 1 else 1
    return 2 if relative_direction == 1 else 3


def pair_data(kind, h, k, a):
    """Return the two outer weights and the positive radius."""
    q = 1 - a
    if kind == 0:
        return HALF - k, HALF, a * (HALF - h) + q * (HALF - k)
    if kind == 1:
        return HALF, HALF, HALF - a * h
    if kind == 2:
        return HALF, HALF - h, HALF
    assert kind == 3
    return HALF - k + 2 * a * h * k, HALF - h + 2 * q * h * k, HALF - q * k


def pair_cost(kind, h, k):
    return (h, h + k, k, 2 * h * k)[kind]


def scalar_checks():
    a, h, k, p, q = S.symbols('a h k p q')
    for eta, epsilon in product((-1, 1), repeat=2):
        kind = pair_type(eta, epsilon)
        h0, h1, rho = pair_data(kind, h, k, a)
        sigma = (1 - a) * (1 - h0) + a * h1
        linked = a * h - eta * rho
        assert S.expand(rho - a * (1 - h1 - h) - (1 - a) * h0) == 0
        assert S.expand(h * rho * (1 + eta) - (HALF - h1)) == 0
        assert S.expand(k * (sigma + epsilon * linked) - (HALF - h0)) == 0
        assert S.expand(linked ** 2 - sigma ** 2 + 2 * (1 - a) * (HALF - h0)) == 0
        assert S.expand(h + k - (1 - h0 - h1) - pair_cost(kind, h, k)) == 0
    # In the +R,+P7 case the only non-generic scalar branch occurs at
    # h=k=1/2. Its cost is 1/2, and the other pair has positive cost.
    rho = HALF - a * h + a * q - (1 - a) * p
    first = q - 2 * h * rho
    second = p - k * (1 - 2 * rho)
    assert S.expand(k * first + h * second - h * p - k * q + h * k) == 0
    qvalue = h * (1 - p / k)
    assert S.cancel(first.subs(q, qvalue)
                    + h * p * (1 - 2 * a * h - 2 * (1 - a) * k) / k) == 0
    assert S.expand(1 - 2 * a * h - 2 * (1 - a) * k
                    - a * (1 - 2 * h) - (1 - a) * (1 - 2 * k)) == 0
    return {'four_scalar_pair_solutions': True,
            'only_exceptional_pair_has_half_cost': True}


@lru_cache(maxsize=None)
def coefficient_sign(expression):
    """Exact strict sign on the open four-dimensional parameter box."""
    polynomial = S.Poly(S.expand(expression), *PARAMETERS)
    terms = polynomial.terms()
    assert all(max(exponents) <= 1 for exponents, _ in terms)
    values = {}
    for bits in BITS:
        corner = tuple(width * bit for width, bit in zip(WIDTHS, bits))
        values[bits] = sum(coefficient * S.prod(value ** exponent for value, exponent
                                               in zip(corner, exponents))
                           for exponents, coefficient in terms)
    # Coefficientwise reconstruction of the multilinear interpolation.
    # This is the Boolean-cube Mobius inversion after scaling X,Y by 1/2.
    for exponents in BITS:
        reconstructed = sum((-1) ** (sum(exponents) - sum(bits)) * value
                            for bits, value in values.items()
                            if all(bit <= exponent for bit, exponent in zip(bits, exponents)))
        actual = polynomial.coeff_monomial(exponents) * S.prod(
            width ** exponent for width, exponent in zip(WIDTHS, exponents))
        assert reconstructed == actual
    if all(value == 0 for value in values.values()):
        return 0
    if all(value >= 0 for value in values.values()):
        return 1
    if all(value <= 0 for value in values.values()):
        return -1
    return None


def classify():
    families, excluded = [], []
    for upper, lower, epsilon, eta, theta in product(UPPER, LOWER, (-1, 1), (-1, 1), (-1, 1)):
        h, j, upper_tip = UPPER[upper]
        k, ell, lower_tip = LOWER[lower]
        first = pair_type(eta, epsilon)
        second = pair_type(theta, epsilon * upper_tip * lower_tip)
        budget = S.factor(pair_cost(first, h, k) + pair_cost(second, j, ell) - HALF)
        record = {'upper': upper, 'lower': lower, 'epsilon': epsilon,
                  'eta': eta, 'theta': theta, 'first_pair_type': first,
                  'second_pair_type': second, 'budget_polynomial': str(budget)}
        sign = coefficient_sign(budget)
        if sign:
            excluded.append({**record, 'strict_budget_sign': sign})
            continue
        if budget == 0:
            substitution = {}
        elif S.expand(budget - (X + Y - HALF)) == 0:
            substitution = {Y: HALF - X}
        elif S.expand(budget) in (X - Y, Y - X):
            substitution = {Y: X}
        else:
            raise AssertionError(budget)
        record['index'] = len(families)
        record['substitution'] = substitution
        families.append(record)
    assert len(families) == 20 and len(excluded) == 108
    return families, excluded


def family_geometry(family):
    h, j, upper_tip = UPPER[family['upper']]
    k, ell, lower_tip = LOWER[family['lower']]
    epsilon, eta, theta = (family[key] for key in ('epsilon', 'eta', 'theta'))
    first, second = family['first_pair_type'], family['second_pair_type']
    h0, h1, rho1 = pair_data(first, h, k, A)
    h5, h4, rho5 = pair_data(second, j, ell, B)
    weights = [h0, h1, h, j, h4, h5, ell, k]
    original = [S.Integer(0), S.Integer(0), None, -eta * rho1 / A,
                None, None, epsilon * (k - lower_tip * ell), epsilon * k]
    original[2] = original[3] + h
    original[4] = original[3] + upper_tip * j
    original[5] = B * original[3] + (1 - B) * original[6] + theta * rho5 * upper_tip
    substitution = family['substitution']
    assert S.cancel((sum(weights) - S.Rational(5, 2)).subs(substitution)) == 0

    # Check every closed C1 projected stress against its original source.
    horizontal = metric.horizontal_displacements(weights)
    residuals = S.Matrix([S.expand((original[j0] - original[i]) ** 2 - horizontal[i, j0] ** 2)
                          for i, j0 in source_metric.EDGES] + [0] * 5)
    stress = source_metric.closed_c1_rows().subs({source_metric.A: A / 2, source_metric.B: -B / 2})
    assert all(S.cancel(value.subs(substitution)) == 0 for value in stress * residuals)

    # A positive-determinant shear removes all alpha denominators.
    assert first in (0, 2, 3)
    shear = (-(1 - 2 * k) if first == 0 else 1 if first == 2 else 1 - 2 * k) / A
    transform = S.Matrix([[2, 0, 2 * shear], [0, 1, 0], [0, 0, 2]])
    assert transform.det() == 4
    levels = (0, A, 1, 1, 1, B, 0, 0)
    x = [S.cancel((2 * point + shear * height).subs(substitution))
         for point, height in zip(original, levels)]
    assert all(A not in point.free_symbols and S.denom(point) == 1 for point in x)
    normals = dict(zip(NORMAL_VERTICES, NORMALS))
    points = [S.Matrix([x[i], normals.get(i, 0), levels[i]]) for i in range(8)]
    rows = []
    for quad in QUADS:
        determinant = S.expand(S.det(S.Matrix.hstack(*(points[i] - points[quad[0]] for i in quad[1:]))))
        row = tuple(determinant.coeff(normal) for normal in NORMALS)
        assert S.expand(determinant - sum(coefficient * normal for coefficient, normal in zip(row, NORMALS))) == 0
        rows.append(row)

    def area(i, j0, k0):
        return S.expand((x[j0] - x[i]) * (levels[k0] - levels[i])
                        - (x[k0] - x[i]) * (levels[j0] - levels[i]))

    relations = []
    for i, j0 in combinations(range(8), 2):
        for a, b, c in combinations([vertex for vertex in range(8) if vertex not in (i, j0)], 3):
            relation = (((i, j0, a, b), area(i, j0, c)),
                        ((i, j0, a, c), -area(i, j0, b)),
                        ((i, j0, b, c), area(i, j0, a)))
            for column in range(len(NORMALS)):
                assert S.expand(sum(coefficient * previous_stretch.parity(quad)
                                    * rows[QUAD_INDEX[tuple(sorted(quad))]][column]
                                    for quad, coefficient in relation)) == 0
            relations.append(relation)
    assert len(rows) == 70 and len(relations) == 560
    return x, rows, relations


class NormalModel(trits.ActualBracketModel):
    def __init__(self, family):
        x, rows, relations = family_geometry(family)
        self.n, base, *_ = shared.base_formula()
        self.clauses = [list(row) for row in base]
        self.trits = {}
        for high in ({2, 3, 4}, {1, 2, 3, 4, 5}):
            for support in combinations(range(8), 5):
                if set(support) <= high or not set(support) & high:
                    continue
                row = [(1 if vertex in high else -1) * (-1) ** i
                       * shared.common.lit(support[:i] + support[i + 1:])
                       for i, vertex in enumerate(support)]
                self.clauses.extend((row, [-literal for literal in row]))
        for index, quad in enumerate(QUADS):
            positive, negative = self.new_trit()
            self.trits[quad] = positive, negative
            self.clauses.extend(([-positive, index + 1], [-negative, -index - 1]))
        normal_bits = [self.new_trit() for _ in NORMALS]
        self.clauses.append([bit for pair in normal_bits for bit in pair])
        for support in combinations(range(8), 5):
            self.sumzero([self.bits(support[:i] + support[i + 1:], (-1) ** i)
                          for i in range(5)])
        omitted = 0
        for quad, row in zip(QUADS, rows):
            signs = tuple(coefficient_sign(value) for value in row)
            if None in signs:
                omitted += 1
                continue
            self.sumzero([self.bits(quad, -1)] + [pair if sign > 0 else pair[::-1]
                         for pair, sign in zip(normal_bits, signs) if sign])
        for relation in relations:
            signs = tuple(coefficient_sign(value) for _, value in relation)
            if None in signs:
                omitted += 1
                continue
            self.sumzero([self.bits(quad, sign)
                          for (quad, _), sign in zip(relation, signs) if sign])
        self.record = {'transformed_horizontal': list(map(str, x)),
                       'omitted_variable_sign_relations': omitted}


def build(directory):
    started = time.monotonic()
    identities = scalar_checks()
    families, excluded = classify()
    directory.mkdir(parents=True, exist_ok=True)
    records = []
    for family in families:
        model = NormalModel(family)
        with FastSAT(model.n, model.clauses) as solver:
            assert solver.check() == -1, family
        filename = f'c1_flat2_positive_stretch_{family["index"]:02d}.cnf'
        write_cnf(directory / filename, model.n, model.clauses)
        serial = {key: value for key, value in family.items() if key != 'substitution'}
        serial['substitution'] = {str(key): str(value) for key, value in family['substitution'].items()}
        records.append({**serial, **model.record, 'file': filename,
                        'variables': model.n, 'clauses': len(model.clauses)})
    packet = {'domain': 'ray2 C1; both collinear caps; h2,h3,h6,h7>0; 0<alpha,beta<1',
              'uses_common_line_reduction': 'remaining_c1_flat_reduction.py',
              'scalar_identities': identities, 'scalar_cases': 128,
              'strict_budget_exclusions': excluded, 'normal_stretch_families': records,
              'coefficient_signs': 'exact multilinear interpolation on the sixteen box corners',
              'source_checks_per_family': {'projected_metric_stresses': 12,
                                           'linear_determinants': 70, 'projection_identities': 560},
              'relative_rate_assumptions': [], 'zero_cap_edges_excluded': False,
              'height_endpoints_excluded': False, 'seconds': time.monotonic() - started}
    (directory / 'c1_flat_positive_stretch.json').write_text(json.dumps(packet, indent=2) + '\n')
    return packet


if __name__ == '__main__':
    if not __debug__:
        raise RuntimeError('run with assertions enabled')
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('output', type=Path)
    result = build(parser.parse_args().output)
    print(json.dumps({'scalar_cases': result['scalar_cases'],
                      'budget_exclusions': len(result['strict_budget_exclusions']),
                      'normal_stretch_families': len(result['normal_stretch_families']),
                      'zero_cap_edges_excluded': False, 'seconds': result['seconds']}))
