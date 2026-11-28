#!/usr/bin/env python3
"""Exact closed orientation certificates for regular C1.

Usage: python exhaustive_c1_holonomy.py OUTPUT_DIRECTORY

Replay uses sparse integer polynomials and rational weights. The four
emitted CNFs require independent RUP replay. This is a topology reduction,
not a metric exclusion of either remaining marking.
"""

import argparse
from fractions import Fraction
from functools import lru_cache
from itertools import combinations
import json
from math import gcd
from pathlib import Path
import time

import sympy as sym

import exhaustive_c1_angles as angles
import solver_remaining_chambers as shared
from solver_chambers import write_cnf


QUADS = tuple(combinations(range(8), 4))
PAIRS = tuple(combinations(range(2, 8), 2))
ANCHORS = tuple(QUADS.index((0, 1) + pair) for pair in PAIRS)
GP_QUADS = tuple(combinations(range(2, 8), 4))
PARAMETER_WEIGHTS = ((1, 0, 0), (0, 1, 0), (1, -1, 0),
                     (0, 0, 1), (0, 1, -1), (1, -2, 1))
DEFAULT_DATA = Path(__file__).with_suffix('.json')


def add(*terms):
    """Linear combination of sparse integer polynomials."""
    result = {}
    for coefficient, row in terms:
        for monomial, value in row.items():
            result[monomial] = result.get(monomial, 0) + coefficient * value
    return {monomial: value for monomial, value in result.items() if value}


def primitive(row):
    divisor = 0
    for value in row.values():
        divisor = gcd(divisor, abs(value))
    return {monomial: value // (divisor or 1) for monomial, value in row.items()}


def cross_row(i, j):
    # Linear keys are (degree in beta, planar-cross index).
    if i == j or min(i, j) < 2:
        return {}
    return {(0, PAIRS.index(tuple(sorted((i, j))))): 1 if i < j else -1}


def parameter(row, polynomial):
    return add(*[(coefficient, {(degree + power, *indices): value
                               for (degree, *indices), value in row.items()})
                 for power, coefficient in enumerate(polynomial) if coefficient])


def product(first, second):
    # Quadratic keys are (degree in beta, first cross index, second cross index).
    result = {}
    for (degree1, i), value1 in first.items():
        for (degree2, j), value2 in second.items():
            monomial = (degree1 + degree2, min(i, j), max(i, j))
            result[monomial] = result.get(monomial, 0) + value1 * value2
    return {monomial: value for monomial, value in result.items() if value}


@lru_cache(maxsize=1)
def geometry_rows():
    # Four times the actual bracket after the positive projective
    # normalization alpha=1/2. Heights are 0,1/4,1/2,1/2,1/2,beta/2,0,0.
    heights = ((0, 0), (1, 0), (2, 0), (2, 0),
               (2, 0), (0, 2), (0, 0), (0, 0))

    def origin(i, j, k):
        return add((1, parameter(cross_row(j, k), heights[i])),
                   (-1, parameter(cross_row(i, k), heights[j])),
                   (1, parameter(cross_row(i, j), heights[k])))

    rows = []
    for i, j, k, l in QUADS:
        rows.append(add((1, origin(j, k, l)), (-1, origin(i, k, l)),
                        (1, origin(i, j, l)), (-1, origin(i, j, k))))
    pluecker = []
    for i, j, k, l in GP_QUADS:
        pluecker.append(add((1, product(cross_row(i, j), cross_row(k, l))),
                           (-1, product(cross_row(i, k), cross_row(j, l))),
                           (1, product(cross_row(i, l), cross_row(j, k)))))
    upper = add((1, cross_row(2, 3)), (-1, cross_row(2, 4)),
                (1, cross_row(3, 4)))
    lower = cross_row(6, 7)
    target = parameter(product(upper, lower), (0, -1, 1))
    u = add((1, cross_row(2, 4)), (-1, cross_row(2, 3)))
    v = add((1, parameter(cross_row(2, 4), (0, 1))),
            (1, parameter(cross_row(2, 6), (1, -1))),
            (-1, cross_row(2, 5)))
    w = add((1, cross_row(2, 7)), (-1, cross_row(2, 6)))
    return tuple(rows), tuple(pluecker), target, (u, v, w)


def signs(word):
    assert len(word) == 70 and set(word) <= {'+', '-'}
    return tuple(1 if sign == '+' else -1 for sign in word)


@lru_cache(maxsize=None)
def signed_rows(word, branch):
    assert branch in (0, 1)
    rows, _, _, (u, v, w) = geometry_rows()
    result = [primitive(add((sign, row))) for sign, row in zip(signs(word), rows)]
    result.extend((u, add((-1, v))) if branch == 0 else (v, w))
    return tuple(result)


def column(word, branch, description):
    kind, *arguments = description
    if kind == 'weak_product':
        i, j = arguments
        assert 0 <= i < 72 and 0 <= j < 72
        rows = signed_rows(word, branch)
        return primitive(product(rows[i], rows[j]))
    if kind == 'anchor_product':
        i, j, weight = arguments
        assert 0 <= i < 15 and 0 <= j < 15
        assert tuple(weight) in PARAMETER_WEIGHTS
        model = signs(word)
        base = {(0, min(i, j), max(i, j)): model[ANCHORS[i]] * model[ANCHORS[j]]}
        return primitive(parameter(base, weight))
    assert kind == 'gp'
    degree, index = arguments
    assert degree in (0, 1, 2) and 0 <= index < 15
    row = geometry_rows()[1][index]
    return {(power + degree, i, j): value for (power, i, j), value in row.items()}


def sign_conditions(certificate):
    """Conditions under which every positive column is unchanged."""
    result = set()
    for weight, kind, *arguments in certificate['terms']:
        assert Fraction(weight) != 0
        if kind == 'gp':
            continue
        if kind == 'weak_product':
            i, j = arguments
        else:
            assert kind == 'anchor_product'
            i, j = (ANCHORS[index] for index in arguments[:2])
        if i != j:
            indices = tuple(sorted(index for index in (i, j) if index < 70))
            if indices:
                result.add(indices)
    return tuple(sorted(result))


def matches(word, certificate, conditions):
    original = certificate['word']
    return all(sum(word[index] != original[index] for index in indices) % 2 == 0
               for indices in conditions)


def symbolic_checks():
    beta = sym.symbols('beta')
    p = [sym.zeros(2, 1), sym.zeros(2, 1)]
    p.extend(sym.Matrix(sym.symbols(f'x{i} y{i}')) for i in range(2, 8))
    crosses = [sym.Matrix.hstack(p[i], p[j]).det() for i, j in PAIRS]
    points = [point.col_join(sym.Matrix([height])) for point, height in
              zip(p, (0, sym.Rational(1, 4), sym.Rational(1, 2), sym.Rational(1, 2),
                      sym.Rational(1, 2), beta / 2, 0, 0))]
    rows, pluecker, target, (u, v, w) = geometry_rows()

    def evaluate(row):
        return sum(coefficient * beta ** degree * sym.prod(crosses[i] for i in indices)
                   for (degree, *indices), coefficient in row.items())

    for quad, row in zip(QUADS, rows):
        first, *rest = quad
        actual = sym.Matrix.hstack(*(points[i] - points[first] for i in rest)).det()
        assert sym.expand(evaluate(row) - 4 * actual) == 0
    assert all(sym.expand(evaluate(row)) == 0 for row in pluecker)
    cross = lambda first, second: sym.Matrix.hstack(first, second).det()
    e3, f = p[4] - p[3], p[7] - p[6]
    y5 = beta * p[4] + (1 - beta) * p[6] - p[5]
    for row, vector in zip((u, v, w), (e3, y5, f)):
        assert sym.expand(evaluate(row) - cross(p[2], vector)) == 0
    upper = cross(p[3] - p[2], p[4] - p[2])
    lower = cross(p[6], p[7])
    assert sym.expand(evaluate(target) + beta * (1 - beta) * upper * lower) == 0

    alpha, z = sym.symbols('alpha z')
    a, c, d = 1 - alpha, 2 - 4 * alpha, alpha
    denominator = c * z + d
    transformed_height = a * z / denominator
    assert sym.cancel(transformed_height.subs(z, 0)) == 0
    assert sym.cancel(transformed_height.subs(z, sym.Rational(1, 2)) - sym.Rational(1, 2)) == 0
    assert sym.cancel(transformed_height.subs(z, alpha / 2) - sym.Rational(1, 4)) == 0
    beta_denominator = denominator.subs(z, beta / 2)
    new_beta = beta * (1 - alpha) / beta_denominator
    assert sym.cancel(2 * transformed_height.subs(z, beta / 2) - new_beta) == 0
    assert sym.expand(beta_denominator - beta * (1 - alpha) - alpha * (1 - beta)) == 0
    matrix = sym.Matrix([[1, 0, 0, 0], [0, 1, 0, 0], [0, 0, a, 0], [0, 0, c, d]])
    assert sym.expand(matrix.det() - a * d) == 0
    new_y5 = new_beta * p[4] / (1 - alpha) + (1 - new_beta) * p[6] / alpha - p[5] / beta_denominator
    assert all(sym.cancel(value) == 0 for value in new_y5 - y5 / beta_denominator)

    # The zero-norm cases in the angular corollary use only adjacent
    # nearest-lift bounds and the strict regularity of the lower cap.
    pp, qq, t = sym.symbols('p q t')
    sigma = sym.Rational(1, 2) + (1 - t) * pp - t * qq
    n2 = sigma ** 2 - 2 * (1 - t) * pp
    certificate = (t * pp + (1 - t) * qq) * (1 - 2 * pp - 2 * qq) + (t * pp - (1 - t) * qq) ** 2
    assert sym.expand(n2 - (sym.Rational(1, 2) - pp - qq) ** 2 - certificate) == 0
    assert sym.expand(sigma.subs({pp: (1 - t) / 2, qq: t / 2}) - (1 - t)) == 0
    return {'bracket_rows': 70, 'planar_pluecker_identities': 15,
            'cross_rows': 3, 'positive_projective_normalization': True,
            'zero_norm_identity': True}


def replay(data):
    assert data['format'] == 1
    models = data['primary_models']
    assert len(models) == len(set(models)) == 132 and models == sorted(models)
    for model in models:
        signs(model)
    certificates = data['certificates']
    assert len(certificates) == 32
    target = geometry_rows()[2]
    coverage = {(word, branch): [] for word in models for branch in (0, 1)}
    term_count = 0
    for index, certificate in enumerate(certificates):
        word, branch = certificate['word'], certificate['branch']
        assert word in models and branch in (0, 1)
        total = {}
        for text_weight, *description in certificate['terms']:
            weight = Fraction(text_weight)
            assert weight != 0 and (description[0] == 'gp' or weight > 0)
            total = add((1, total), (weight, column(word, branch, description)))
            term_count += 1
        assert total == target, (index, word, branch)
        conditions = sign_conditions(certificate)
        for model in models:
            if matches(model, certificate, conditions):
                coverage[model, branch].append(index)
    assert all(coverage.values())
    for quad, sign in (((0, 1, 2, 3), 1), ((0, 1, 2, 7), -1),
                       ((3, 4, 5, 6), -1), ((4, 5, 6, 7), -1)):
        assert all(signs(word)[QUADS.index(quad)] == sign for word in models)
    return {'certificates': len(certificates), 'exact_terms': term_count,
            'primary_words': len(models), 'closed_branches': len(coverage),
            'coverage': [{'word': word, 'branch': branch, 'certificate': indices[0]}
                         for (word, branch), indices in coverage.items()]}


def build(directory, data_path=DEFAULT_DATA):
    started = time.monotonic()
    data = json.loads(data_path.read_text())
    symbolic = symbolic_checks()
    replayed = replay(data)
    directory.mkdir(parents=True, exist_ok=True)
    n, base, *_ = shared.base_formula()
    obligations = []
    for upper, lower in ((-1, -1), (-1, 1), (1, -1)):
        name = f'c1_holonomy_cap_{upper}_{lower}.cnf'
        write_cnf(directory / name, n, base + angles.cap_units(upper, lower))
        obligations.append(name)
    cover = base + angles.cap_units(1, 1)
    cover += [[-(i + 1) * value for i, value in enumerate(signs(word))]
              for word in data['primary_models']]
    name = 'c1_holonomy_coverage.cnf'
    write_cnf(directory / name, n, cover)
    obligations.append(name)
    result = {**replayed, 'symbolic_checks': symbolic,
              'assumptions': ['noncollinear projected caps 234 and 067', '0<alpha,beta<1'],
              'conclusions': ['U<0 or V>0', 'V<0 or W<0'],
              'definitions': {'U': 'cross(P2,P4-P3)',
                              'V': 'cross(P2,beta*P4+(1-beta)*P6-P5)',
                              'W': 'cross(P2,P7-P6)'},
              'actual_minor_semantics': 'weak signs of a generic completion',
              'unsat_obligations': obligations, 'metric_exclusion': False,
              'replay_seconds': time.monotonic() - started}
    (directory / 'c1_holonomy.json').write_text(json.dumps(result, indent=2) + '\n')
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('output', type=Path)
    parser.add_argument('--data', type=Path, default=DEFAULT_DATA)
    args = parser.parse_args()
    result = build(args.output, args.data)
    print(json.dumps({key: value for key, value in result.items() if key != 'coverage'}))


if __name__ == '__main__':
    if not __debug__:
        raise RuntimeError('run with assertions enabled')
    main()
