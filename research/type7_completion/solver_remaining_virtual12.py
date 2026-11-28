#!/usr/bin/env python3
"""Exact virtual-edge sign cones at the ray-1 h1=0 endpoint.

Usage: python solver_remaining_virtual12.py [--produce OUTPUT_JSON]

The optional LP is only a certificate producer. Replay reconstructs every
bracket, binds the complete endpoint sign list, and checks rational or
polynomial Farkas identities. The other collapsed vertex, 4, is left free.
"""

import argparse
from fractions import Fraction
from functools import lru_cache
from itertools import combinations
import json
from math import gcd, lcm
from pathlib import Path
import time

import sympy as sym

import remaining_ray1_endpoint as endpoint

C, D, E, Y, R = sym.symbols('c d e aY r')
VARIABLES = (C, D, E, Y)
QUADS = tuple(combinations(range(8), 4))
QUAD_INDEX = {quad: index for index, quad in enumerate(QUADS)}
POINTS = tuple(sym.Matrix(point) for point in (
    (0, 0, 0), (0, 0, 1), (0, 0, 1), (sym.Rational(1, 2), 0, 1),
    (0, 0, 1), (sym.Rational(1, 2), C, 0), (0, D, 0),
    (sym.Rational(1, 2), E, 0)))
SCENARIOS = {
    'positive_x': (sym.Integer(1), sym.Integer(2), None),
    'pure_positive_y': (sym.Integer(0), sym.Integer(0), 1),
    'pure_negative_y': (sym.Integer(0), sym.Integer(0), -1),
    'negative_quadrant': (R-1, -2*R, None),
    'negative_x_boundary': (sym.Integer(-1), sym.Integer(0), None),
    'negative_z_boundary': (sym.Integer(0), sym.Integer(-2), None),
    'positive_z_boundary': (sym.Integer(0), sym.Integer(2), None),
}
EXPECTED = {'positive_x': 172, 'pure_positive_y': 0, 'pure_negative_y': 0,
            'negative_quadrant': 0, 'negative_x_boundary': 15,
            'negative_z_boundary': 38, 'positive_z_boundary': 172}
DEFAULT_DATA = Path(__file__).with_suffix('.json')


def word(model):
    return ''.join('+' if value > 0 else '-' for value in model)


def model(word_):
    assert len(word_) == 70 and set(word_) <= {'+', '-'}
    return tuple(1 if value == '+' else -1 for value in word_)


@lru_cache(maxsize=None)
def bracket(quad):
    origin = POINTS[quad[0]]
    return sym.expand(sym.Matrix.hstack(*(POINTS[i]-origin for i in quad[1:])).det())


@lru_cache(maxsize=None)
def virtual_brackets(x, z):
    direction = sym.Matrix((x, Y, z))
    result = {}
    for j, k in combinations((0, 3, 5, 6, 7), 2):
        ordered = (1, 2, j, k)
        parity = (-1)**sum(ordered[a] > ordered[b] for a, b in combinations(range(4), 2))
        result[QUAD_INDEX[tuple(sorted(ordered))]] = sym.expand(
            parity*sym.Matrix.hstack(direction, POINTS[j]-POINTS[1],
                                    POINTS[k]-POINTS[1]).det())
    assert len(result) == 10
    return result


@lru_cache(maxsize=None)
def primitive_row(expression):
    expression = sym.expand(expression)
    row = [expression.coeff(variable) for variable in VARIABLES]
    row.append(expression.subs(dict.fromkeys(VARIABLES, 0)))
    assert sym.expand(expression-sum(a*v for a, v in zip(row, VARIABLES))-row[4]) == 0
    assert all(sym.Poly(value, R).degree() <= 1 for value in row)
    coefficients = [coefficient for value in row for coefficient in sym.Poly(value, R).all_coeffs()]
    denominator = lcm(*(int(value.q) for value in coefficients))
    content = gcd(*(int(value*denominator) for value in coefficients))
    assert content > 0
    return tuple(sym.expand(value*denominator/content) for value in row)


@lru_cache(maxsize=None)
def row_key(row):
    return tuple(int(coefficient) for value in row
                 for coefficient in (sym.expand(value).coeff(R, 0), sym.expand(value).coeff(R, 1)))


def groups(words, scenario):
    macro = tuple(bracket(quad) for quad in QUADS)
    x, z, fixed_y = SCENARIOS[scenario]
    virtual = virtual_brackets(x, z)
    grouped = {}
    for signs in words:
        values = model(signs)
        rows = {primitive_row(values[i]*value) for i, value in enumerate(macro) if value != 0}
        rows.update(primitive_row(values[i]*value) for i, value in virtual.items() if value != 0)
        for variable in VARIABLES[:3]:
            rows.update((primitive_row(1-variable), primitive_row(1+variable)))
        if fixed_y is not None:
            rows.update((primitive_row(Y-fixed_y), primitive_row(fixed_y-Y)))
        key = tuple(sorted(rows, key=row_key))
        grouped.setdefault(key, []).append(signs)
    return [(rows, tuple(sorted(signs))) for rows, signs in
            sorted(grouped.items(), key=lambda item: tuple(map(row_key, item[0])))]


def face_rows(base, coordinate, sign):
    assert coordinate in range(3) and sign in (-1, 1)
    row = [sym.Integer(0)]*5
    row[coordinate], row[4] = sym.Integer(1), sym.Integer(-sign)
    return tuple(sorted(set(base+(tuple(row), tuple(-value for value in row))), key=row_key))


def encode_polynomial(expression):
    polynomial = sym.Poly(expression, R, domain=sym.QQ)
    return [str(polynomial.nth(index)) for index in range(max(0, polynomial.degree())+1)]


def decode_polynomial(coefficients):
    assert isinstance(coefficients, list) and 1 <= len(coefficients) <= 12
    values = [sym.Rational(str(Fraction(value))) for value in coefficients]
    return sum(value*R**index for index, value in enumerate(values))


def bernstein_coefficients(expression):
    polynomial = sym.Poly(expression, R, domain=sym.QQ)
    degree = max(0, polynomial.degree())
    return [sum(polynomial.nth(k)*sym.binomial(j, k)/sym.binomial(degree, k)
                for k in range(j+1)) for j in range(degree+1)]


def check_certificate(rows, certificate):
    indices = [entry[0] for entry in certificate['weights']]
    assert len(indices) == len(set(indices)) and all(0 <= index < len(rows) for index in indices)
    weights = [(index, decode_polynomial(coefficients))
               for index, coefficients in certificate['weights']]
    rhs = decode_polynomial(certificate['rhs'])
    assert all(value >= 0 for _, weight in weights for value in bernstein_coefficients(weight))
    positive = bernstein_coefficients(rhs)
    assert all(value >= 0 for value in positive) and any(value > 0 for value in positive)
    # Every Bernstein basis function is positive at every 0<r<1.
    # Constant certificates apply without a parameter as well.
    for column in range(5):
        assert sym.expand(sum(weight*rows[index][column] for index, weight in weights)
                          +(rhs if column == 4 else 0)) == 0


def produce_certificate(rows, sample=sym.Rational(2, 5)):
    import numpy as np
    from scipy.optimize import linprog
    matrix = sym.Matrix(rows).T
    result = linprog(np.ones(matrix.cols), A_eq=np.array(matrix.subs(R, sample)).astype(float),
                     b_eq=[0, 0, 0, 0, -1], bounds=(0, None), method='highs')
    assert result.success
    indices = [index for index, value in enumerate(result.x) if value > 1e-9]
    solution, parameters = matrix[:, indices].gauss_jordan_solve(sym.Matrix([0, 0, 0, 0, -1]))
    assert parameters.rows == 0
    denominator = sym.lcm([sym.fraction(sym.cancel(value))[1] for value in solution])
    weights = [sym.cancel(value*denominator**2) for value in solution]
    rhs = sym.expand(denominator**2)
    common = sym.gcd_list(weights+[rhs])
    weights, rhs = [sym.cancel(value/common) for value in weights], sym.cancel(rhs/common)
    if rhs.subs(R, sample) < 0:
        weights, rhs = [-value for value in weights], -rhs
    certificate = {'weights': [[index, encode_polynomial(weight)] for index, weight in zip(indices, weights)],
                   'rhs': encode_polynomial(rhs)}
    check_certificate(rows, certificate)
    return certificate


def produce(words):
    import numpy as np
    from scipy.optimize import linprog
    output = {'version': 1, 'models': sorted(words), 'scenarios': {}}
    for name in SCENARIOS:
        records = []
        for base, signs in groups(words, name):
            cases, found = [], False
            for coordinate, sign in ((k, sign) for k in range(3) for sign in (-1, 1)):
                rows = face_rows(base, coordinate, sign)
                if name != 'negative_quadrant':
                    matrix = np.array(rows).astype(float)
                    result = linprog(np.zeros(4), A_ub=-matrix[:, :4], b_ub=matrix[:, 4],
                                     bounds=[(None, None)]*4, method='highs')
                    if result.success:
                        point = [Fraction(float(value)).limit_denominator(10**7) for value in result.x]
                        assert all(sum(sym.Rational(value.numerator, value.denominator)*coefficient
                                       for value, coefficient in zip(point, row))+row[4] >= 0 for row in rows)
                        cases = [{'face': [coordinate, sign], 'point': list(map(str, point))}]
                        found = True
                        break
                    assert result.status == 2
                cases.append({'face': [coordinate, sign], **produce_certificate(rows)})
            records.append({'signs': list(signs), 'satisfiable_relaxation': found, 'cases': cases})
        output['scenarios'][name] = records
    return output


def verify(packet, words):
    assert packet['version'] == 1 and packet['models'] == sorted(words)
    assert set(packet['scenarios']) == set(SCENARIOS)
    statistics, witnesses = {}, {}
    total_certificates = 0
    for name, records in packet['scenarios'].items():
        expected = groups(words, name)
        assert len(records) == len(expected)
        surviving = []
        for record, (base, signs) in zip(records, expected):
            assert record['signs'] == list(signs)
            if record['satisfiable_relaxation']:
                assert name != 'negative_quadrant' and len(record['cases']) == 1
                case = record['cases'][0]
                point = tuple(sym.Rational(str(Fraction(value))) for value in case['point'])
                assert len(point) == 4
                rows = face_rows(base, *case['face'])
                assert all(sum(a*b for a, b in zip(row, point))+row[4] >= 0 for row in rows)
                surviving.extend(signs)
            else:
                cases = record['cases']
                assert [case['face'] for case in cases] == [[k, sign] for k in range(3) for sign in (-1, 1)]
                for case in cases:
                    check_certificate(face_rows(base, *case['face']), case)
                    total_certificates += 1
        assert len(surviving) == EXPECTED[name]
        statistics[name] = {'groups': len(records), 'surviving_models': len(surviving)}
        witnesses[name] = sorted(surviving)
    return {'scenarios': statistics, 'exact_farkas_certificates': total_certificates,
            'surviving_signs': witnesses, 'complete_endpoint_exclusion': False}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--produce', type=Path)
    parser.add_argument('--data', type=Path, default=DEFAULT_DATA)
    args = parser.parse_args()
    start = time.monotonic()
    words = tuple(sorted(map(word, endpoint.endpoint_primary_models())))
    if args.produce:
        packet = produce(words)
        args.produce.write_text(json.dumps(packet, separators=(',', ':'))+'\n')
    else:
        packet = json.loads(args.data.read_text())
    result = verify(packet, words)
    result.pop('surviving_signs')
    result['seconds'] = round(time.monotonic()-start, 3)
    print(json.dumps(result), flush=True)


if __name__ == '__main__':
    if not __debug__:
        raise RuntimeError('run with assertions enabled')
    main()
