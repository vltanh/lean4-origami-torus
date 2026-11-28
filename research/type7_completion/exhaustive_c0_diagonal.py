#!/usr/bin/env python3
"""Exact product certificates for the regular ray-1 C0 diagonal.

Usage: python exhaustive_c0_diagonal.py OUTPUT [--produce]

Replay uses integer polynomial coefficients and rational weights only.
The emitted source-coverage CNF must also pass independent RUP replay.
An LP is used only with --produce to discover the frozen certificates.
"""

import argparse
from fractions import Fraction
from functools import lru_cache
from itertools import combinations, combinations_with_replacement
import json
from math import gcd
from pathlib import Path
import time

import sympy as sym

import exhaustive_c0_angles as angles
import exhaustive_c0_turning as turning
import solver_remaining_chambers as shared
from solver_chambers import write_cnf

QUADS = tuple(combinations(range(8), 4))
PAIRS = tuple(combinations(range(2, 8), 2))
MONOMIALS = tuple(combinations_with_replacement(range(15), 2))
STRICT_QUADS = ((0, 1, 2, 3), (0, 1, 6, 7)) + tuple(q for q, _ in turning.METRIC_SIGNS)
DIAGONAL_QUADS = ((2, 3, 4, 5), (4, 5, 6, 7))
DEFAULT_DATA = Path(__file__).with_suffix('.json')


def primitive(row):
    common = 0
    for value in row:
        common = gcd(common, abs(value))
    return tuple(value // (common or 1) for value in row)


def cross_row(i, j):
    row = [0] * 15
    if i != j and min(i, j) >= 2:
        row[PAIRS.index(tuple(sorted((i, j))))] = 1 if i < j else -1
    return tuple(row)


def combine(*terms):
    return tuple(sum(weight * row[i] for weight, row in terms) for i in range(len(terms[0][1])))


def product_row(first, second):
    return tuple(first[i] * second[j] + (first[j] * second[i] if i != j else 0)
                 for i, j in MONOMIALS)


@lru_cache(maxsize=1)
def geometry_rows():
    # Four times the actual quarter-height bracket, before primitive scaling.
    heights = (0, 2, 2, 2, 1, 1, 0, 0)

    def origin(i, j, k):
        return combine((heights[i], cross_row(j, k)),
                       (-heights[j], cross_row(i, k)), (heights[k], cross_row(i, j)))

    rows = []
    for i, j, k, l in QUADS:
        rows.append(combine((1, origin(j, k, l)), (-1, origin(i, k, l)),
                            (1, origin(i, j, l)), (-1, origin(i, j, k))))
    gp = [combine((1, product_row(cross_row(i, j), cross_row(k, l))),
                  (-1, product_row(cross_row(i, k), cross_row(j, l))),
                  (1, product_row(cross_row(i, l), cross_row(j, k))))
          for i, j, k, l in combinations(range(2, 8), 4)]
    return tuple(rows), tuple(gp)


def symbolic_checks():
    p = [sym.zeros(2, 1), sym.zeros(2, 1)]
    p.extend(sym.Matrix(sym.symbols(f'x{i} y{i}')) for i in range(2, 8))
    values = [sym.Matrix.hstack(p[i], p[j]).det() for i, j in PAIRS]
    points = [point.col_join(sym.Matrix([height])) for point, height in
              zip(p, (0, sym.Rational(1, 2), sym.Rational(1, 2), sym.Rational(1, 2),
                      sym.Rational(1, 4), sym.Rational(1, 4), 0, 0))]
    rows, gp = geometry_rows()
    for quad, row in zip(QUADS, rows):
        first, *rest = quad
        actual = sym.Matrix.hstack(*(points[i] - points[first] for i in rest)).det()
        assert sym.expand(sum(c * value for c, value in zip(row, values)) - 4 * actual) == 0
    monomials = [values[i] * values[j] for i, j in MONOMIALS]
    assert all(sym.expand(sum(c * value for c, value in zip(row, monomials))) == 0 for row in gp)
    # A positive projective map sends any common interior height to 1/4.
    u, z = sym.symbols('u z')
    a, c, d = 1 - 2 * u, 2 - 8 * u, 2 * u
    height = a * z / (c * z + d)
    assert sym.cancel(height.subs(z, 0)) == 0
    assert sym.cancel(height.subs(z, sym.Rational(1, 2)) - sym.Rational(1, 2)) == 0
    assert sym.cancel(height.subs(z, u) - sym.Rational(1, 4)) == 0
    matrix = sym.Matrix([[1, 0, 0, 0], [0, 1, 0, 0], [0, 0, a, 0], [0, 0, c, d]])
    assert sym.expand(matrix.det() - a * d) == 0
    # This is the universal homogeneous determinant rule; the four positive
    # denominators supply the remaining pointwise factors after normalization.
    return {'bracket_rows': 70, 'planar_pluecker_identities': 15,
            'positive_projective_diagonal_normalization': True}


def source_formula():
    n, clauses, *_ = shared.base_formula()
    clauses += angles.cap_units(1)
    clauses += [[sign * shared.common.lit(quad)] for quad, sign in turning.METRIC_SIGNS]
    clauses += [[shared.common.lit(quad) for quad in DIAGONAL_QUADS]]
    return n, clauses


def word(model):
    return ''.join('+' if value > 0 else '-' for value in model)


def signs(text):
    assert len(text) == 70 and set(text) <= {'+', '-'}
    return tuple(1 if value == '+' else -1 for value in text)


def branches(models):
    for model in models:
        for quad in DIAGONAL_QUADS:
            if model[QUADS.index(quad)] > 0:
                yield model, quad


def signed_rows(model):
    return tuple(primitive(tuple(sign * value for value in row))
                 for sign, row in zip(model, geometry_rows()[0]))


def produce():
    import numpy as np
    from scipy.optimize import linprog
    from solver_sat import FastSAT

    n, clauses = source_formula()
    models = []
    with FastSAT(n, clauses) as solver:
        while solver.check() == 1:
            model = tuple(solver.model())
            models.append(model)
            solver.add([-(i + 1) * sign for i, sign in enumerate(model)])
        assert solver.check() == -1
    models.sort()
    assert len(models) == 50
    records = []
    for model, branch in branches(models):
        forms = signed_rows(model)
        unique = {}
        for i, row in enumerate(forms):
            if any(row):
                unique.setdefault(row, i)
        polys = {}
        for first, second in combinations_with_replacement(unique.values(), 2):
            row = primitive(product_row(forms[first], forms[second]))
            if any(row):
                polys.setdefault(row, ['weak', first, second])
        strict_indices = [QUADS.index(quad) for quad in STRICT_QUADS + (branch,)]
        strict = [(primitive(product_row(forms[i], forms[j])), ['strict', i, j])
                  for i, j in combinations_with_replacement(strict_indices, 2)]
        gp = geometry_rows()[1]
        columns = list(polys) + [row for row, _ in strict] + list(gp)
        descriptions = list(polys.values()) + [description for _, description in strict] + [['gp', i] for i in range(len(gp))]
        nw, ns, ng = len(polys), len(strict), len(gp)
        matrix = np.array(columns, dtype=int).T
        matrix = np.vstack([matrix, np.r_[np.zeros(nw, dtype=int), np.ones(ns, dtype=int), np.zeros(ng, dtype=int)]])
        target = np.r_[np.zeros(120, dtype=int), 1]
        result = linprog(np.r_[np.ones(nw), np.zeros(ns + ng)], A_eq=matrix, b_eq=target,
                         bounds=[(0, None)] * (nw + ns) + [(None, None)] * ng,
                         method='highs', options={'time_limit': 3})
        if not result.success:
            raise RuntimeError(f'no certificate for {word(model)} {branch}: {result.message}')
        support = [i for i, value in enumerate(result.x) if abs(value) > 1e-8]
        active = sym.Matrix(matrix[:, support])
        weights, parameters = active.gauss_jordan_solve(sym.Matrix(target))
        if parameters.rows:
            weights = weights.subs({parameter: 0 for parameter in parameters})
        assert active * weights == sym.Matrix(target)
        assert all(weight >= 0 for i, weight in zip(support, weights) if i < nw + ns)
        records.append({'word': word(model), 'strict_branch': list(branch),
                        'terms': [[descriptions[i], str(weight)] for i, weight in zip(support, weights) if weight]})
    return {'models': [word(model) for model in models], 'certificates': records}


def verify(packet, directory):
    identities = symbolic_checks()
    models = [signs(text) for text in packet['models']]
    assert len(models) == len(set(models)) == 50 and models == sorted(models)
    for model in models:
        assert all(model[abs(row[0]) - 1] * (1 if row[0] > 0 else -1) > 0 for row in angles.cap_units(1))
        assert all(model[QUADS.index(quad)] == sign for quad, sign in turning.METRIC_SIGNS)
        assert any(model[QUADS.index(quad)] > 0 for quad in DIAGONAL_QUADS)
    expected = list(branches(models))
    assert len(packet['certificates']) == len(expected)
    terms_checked = 0
    for record, (model, branch) in zip(packet['certificates'], expected):
        assert record['word'] == word(model) and record['strict_branch'] == list(branch)
        forms = signed_rows(model)
        strict_indices = {QUADS.index(quad) for quad in STRICT_QUADS + (branch,)}
        total = [Fraction(0)] * 120
        strict_total = Fraction(0)
        assert record['terms']
        for description, weight_text in record['terms']:
            weight = Fraction(weight_text)
            kind, *indices = description
            if kind == 'gp':
                assert len(indices) == 1 and 0 <= indices[0] < 15
                row = geometry_rows()[1][indices[0]]
            else:
                assert kind in ('weak', 'strict') and len(indices) == 2
                assert all(type(i) is int and 0 <= i < 70 for i in indices)
                assert weight >= 0
                if kind == 'strict':
                    assert set(indices) <= strict_indices
                    strict_total += weight
                row = primitive(product_row(forms[indices[0]], forms[indices[1]]))
                assert any(row)
            for i, coefficient in enumerate(row):
                total[i] += weight * coefficient
            terms_checked += 1
        assert not any(total) and strict_total == 1
    directory.mkdir(parents=True, exist_ok=True)
    n, clauses = source_formula()
    coverage = clauses + [[-(i + 1) * sign for i, sign in enumerate(model)] for model in models]
    write_cnf(directory / 'c0_diagonal_complete_cover.cnf', n, coverage)
    result = {'identities': identities, 'generic_models': len(models),
              'actual_strict_branches': len(expected), 'exact_certificate_terms': terms_checked,
              'source_coverage_cnfs': 1,
              'regular_ray1_diagonal_excluded_after_independent_coverage_replay': True,
              'off_diagonal_or_degenerate_caps_excluded': False}
    (directory / 'verification.json').write_text(json.dumps(result, indent=2) + '\n')
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('output', type=Path)
    parser.add_argument('--produce', action='store_true')
    args = parser.parse_args()
    started = time.monotonic()
    packet = produce() if args.produce else json.loads(DEFAULT_DATA.read_text())
    result = verify(packet, args.output)
    if args.produce:
        DEFAULT_DATA.write_text(json.dumps(packet, separators=(',', ':')) + '\n')
    result['seconds'] = round(time.monotonic() - started, 3)
    print(json.dumps(result), flush=True)


if __name__ == '__main__':
    if not __debug__:
        raise RuntimeError('run with assertions enabled')
    main()
