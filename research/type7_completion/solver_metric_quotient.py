#!/usr/bin/env python3
"""Independently replay metric certificates discovered in a smaller quotient.

Replay does NOT construct or trust that quotient.  It expands every
stored raw identity in 21 formal spatial coordinates using the ordinary
3-by-3 determinant formula, and checks exact zero with integer arithmetic.
The remaining metric-product sum is coefficientwise nonnegative and has
a positive product of two nonzero K4 brackets.  Weak zeros are retained.
"""

from collections import Counter
from fractions import Fraction as F
from functools import lru_cache
from itertools import combinations, permutations, product
import json
from math import isqrt
from pathlib import Path

import solver_metric_certificates as metric
import solver_metric_differences as differences

DATA = json.loads(Path(__file__).with_suffix('.json').read_text())
CERTIFICATES = {row['reference_case']: row for row in DATA['certificates']}
COVERAGE = {row['signs']: row for row in DATA['coverage']}
CASES = tuple(row['chamber'] for row in DATA['coverage'])
assert len(CERTIFICATES) == len(DATA['certificates'])
assert len(COVERAGE) == len(DATA['coverage'])
AXIS_PERMUTATIONS = tuple((p, (-1)**sum(p[i] > p[j] for i, j in combinations(range(3), 2)))
                          for p in permutations(range(3)))


def clean(row):
    return {key: value for key, value in row.items() if value}


def anchored_form(q):
    """Express a sorted raw affine bracket using the 35 brackets at 0."""
    assert q in metric.INDEX
    if q[0] == 0:
        return {q[1:]: 1}
    return {q[:i] + q[i + 1:]: (-1)**i for i in range(4)}


@lru_cache(None)
def anchor_determinant(triple):
    """The six signed coordinate monomials of det(r_i,r_j,r_k)."""
    assert len(triple) == 3 and tuple(sorted(set(triple))) == triple
    assert set(triple) <= set(range(1, 8))
    return {tuple(sorted(3*(vertex - 1) + axis for vertex, axis in zip(triple, axes))): sign
            for axes, sign in AXIS_PERMUTATIONS}


def direct_affine_determinant(q):
    """Independently expand det(r_b-r_a,r_c-r_a,r_d-r_a), with r_0=0."""
    a, *others = q
    answer = Counter()
    for axes, sign in AXIS_PERMUTATIONS:
        columns = []
        for vertex, axis in zip(others, axes):
            choices = [(3*(vertex - 1) + axis, 1)] if vertex else []
            if a:
                choices.append((3*(a - 1) + axis, -1))
            columns.append(choices)
        for selected in product(*columns):
            variables, coefficients = zip(*selected)
            answer[tuple(sorted(variables))] += sign * coefficients[0] * coefficients[1] * coefficients[2]
    return clean(answer)


@lru_cache(None)
def anchor_product(a, b):
    answer = Counter()
    for left, left_coefficient in anchor_determinant(a).items():
        for right, right_coefficient in anchor_determinant(b).items():
            answer[tuple(sorted(left + right))] += left_coefficient * right_coefficient
    return clean(answer)


def parse_product(key):
    parts = key.split('*')
    assert len(parts) == 2
    pair = tuple(tuple(map(int, text)) for text in parts)
    assert all(q in metric.INDEX for q in pair) and tuple(sorted(pair)) == pair
    return pair


@lru_cache(None)
def validate_raw_expansions():
    """Check all 70 anchor substitutions against direct coordinate determinants."""
    for q in metric.QUADS:
        anchored = Counter()
        for triple, coefficient in anchored_form(q).items():
            for monomial, value in anchor_determinant(triple).items():
                anchored[monomial] += coefficient * value
        assert clean(anchored) == direct_affine_determinant(q)
    return True


@lru_cache(None)
def verify_identity(reference):
    """Check one stored universal raw identity by exact coordinate expansion."""
    validate_raw_expansions()
    certificate = CERTIFICATES[reference]
    anchored = Counter()
    for key, coefficient in certificate['raw_identity'].items():
        assert isinstance(coefficient, int) and not isinstance(coefficient, bool) and coefficient != 0
        a, b = parse_product(key)
        for u, cu in anchored_form(a).items():
            for v, cv in anchored_form(b).items():
                anchored[tuple(sorted((u, v)))] += coefficient * cu * cv
    coordinates = Counter()
    for (u, v), coefficient in anchored.items():
        if coefficient:
            for monomial, value in anchor_product(u, v).items():
                coordinates[monomial] += coefficient * value
    assert not any(coordinates.values()), f'nonzero universal identity: {reference}'
    return True


def minimum_height(coefficient):
    """The proved source bound 8/y^2 is at most the stored coefficient."""
    assert coefficient > 0
    threshold = F(8) / coefficient
    height = max(8, isqrt(threshold.numerator // threshold.denominator))
    while height*height < threshold:
        height += 1
    assert F(8, height*height) <= coefficient
    return height


def verify(model, symmetries, edges):
    """Return a complete checked manifest summary, or None if not covered."""
    assert len(model) == 70 and all(value in (-1, 1) for value in model)
    key = ''.join('+' if value > 0 else '-' for value in model)
    entry = COVERAGE.get(key)
    if entry is None:
        return None
    reference = entry['reference']
    certificate = CERTIFICATES[reference]
    verify_identity(reference)
    phase = set(metric.phase_permutations(symmetries))
    permutation = tuple(entry['permutation'])
    assert len(phase) == 16 and permutation in phase
    mapped = tuple(metric.sign(model, tuple(permutation[v] for v in q)) for q in metric.QUADS)
    orientation = mapped[0]
    mapped = tuple(value * orientation for value in mapped)
    coefficient = F(certificate['coefficient'])
    residual = Counter()
    weights = []
    for row in certificate['metric_rows']:
        weight = row['weight']
        assert isinstance(weight, int) and not isinstance(weight, bool) and weight > 0
        source, pair, direction = row['source']
        source, pair = tuple(source), tuple(pair)
        multiplier = tuple(row['multiplier'])
        assert source in phase and multiplier in metric.INDEX
        for q, value in differences.metric_row(mapped, source, pair, direction, coefficient).items():
            residual[tuple(sorted((q, multiplier)))] += weight * value
        weights.append(weight)
    # The stored polynomial is identically zero in RAW signed brackets.
    # Convert it to this chamber's magnitude variables before subtracting.
    for key, value in certificate['raw_identity'].items():
        a, b = parse_product(key)
        residual[a, b] -= value * mapped[metric.INDEX[a]] * mapped[metric.INDEX[b]]
    residual = clean(residual)
    assert residual and all(value >= 0 for value in residual.values())
    strict_product = None
    for monomial, value in sorted(residual.items()):
        actual = tuple(tuple(sorted(permutation[v] for v in q)) for q in monomial)
        if value > 0 and all(set(combinations(q, 2)) <= set(edges) for q in actual):
            strict_product = monomial
            break
    assert strict_product is not None
    height = minimum_height(coefficient)
    return {'certificate_case': reference, 'valid_for': f'y>={height}',
            'permutation': permutation, 'orientation': orientation,
            'metric_products': len(certificate['metric_rows']),
            'raw_identity_terms': len(certificate['raw_identity']),
            'weight_bits': max(abs(weight).bit_length() for weight in weights),
            'residual_monomials': len(residual),
            'strict_product': strict_product, 'strict_coefficient': str(residual[strict_product])}


def main():
    import time
    import solver_chambers as compiler

    start = time.monotonic()
    metric.symbolic_checks()
    symmetries = compiler.marked_symmetries()
    edges = compiler.direct.load_data()[2]
    for reference in CERTIFICATES:
        verify_identity(reference)
    for key, entry in COVERAGE.items():
        model = tuple(1 if value == '+' else -1 for value in key)
        result = verify(model, symmetries, edges)
        assert result is not None
        print(f"PASS chamber {entry['chamber']}, reference {entry['reference']}: "
              f"{result['metric_products']} metric products, "
              f"independent coordinate identity; {result['valid_for']}")
    print(f'PASS {len(CASES)} weak chambers, {len(CERTIFICATES)} universal identities, '
          f'all 70 raw substitutions; {time.monotonic() - start:.3f}s')


if __name__ == '__main__':
    if not __debug__:
        raise RuntimeError('run with assertions enabled')
    main()
