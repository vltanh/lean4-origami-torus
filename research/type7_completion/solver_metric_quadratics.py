#!/usr/bin/env python3
"""Exact quadratic raw-bracket cone certificates, with symmetry reuse.

Every inequality is a proved metric difference multiplied by one
nonnegative raw bracket magnitude.  Every equality is an affine cocycle
times one magnitude, or a Grassmann--Pluecker relation.  Integer/Fraction
replay checks a nonnegative residual with a strictly positive K4 product.
No floating solver or numerical tolerance is used by this checker.
"""

from collections import Counter
from fractions import Fraction as F
from itertools import combinations
import json
from pathlib import Path

import solver_metric_certificates as metric
import solver_metric_differences as differences

DATA = json.loads(Path(__file__).with_suffix('.json').read_text())
CERTIFICATES = {row['reference_case']: row for row in DATA['certificates']}
COVERAGE = {row['signs']: row for row in DATA['coverage']}
CASES = tuple(row['chamber'] for row in DATA['coverage'])
assert len(CERTIFICATES) == len(DATA['certificates'])
assert len(COVERAGE) == len(DATA['coverage'])
assert DATA['valid_for'] == 'y>=8' and F(DATA['coefficient']) == F(1, 8)


def product(a, b):
    assert a in metric.INDEX and b in metric.INDEX
    return tuple(sorted((a, b)))


def gp_row(model, common, others):
    """Expand a universal three-term GP identity in raw magnitudes."""
    assert len(common) == 2 and len(others) == 4
    assert tuple(sorted(set(common))) == common
    assert tuple(sorted(set(others))) == others
    assert len(set(common + others)) == 6
    assert set(common + others) <= set(range(8))
    a, b, c, d = others
    pairs = ((common + (a, b), common + (c, d)),
             (common + (a, c), common + (b, d)),
             (common + (a, d), common + (b, c)))
    result = {}
    for i, (u, v) in enumerate(pairs):
        monomial = product(tuple(sorted(u)), tuple(sorted(v)))
        result[monomial] = result.get(monomial, F(0)) + (
            (-1)**i * metric.sign(model, u) * metric.sign(model, v))
    return result


def expand(model, certificate, symmetries):
    """Reconstruct all sources and sum their exact quadratic coefficients."""
    coefficient = F(certificate['coefficient'])
    assert coefficient == F(1, 8)
    phase = set(metric.phase_permutations(symmetries))
    assert len(phase) == 16
    result = {}
    weights = []

    def add(row, weight):
        for monomial, value in row.items():
            result[monomial] = result.get(monomial, F(0)) + weight * value

    for entry in certificate['metric_rows']:
        weight = entry['weight']
        assert isinstance(weight, int) and not isinstance(weight, bool) and weight > 0
        permutation, pair, direction = entry['source']
        permutation, pair = tuple(permutation), tuple(pair)
        assert permutation in phase
        multiplier = tuple(entry['multiplier'])
        assert multiplier in metric.INDEX
        row = differences.metric_row(model, permutation, pair, direction, coefficient)
        add({product(q, multiplier): value for q, value in row.items()}, weight)
        weights.append(weight)
    for entry in certificate['identity_rows']:
        weight = entry['weight']
        assert isinstance(weight, int) and not isinstance(weight, bool) and weight != 0
        if entry['kind'] == 'cocycle':
            multiplier = tuple(entry['multiplier'])
            assert multiplier in metric.INDEX
            row = differences.cocycle_row(model, tuple(entry['support']))
            add({product(q, multiplier): value for q, value in row.items()}, weight)
        elif entry['kind'] == 'gp':
            add(gp_row(model, tuple(entry['common']), tuple(entry['others'])), weight)
        else:
            raise AssertionError(entry['kind'])
        weights.append(weight)
    return {q: value for q, value in result.items() if value}, weights


def verify(model, symmetries, edges):
    """Replay the certificate named by the complete weak sign model."""
    assert len(model) == 70 and all(v in (-1, 1) for v in model)
    key = ''.join('+' if v > 0 else '-' for v in model)
    entry = COVERAGE.get(key)
    if entry is None:
        return None
    permutation = tuple(entry['permutation'])
    assert permutation in metric.phase_permutations(symmetries)
    mapped = tuple(metric.sign(model, tuple(permutation[v] for v in q)) for q in metric.QUADS)
    orientation = mapped[0]
    mapped = tuple(orientation * value for value in mapped)
    certificate = CERTIFICATES[entry['certificate']]
    residual, weights = expand(mapped, certificate, symmetries)
    assert residual and all(value >= 0 for value in residual.values())
    # Relabel both factors back to the original graph before asserting
    # strictness.  Every other raw magnitude may be zero.
    strict_product = None
    for monomial, value in sorted(residual.items()):
        actual = tuple(tuple(sorted(permutation[v] for v in q)) for q in monomial)
        if value > 0 and all(set(combinations(q, 2)) <= set(edges) for q in actual):
            strict_product = monomial
            break
    assert strict_product is not None
    counts = Counter(row['kind'] for row in certificate['identity_rows'])
    return {'certificate_case': entry['certificate'], 'valid_for': 'y>=8',
            'permutation': permutation, 'orientation': orientation,
            'metric_relations': len(certificate['metric_rows']),
            'cocycle_products': counts['cocycle'], 'gp_relations': counts['gp'],
            'weight_bits': max(abs(v).bit_length() for v in weights),
            'residual_monomials': len(residual),
            'strict_product': strict_product,
            'strict_coefficient': str(residual[strict_product])}


def symbolic_checks():
    import sympy as s

    metric.symbolic_checks()
    # Translation puts the first common point at the origin.  The
    # remaining five points are arbitrary, so this checks the universal
    # ordered identity, including every possible zero determinant.
    points = [s.zeros(3, 1)] + [s.Matrix(s.symbols(f'p{i}x p{i}y p{i}z'))
                              for i in range(1, 6)]
    bracket = lambda a, b: s.Matrix.hstack(points[1], points[a], points[b]).det()
    relation = bracket(2, 3)*bracket(4, 5) - bracket(2, 4)*bracket(3, 5) \
        + bracket(2, 5)*bracket(3, 4)
    assert s.expand(relation) == 0


def main():
    import solver_chambers as compiler

    symbolic_checks()
    symmetries = compiler.marked_symmetries()
    edges = compiler.direct.load_data()[2]
    for key, entry in COVERAGE.items():
        model = tuple(1 if value == '+' else -1 for value in key)
        result = verify(model, symmetries, edges)
        assert result is not None
        print(f"PASS chamber {entry['chamber']}, reference {entry['certificate']}: "
              f"{result['metric_relations']} metric products, "
              f"{result['cocycle_products']} cocycle products, "
              f"{result['gp_relations']} GP identities; y>=8")
    print(f'{len(CASES)} complete weak chambers excluded by exact quadratic certificates.')


if __name__ == '__main__':
    if not __debug__:
        raise RuntimeError('run with assertions enabled')
    main()
