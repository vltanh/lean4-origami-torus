#!/usr/bin/env python3
"""Exact linear certificates from all raw-bracket difference bounds.

Unlike the five-sign obstruction, these certificates retain the metric
difference comparison when its two brackets have equal weak signs.
Replay uses integers and Fraction only; the discovery LP is not imported.
See solver_metric_differences.md for the necessary geometric inequality.
"""

from fractions import Fraction as F
from itertools import combinations
import json
from pathlib import Path

import solver_metric_certificates as metric

DATA = json.loads(Path(__file__).with_suffix('.json').read_text())
CERTIFICATES = {row['signs']: row for row in DATA['certificates']}
CASES = (88, 91, 93, 95, 96, 97, 98, 99, 100)
assert tuple(row['chamber'] for row in DATA['certificates']) == CASES
assert len(CERTIFICATES) == len(CASES)
assert DATA['valid_for'] == 'y>=8' and F(DATA['coefficient']) == F(1, 8)


def metric_row(model, permutation, pair, direction, coefficient):
    """Expand one side of |[0ij2]-[0ij3]| <= coefficient*R.

    The dictionary uses nonnegative RAW bracket magnitudes.  The sign
    belongs to the ordered bracket, so relabeling parity is essential.
    """
    i, j = pair
    assert pair in tuple(combinations((1, 4, 5), 2))
    assert direction in (-1, 1)
    row = {}
    for position, endpoint in enumerate((2, 3)):
        ordered = tuple(permutation[v] for v in (0, i, j, endpoint))
        q = tuple(sorted(ordered))
        row[q] = row.get(q, F(0)) + direction * (-1)**position * metric.sign(model, ordered)
    for vertex in (i, j):
        q = tuple(sorted(permutation[v] for v in (0, 2, 3, vertex)))
        row[q] = row.get(q, F(0)) - coefficient
    return row


def cocycle_row(model, support):
    """The five-point affine identity, expressed in raw magnitudes."""
    assert len(support) == 5 and tuple(sorted(set(support))) == support
    assert set(support) <= set(range(8))
    return {support[:i] + support[i + 1:]:
            F((-1)**i * model[metric.INDEX[support[:i] + support[i + 1:]]])
            for i in range(5)}


def verify(model, symmetries, edges):
    """Replay the full coefficient sum, returning a manifest summary."""
    assert len(model) == 70 and all(v in (-1, 1) for v in model)
    key = ''.join('+' if v > 0 else '-' for v in model)
    certificate = CERTIFICATES.get(key)
    if certificate is None:
        return None
    coefficient = F(certificate['mu'])
    assert coefficient == F(1, 8)
    phase = set(metric.phase_permutations(symmetries))
    assert len(phase) == 16
    coefficients = {q: F(0) for q in metric.QUADS}
    weights = []
    for entry in certificate['metric_rows']:
        weight = entry['weight']
        assert isinstance(weight, int) and not isinstance(weight, bool) and weight > 0
        permutation, pair, direction = entry['source']
        permutation, pair = tuple(permutation), tuple(pair)
        assert permutation in phase
        for q, value in metric_row(model, permutation, pair, direction, coefficient).items():
            coefficients[q] += weight * value
        weights.append(weight)
    for entry in certificate['cocycle_rows']:
        weight = entry['weight']
        assert isinstance(weight, int) and not isinstance(weight, bool) and weight != 0
        for q, value in cocycle_row(model, tuple(entry['support'])).items():
            coefficients[q] += weight * value
        weights.append(weight)
    # The weighted metric sum is <=0 and the affine identities equal 0.
    # Every resulting monomial is nonnegative, and one K4 term is positive.
    assert all(value >= 0 for value in coefficients.values())
    clique = tuple(certificate['strict_clique'])
    assert clique in metric.INDEX and set(combinations(clique, 2)) <= set(edges)
    assert coefficients[clique] > 0
    return {'certificate_case': certificate['chamber'], 'valid_for': 'y>=8',
            'metric_relations': len(certificate['metric_rows']),
            'affine_cocycles': len(certificate['cocycle_rows']),
            'weight_bits': max(abs(v).bit_length() for v in weights),
            'strict_clique': clique,
            'positive_coefficients': {''.join(map(str, q)): str(value)
                                      for q, value in coefficients.items() if value}}


def main():
    import solver_chambers as compiler

    # These identities prove the general absolute difference comparison
    # before imposing either equal or opposite signs on its two brackets.
    metric.symbolic_checks()
    symmetries = compiler.marked_symmetries()
    edges = compiler.direct.load_data()[2]
    for key, certificate in CERTIFICATES.items():
        model = tuple(1 if value == '+' else -1 for value in key)
        result = verify(model, symmetries, edges)
        assert result is not None
        print(f"PASS chamber {certificate['chamber']}: "
              f"{result['metric_relations']} metric differences + "
              f"{result['affine_cocycles']} affine cocycles; "
              f"exact nonnegative residual, y>=8")
    print('Nine additional complete weak metric chambers excluded; no full marking exclusion.')


if __name__ == '__main__':
    if not __debug__:
        raise RuntimeError('run with assertions enabled')
    main()
