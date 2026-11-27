#!/usr/bin/env python3
"""Complete two-line order check for a common-line transverse blow-up.

The physical limiting length is |Delta X|, not the stretched Euclidean
length. See common_line_edge_collapse.md for the global consequence.
"""

from collections import Counter
from itertools import combinations, product
import json
from pathlib import Path
import sys

import exhaustive_collinear_caps as collinear
import solver_chambers as chambers


def check(models):
    all_bits = (1 << 70)-1
    signed_models = []
    for model in models:
        value = sum(1 << i for i, sign in enumerate(model) if sign > 0)
        signed_models.extend((value, all_bits ^ value))
    requirements = [
        (i, j, k, l, abs(chambers.lit((a, b, c, d)))-1,
         -collinear.sign(chambers.lit((a, b, c, d))))
        for (i, a), (j, b) in combinations(enumerate(collinear.A), 2)
        for (k, c), (l, d) in combinations(enumerate(collinear.B), 2)
    ]
    orders = collinear.weak_orders()
    assert len(orders) == 74
    counts = Counter()
    zeros = []
    for a, b in product(orders, repeat=2):
        positive = negative = 0
        for i, j, k, l, index, parity in requirements:
            sign = collinear.sign(a[j]-a[i])*collinear.sign(b[l]-b[k])*parity
            if sign > 0:
                positive |= 1 << index
            elif sign < 0:
                negative |= 1 << index
        if not any(positive & model == positive and negative & model == 0
                   for model in signed_models):
            counts['orientation_excluded'] += 1
            continue
        # Coordinates on both stretched lines are measured by their
        # original physical X components. The physical dot product is
        # therefore exactly the endpoint cos(theta)=+1 expression,
        # including scalar edge steps of either sign.
        plus, _ = collinear.stress_endpoints(a, b)
        coefficients = sum(plus, [])
        assert all(value >= 0 for value in coefficients) or all(value <= 0 for value in coefficients)
        if any(coefficients):
            counts['strict_stress_excluded'] += 1
            continue
        counts['zero_stress'] += 1
        zero_a = tuple(i for i in range(4) if a[i] == a[(i+1) % 4])
        zero_b = tuple(i for i in range(4) if b[i] == b[(i+1) % 4])
        assert zero_a or zero_b
        zeros.append({'a': a, 'b': b, 'zero_a_edges': zero_a, 'zero_b_edges': zero_b})
    assert counts == Counter(orientation_excluded=4140, strict_stress_excluded=712, zero_stress=624)
    assert len(zeros) == 624
    return counts, zeros


def main():
    if not __debug__:
        raise RuntimeError('run with assertions enabled')
    if len(sys.argv) > 2:
        raise SystemExit(__doc__)
    symmetries = chambers.marked_symmetries()
    n, clauses, *_ = chambers.base_formula()
    models = chambers.enumerate_models(n, clauses, symmetries)
    counts, zeros = check(models)
    assert sum(len(row['zero_a_edges'])+len(row['zero_b_edges']) == 1 for row in zeros) == 16
    print('PASS all 5,476 weak-order pairs:', dict(counts))
    print('PASS every zero-stress survivor has a zero physical short-edge weight')
    print('PASS exactly 16 orders have one zero weight; the separate two-line proof excludes them')
    if len(sys.argv) == 2:
        output = Path(sys.argv[1])
        output.mkdir(parents=True, exist_ok=True)
        (output/'two_line_zero_orders.json').write_text(json.dumps(zeros, separators=(',', ':'))+'\n')
        blocked = clauses + [[-(i+1)*value for i, value in enumerate(model)] for model in models]
        chambers.write_cnf(output/'two_line_model_coverage.cnf', n, blocked)
    print('The second-smallest-weight theorem additionally uses both one-zero mixed proofs and the two-line proof.')


if __name__ == '__main__':
    main()
