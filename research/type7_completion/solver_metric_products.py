#!/usr/bin/env python3
"""Replay exact finite product certificates for metric chambers 28 and 36.

Each necessary maximum comparison has finitely many alternatives.  The
stored tree covers every alternative, and every leaf cancels all log
variables with positive integer multipliers and leaves a negative
constant.  Replay imports neither a numerical LP solver nor an SMT
solver.  See solver_metric_products.md for positivity and zero cases.
"""
from collections import Counter
from fractions import Fraction as F
from itertools import combinations
import json
from pathlib import Path

import solver_metric_certificates as metric

DATA = json.loads(Path(__file__).with_suffix('.json').read_text())
CERTIFICATES = {row['signs']: row for row in DATA['certificates']}
CASES = (28, 36)
assert tuple(row['chamber'] for row in DATA['certificates']) == CASES
assert len(CERTIFICATES) == len(CASES)
assert DATA['valid_for'] == 'y>=32'


def linear_row(terms, bound=0):
    """An exact inequality sum(coefficient_i * log_i) <= bound."""
    coefficients = Counter()
    for quad, coefficient in terms:
        coefficients[metric.INDEX[tuple(sorted(quad))]] += coefficient
    return tuple(sorted((i, v) for i, v in coefficients.items() if v)), bound


def necessary_rule(model, strict, symmetries, rule, gap):
    """Reconstruct every alternative from its checked geometric source."""
    kind = rule['kind']
    if kind == 'gp':
        common, others = tuple(rule['common']), tuple(rule['others'])
        assert len(common) == 2 and tuple(sorted(set(common))) == common
        assert len(others) == 4 and tuple(sorted(set(others))) == others
        assert not set(common) & set(others)
        assert set(common + others) <= set(range(8))
        a, b, c, d = others
        pairs = ((common+(a, b), common+(c, d)),
                 (common+(a, c), common+(b, d)),
                 (common+(a, d), common+(b, c)))
        signs = [(-1)**i * metric.sign(model, p) * metric.sign(model, q)
                 for i, (p, q) in enumerate(pairs)]
        smaller, dominant = rule['smaller'], rule['dominant']
        assert smaller in range(3) and dominant in range(3) and smaller != dominant
        assert signs[dominant] == -sum(signs)
        left, right = pairs[smaller], pairs[dominant]
        assert all(tuple(sorted(q)) in strict for q in left + right)
        return ((linear_row([(q, 1) for q in left] + [(q, -1) for q in right]),),)

    if kind == 'metric':
        permutation, pair = tuple(rule['permutation']), tuple(rule['cap_pair'])
        sources = [source for source in metric.relative_comparisons(model, symmetries)
                   if tuple(source['permutation']) == permutation
                   and tuple(source['cap_pair']) == pair]
        assert len(sources) == 1
        source = sources[0]
        left = [q for q in source['left'] if q in strict]
        assert left and len(source['right']) == 2
        return tuple(tuple(linear_row(((l, 1), (r, -1)), -gap) for l in left)
                     for r in source['right'])

    if kind == 'cocycle':
        points, left = tuple(rule['support']), tuple(rule['left'])
        assert len(points) == 5 and tuple(sorted(set(points))) == points
        assert set(points) <= set(range(8)) and left in strict
        signed = [(points[:i]+points[i+1:],
                   (-1)**i * model[metric.INDEX[points[:i]+points[i+1:]]])
                  for i in range(5)]
        assert left in dict(signed)
        direction = dict(signed)[left]
        right = [q for q, sign in signed if sign == -direction]
        assert right
        bound = (len(right)-1).bit_length()
        assert len(right) <= 2**bound and bound in (0, 1, 2)
        return tuple((linear_row(((left, 1), (r, -1)), bound),) for r in right)

    raise AssertionError(f'unknown necessary rule: {kind}')


def verify(model, strict, symmetries):
    """Return the checked manifest summary, or None for other chambers.

    As in the other metric certificate modules, the compiler supplies
    its independently replayed strictness set and marked symmetries.
    """
    assert len(model) == 70 and all(value in (-1, 1) for value in model)
    key = ''.join('+' if value > 0 else '-' for value in model)
    certificate = CERTIFICATES.get(key)
    if certificate is None:
        return None
    gap = certificate['gap']
    assert gap == 5
    # At y>=32 the source comparison has coefficient 8/y^2.  Choosing
    # the larger of its two right magnitudes contributes one factor 2.
    assert 2*F(8, 32**2) <= F(1, 2**gap)
    strict = {tuple(q) for q in strict}
    rules = tuple(necessary_rule(model, strict, symmetries, rule, gap)
                  for rule in certificate['rules'])
    root = frozenset((i, 0, j) for i, options in enumerate(rules)
                     if len(options) == 1 for j in range(len(options[0])))
    nodes = leaves = max_weight = max_terms = 0

    def replay(tree, available, split):
        nonlocal nodes, leaves, max_weight, max_terms
        nodes += 1
        if 'weights' in tree:
            assert set(tree) == {'weights'}
            coefficients = Counter()
            bound = 0
            used = set()
            assert tree['weights']
            for entry in tree['weights']:
                assert len(entry) == 4
                i, option, part, weight = entry
                reference = (i, option, part)
                assert reference in available and reference not in used
                assert isinstance(weight, int) and not isinstance(weight, bool) and weight > 0
                used.add(reference)
                row, rhs = rules[i][option][part]
                for variable, value in row:
                    coefficients[variable] += weight*value
                bound += weight*rhs
                max_weight = max(max_weight, weight)
            assert all(value == 0 for value in coefficients.values())
            assert bound < 0
            leaves += 1
            max_terms = max(max_terms, len(used))
            return
        assert set(tree) == {'split', 'branches'}
        i = tree['split']
        assert isinstance(i, int) and not isinstance(i, bool) and 0 <= i < len(rules)
        assert i not in split and len(rules[i]) > 1
        assert len(tree['branches']) == len(rules[i])
        for option, branch in enumerate(tree['branches']):
            added = {(i, option, j) for j in range(len(rules[i][option]))}
            replay(branch, available | added, split | {i})

    replay(certificate['tree'], root, frozenset())
    expected = {28: (173, 121), 36: (53, 30)}
    assert (nodes, leaves) == expected[certificate['chamber']]
    return {'certificate_case': certificate['chamber'], 'valid_for': 'y>=32',
            'rules': len(rules), 'rule_kinds': dict(Counter(
                rule['kind'] for rule in certificate['rules'])),
            'tree_nodes': nodes, 'leaves': leaves, 'max_weight': max_weight,
            'max_terms': max_terms, 'metric_log2_gap': gap}


def main():
    import solver_chambers as compiler

    metric.symbolic_checks()
    symmetries = compiler.marked_symmetries()
    _, _, faces, edges, neighbors = compiler.base_formula()
    for key, certificate in CERTIFICATES.items():
        model = tuple(1 if value == '+' else -1 for value in key)
        strict, _ = compiler.strict_closure(model, faces, edges, neighbors)
        result = verify(model, strict, symmetries)
        assert result is not None
        print(f"PASS chamber {certificate['chamber']}: {result['rules']} necessary rules, "
              f"{result['leaves']} exact product cancellations, y>=32", flush=True)
    print('Two additional complete weak metric chambers excluded; no full marking exclusion.')


if __name__ == '__main__':
    if not __debug__:
        raise RuntimeError('run with assertions enabled')
    main()
