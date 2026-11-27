#!/usr/bin/env python3
"""Exact six-relation exclusions of two complete weak ray-3 chambers.

The log-magnitude LP was used only to discover these integer certificates.
Replay uses bracket parity, already-proved nonvanishing, and exact
multiset cancellation. Actual zero cap brackets remain permitted.
"""

from collections import Counter
from itertools import combinations

QUADS = tuple(combinations(range(8), 4))
INDEX = {q: i for i, q in enumerate(QUADS)}
CERTIFICATES = {
    '+---------+++++++++++++++++++++++--++++++++++++++++++--+++++-++--++--+': (
        ((0, 1), (3, 5, 6, 7), 1, 2),
        ((0, 3), (1, 2, 6, 7), 2, 1),
        ((1, 5), (0, 4, 6, 7), 1, 2),
        ((2, 3), (0, 5, 6, 7), 2, 1),
        ((2, 5), (3, 4, 6, 7), 2, 1),
        ((4, 5), (1, 2, 6, 7), 1, 2),
    ),
    '+-++-+--++-++-+++++--+++++++---+--+-++-++-----+--+--+--++-----+--+--++': (
        ((0, 1), (2, 3, 5, 6), 2, 0),
        ((0, 3), (1, 2, 4, 5), 0, 2),
        ((1, 4), (2, 5, 6, 7), 2, 1),
        ((1, 6), (0, 2, 4, 5), 2, 0),
        ((3, 4), (0, 2, 5, 7), 0, 1),
        ((4, 7), (1, 2, 3, 5), 2, 0),
    ),
}


def verify(model, strict):
    """Return an exact certificate summary, or None if not covered.

    strict is supplied by the independently replayed cofactor/GP closure.
    Every compared factor is positive. Four of six inequalities are
    strict, while two may be equalities when nonclique cap minors vanish.
    """
    key = ''.join('+' if value > 0 else '-' for value in model)
    if key not in CERTIFICATES:
        return None
    assert len(model) == 70 and all(value in (-1, 1) for value in model)
    strict = set(strict)

    def sign(q):
        parity = (-1)**sum(q[i] > q[j] for i, j in combinations(range(4), 2))
        return parity*model[INDEX[tuple(sorted(q))]]

    balance = Counter()
    strict_rows = 0
    inequalities = []
    for common, others, dominant, smaller in CERTIFICATES[key]:
        a, b, c, d = others
        assert len(set(common+others)) == 6
        pairs = ((common+(a, b), common+(c, d)),
                 (common+(a, c), common+(b, d)),
                 (common+(a, d), common+(b, c)))
        signs = [(-1)**i*sign(u)*sign(v) for i, (u, v) in enumerate(pairs)]
        assert signs[dominant] == -sum(signs) and dominant != smaller
        other = 3-dominant-smaller
        left = tuple(tuple(sorted(q)) for q in pairs[smaller])
        right = tuple(tuple(sorted(q)) for q in pairs[dominant])
        assert all(q in strict for q in left+right)
        is_strict = all(tuple(sorted(q)) in strict for q in pairs[other])
        strict_rows += is_strict
        balance.update(right)
        balance.subtract(left)
        inequalities.append((left, '<' if is_strict else '<=', right))
    assert len(inequalities) == 6 and strict_rows == 4
    assert all(value == 0 for value in balance.values())
    return {'relations': 6, 'strict_relations': strict_rows,
            'positive_factors': len(balance), 'inequalities': inequalities}


def main():
    import solver_chambers as compiler
    _, _, faces, edges, neighbors = compiler.base_formula()
    for key in CERTIFICATES:
        model = tuple(1 if value == '+' else -1 for value in key)
        strict, _ = compiler.strict_closure(model, faces, edges, neighbors)
        proof = verify(model, strict)
        assert proof is not None
        print(f'PASS six exact inequalities, four strict; '
              f'{proof["positive_factors"]} positive factors cancel')
        for left, comparison, right in proof['inequalities']:
            show = lambda pair: '*'.join('|' + ''.join(map(str, q)) + '|' for q in pair)
            print(f'  {show(left)} {comparison} {show(right)}')
    print('Two complete weak chambers excluded by this module; see the compiler for the combined ledger.')


if __name__ == '__main__':
    if not __debug__:
        raise RuntimeError('run with assertions enabled')
    main()
