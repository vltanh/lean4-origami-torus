#!/usr/bin/env python3
"""Exact weak-chamber simplification on the actual Type 5 sign archive.

No floating arithmetic, search solver, or general-position assumption is used.
The geometric meaning of the two propagation rules is proved in
weak_chamber_reduction.md. Historical SAT completeness is an inherited premise.
"""
from collections import Counter
from itertools import combinations
from pathlib import Path
import json
import sys

if not __debug__:
    raise RuntimeError('Run the exact checker with assertions enabled (without -O).')

HERE = Path(__file__).resolve().parent
SOURCE = HERE.parent / 'type5_focus'
sys.path.insert(0, str(SOURCE))
import focused_system as fs

V = tuple(range(8))
Q = tuple(combinations(V, 4))
INDEX = {q: i for i, q in enumerate(Q)}
EDGES = frozenset(fs.E)
CLIQUES = frozenset(q for q in Q if all(e in EDGES for e in combinations(q, 2)))
assert CLIQUES == frozenset(fs.cl), 'clique archive must agree with the face-list graph'
assert all(any(set(face) <= set(q) for q in CLIQUES) for face in fs.F)
SIMPLICES = frozenset([(i,) for i in V] + list(EDGES) +
                      [tuple(sorted(f)) for f in fs.F])
EXCLUDED = '+----++-+-++++-+++--+++++++-+--------+-+----++-+--++-++++-+-------++--'


def sign(pattern, ordered):
    """Sign of an ordered affine bracket, including permutation parity."""
    inversions = sum(a > b for i, a in enumerate(ordered)
                     for b in ordered[i + 1:])
    return (-1) ** inversions * (1 if pattern[INDEX[tuple(sorted(ordered))]] == '+' else -1)


def strict_closure(pattern):
    """Propagate only sound strictness consequences of the weak chamber."""
    assert len(pattern) == len(Q) and set(pattern) <= {'+', '-'}
    strict = set(CLIQUES)
    rounds = []
    while True:
        new = set()
        # If bracket q vanished, a five-point cofactor relation would have
        # support in q. At least one other strict cofactor makes it nonzero.
        for union in combinations(V, 5):
            cof = {v: (-1) ** i * sign(pattern, tuple(x for x in union if x != v))
                   for i, v in enumerate(union)}
            for omitted in union:
                q = tuple(v for v in union if v != omitted)
                if q in strict:
                    continue
                if not any(tuple(x for x in union if x != v) in strict for v in q):
                    continue
                positive = tuple(v for v in q if cof[v] > 0)
                negative = tuple(v for v in q if cof[v] < 0)
                forbidden = (not positive or not negative or
                             (positive in SIMPLICES and negative in SIMPLICES) or
                             (len(positive) == 1 and all(
                                 tuple(sorted((positive[0], j))) in EDGES for j in negative)) or
                             (len(negative) == 1 and all(
                                 tuple(sorted((negative[0], j))) in EDGES for j in positive)))
                if forbidden:
                    new.add(q)
        # A signed three-term GP identity is sum of two nonnegative products
        # = a third nonnegative product. A strictly positive summand forces
        # both factors of the right-hand product to be nonzero.
        for common in combinations(V, 2):
            remaining = tuple(i for i in V if i not in common)
            for a, b, c, d in combinations(remaining, 4):
                products = [(common + (a, b), common + (c, d)),
                            (common + (a, c), common + (b, d)),
                            (common + (a, d), common + (b, c))]
                signs = [(-1) ** k * sign(pattern, x) * sign(pattern, y)
                         for k, (x, y) in enumerate(products)]
                assert abs(sum(signs)) == 1, 'archive violates a GP sign axiom'
                lone = signs.index(-sum(signs))
                if any(all(tuple(sorted(q)) in strict for q in pair)
                       for k, pair in enumerate(products) if k != lone):
                    new.update(tuple(sorted(q)) for q in products[lone])
        new -= strict
        if not new:
            return frozenset(strict), tuple(rounds)
        rounds.append(len(new))
        strict.update(new)


def remaining_circuits(pattern, strict):
    """All still-possible intersecting minimal circuits, modulo extension.

Every minimal affine dependence extends to a five-point cofactor relation
using a basis of the globally spanning point set. The global independence
test is essential: every subset of a strict tetrahedron is independent.
"""
    result = set()
    for union in combinations(V, 5):
        cof = {v: (-1) ** i * sign(pattern, tuple(x for x in union if x != v))
               for i, v in enumerate(union)}
        mandatory = {v for v in union if tuple(x for x in union if x != v) in strict}
        for size in range(2, 6):
            for support in combinations(union, size):
                if not mandatory <= set(support):
                    continue
                if any(set(support) <= set(q) for q in strict):
                    continue
                positive = tuple(v for v in support if cof[v] > 0)
                negative = tuple(v for v in support if cof[v] < 0)
                if positive in SIMPLICES and negative in SIMPLICES:
                    result.add(tuple(sorted((positive, negative))))
    return tuple(sorted(result))


def audit(pattern):
    strict, rounds = strict_closure(pattern)
    return strict, remaining_circuits(pattern, strict), rounds


def main():
    archive = json.loads((SOURCE / 'full_sign_orbits5.json').read_text())
    branches = json.loads((SOURCE / 'branch_ledger' / 'branches.json').read_text())
    assert len(archive) == 751 and len(set(archive)) == 751
    assert len(CLIQUES) == 23 and EXCLUDED in archive
    counts, strict_counts, remaining_counts = Counter(), Counter(), Counter()
    for pattern in archive:
        strict, residual, _ = audit(pattern)
        counts[len(residual)] += 1
        strict_counts[len(strict)] += 1
        assert all(len(a) + len(b) == 4 for a, b in residual)
        if pattern != EXCLUDED:
            remaining_counts[len(residual)] += 1
    assert counts == {0: 701, 1: 10, 2: 40}, counts
    assert remaining_counts == {0: 700, 1: 10, 2: 40}, remaining_counts
    expected = [67, 66, 66, 67, 65, 66, 66, 67, 65, 65, 66, 66, 67, 67]
    b11 = next(b for b in branches if b['id'] == 'B1.1')
    actual = []
    for pattern in b11['chambers']:
        strict, residual, _ = audit(pattern)
        assert not residual
        actual.append(len(strict))
    assert actual == expected
    print('PASS: 751 actual archive representatives; 23 initial strict clique brackets')
    print('Forced strict-bracket histogram:', dict(sorted(strict_counts.items())))
    print('Remaining circuit exclusions per archived orbit:', dict(sorted(counts.items())))
    print('After the previously proved final-polynomial exclusion:', dict(sorted(remaining_counts.items())))
    print('B1.1 strict-bracket counts:', actual)
    print('PASS: all 14 B1.1 weak chambers imply embeddedness after strictness propagation')
    print('No new chamber infeasibility, realization, or universality conclusion.')


if __name__ == '__main__':
    main()
