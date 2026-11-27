#!/usr/bin/env python3
"""Exact finite reduction when one limiting cap is a line.

Usage: python remaining_one_collinear.py [OUTPUT_DIRECTORY]

The necessary weak-sign cells and exact stress inequalities reduce every
one-collinear/one-noncollinear ray-3 limit to the canonical one-V family
treated by remaining_one_v.py.  See remaining_one_collinear.md for the
analytic bridge.  This is an asymptotic research theorem, not a fixed-y
exclusion or a Lean proof.  Generated certificates belong outside the repo.
"""

from collections import Counter
from functools import lru_cache
from itertools import combinations, product
import json
from pathlib import Path
import sys

from solver_chambers import base_formula, enumerate_models, marked_symmetries
from verify_linking import SAT, lit

A = (0, 1, 4, 5)
B = (2, 3, 6, 7)
PAIRS = tuple(combinations(range(4), 2))
TRIPLES = tuple(combinations(range(4), 3))
MASK = ((1, 0, 1, 1), (1, 0, 0, 0), (1, 1, 1, 0), (0, 0, 1, 0))


def sign(value):
    return (value > 0) - (value < 0)


def weak_orders():
    """Every nonconstant ordered partition of four labelled points."""
    result = tuple(ranks for ranks in product(range(4), repeat=4)
                   if set(ranks) == set(range(max(ranks) + 1)) and max(ranks))
    assert len(result) == 74
    return result


ORDERS = weak_orders()


def pair_sign(ranks, i, j):
    return sign(ranks[j] - ranks[i])


def zero_sum_possible(terms):
    return not any(terms) or min(terms) < 0 < max(terms)


def rank_three_axioms(size, sorted_sign):
    """Necessary three-term determinant signs, retaining every zero case."""
    def bracket(points):
        parity = (-1) ** sum(points[i] > points[j]
                             for i, j in combinations(range(3), 2))
        return parity * sorted_sign(tuple(sorted(points)))

    for common in range(size):
        for a, b, c, d in combinations([v for v in range(size) if v != common], 4):
            terms = (bracket((common, a, b)) * bracket((common, c, d)),
                     -bracket((common, a, c)) * bracket((common, b, d)),
                     bracket((common, a, d)) * bracket((common, b, c)))
            if not zero_sum_possible(terms):
                return False
    return True


@lru_cache(None)
def vertical_compatible(y, beta):
    # Point 0 is E=(1,0,0) at infinity; the other four have final
    # homogeneous coordinate 1.  [E,Bi,Bj]=-(Yj-Yi).
    def bracket(points):
        if points[0] == 0:
            return -pair_sign(y, points[1] - 1, points[2] - 1)
        return beta[TRIPLES.index(tuple(v - 1 for v in points))]
    return rank_three_axioms(5, bracket)


@lru_cache(None)
def axes_compatible(x, y, beta):
    # E=(1,0,0), F=(0,1,0), Bi=(Xi,Yi,1).  In particular
    # [E,F,Bi]=1, [E,Bi,Bj]=-(Yj-Yi), [F,Bi,Bj]=Xj-Xi.
    def bracket(points):
        if points[:2] == (0, 1):
            return 1
        if points[0] == 0:
            return -pair_sign(y, points[1] - 2, points[2] - 2)
        if points[0] == 1:
            return pair_sign(x, points[1] - 2, points[2] - 2)
        return beta[TRIPLES.index(tuple(v - 2 for v in points))]
    return rank_three_axioms(6, bracket)


def noncollinear_patterns():
    result = []
    for beta in product((-1, 0, 1), repeat=4):
        cofactors = [(-1)**i * beta[TRIPLES.index(tuple(j for j in range(4) if j != i))]
                     for i in range(4)]
        # The nonzero affine cofactors sum to zero.  They must have
        # both signs; all-zero beta would describe a collinear cap.
        if min(cofactors) < 0 < max(cofactors):
            result.append(beta)
    assert len(result) == 50
    return result


def sign_cells(models):
    all_models = (1 << len(models)) - 1
    bits = {(q, value): sum(1 << i for i, model in enumerate(models) if model[q - 1] == value)
            for q in range(1, 71) for value in (-1, 1)}

    def supporting(points, value):
        literal = lit(points)
        return bits[abs(literal), value * sign(literal)]

    beta_masks = []
    for beta in noncollinear_patterns():
        mask = all_models
        for triple, value in zip(TRIPLES, beta):
            if value:
                for vertex in A:
                    mask &= supporting(tuple(B[i] for i in triple) + (vertex,), -value)
        if mask:
            beta_masks.append((beta, mask))
    assert len(beta_masks) == 22

    result = []
    for a, y in product(ORDERS, repeat=2):
        mask = all_models
        for i, j in PAIRS:
            left = pair_sign(a, i, j)
            if not left:
                continue
            for k, l in PAIRS:
                right = pair_sign(y, k, l)
                if right:
                    mask &= supporting((A[i], A[j], B[k], B[l]), -left * right)
        if not mask:
            continue
        for beta, beta_mask in beta_masks:
            witnesses = mask & beta_mask
            if witnesses and vertical_compatible(y, beta):
                result.append((a, y, beta, witnesses))
    assert len(result) == 642
    return result


def edge_differences(points):
    return tuple(points[(i + 1) % 4] - points[i] for i in range(4))


def stress_projection(a, x):
    e, f = edge_differences(a), edge_differences(x)
    h, k = tuple(map(abs, e)), tuple(map(abs, f))
    return (2 * sum(MASK[i][j] * (h[i] * k[j] - e[i] * f[j])
                    for i, j in product(range(4), repeat=2)) - sum(h) * sum(k))


def step(ranks, gap):
    return tuple(int(value > gap) for value in ranks)


@lru_cache(None)
def projected_coefficients(a, x):
    # Positive consecutive gaps generate the complete weak-order cone.
    # In that cone every absolute edge displacement is linear.  Thus
    # these are exactly the coefficients of the bilinear stress F0.
    return tuple(stress_projection(step(a, i), step(x, j))
                 for i in range(max(a)) for j in range(max(x)))


@lru_cache(None)
def lambda_coefficients(a):
    result = []
    for gap in range(max(a)):
        h = tuple(map(abs, edge_differences(step(a, gap))))
        result.append(tuple(2 * sum(MASK[i][j] * h[i] for i in range(4)) - sum(h)
                            for j in range(4)))
    # For a closed scalar polygon each edge length is at most half its
    # perimeter.  Check the corresponding coefficient signs directly.
    for j in range(4):
        column = [row[j] for row in result]
        assert all(value >= 0 for value in column) or all(value <= 0 for value in column)
    return tuple(result)


def stress_excludes(a, x, y, groups=((0,), (1,), (2,), (3,))):
    """Certify one strict sign of F0 + sum(lambda_j*norm_excess_j)."""
    projected = projected_coefficients(a, x)
    lambdas = lambda_coefficients(a)
    active = []
    for group in groups:
        # A nonhorizontal edge has strictly positive Euclidean norm
        # excess.  Horizontally directed edges have exactly zero excess.
        nonhorizontal = [y[j] != y[(j + 1) % 4] for j in group]
        assert len(set(nonhorizontal)) == 1
        if nonhorizontal[0]:
            active.extend(sum(row[j] for j in group) for row in lambdas)
    for direction in (-1, 1):
        if (all(direction * value >= 0 for value in projected + tuple(active))
                and any(projected + tuple(active))):
            return True
    return False


def classify(cells, symmetries):
    counts = Counter()
    remaining = []
    for a, y, beta, witnesses in cells:
        for x in ORDERS:
            if not axes_compatible(x, y, beta):
                continue
            counts['refined_cells'] += 1
            if stress_excludes(a, x, y):
                counts['individual_norm_exclusions'] += 1
                continue
            zeros = tuple(i for i, value in enumerate(beta) if not value)
            if zeros == (0, 2):
                pair, groups = (0, 2), ((0, 1), (2, 3))
            elif zeros == (1, 3):
                pair, groups = (1, 3), ((0, 3), (1, 2))
            else:
                raise AssertionError(('unclassified noncollinear B shape', a, x, y, beta))
            # Two zero triangles through a common pair force that pair
            # to coincide, since all four B points are not collinear.
            assert x[pair[0]] == x[pair[1]] and y[pair[0]] == y[pair[1]]
            # Oppositely traversed equal vectors have equal norm excess.
            # Check that every grouped coefficient has one fixed sign
            # over the full positive A-gap cone, not just at unit gaps.
            for group in groups:
                coefficients = [sum(row[j] for j in group) for row in lambda_coefficients(a)]
                assert all(v >= 0 for v in coefficients) or all(v <= 0 for v in coefficients)
            if stress_excludes(a, x, y, groups):
                counts['paired_norm_exclusions'] += 1
                continue
            multiplicities = Counter(a)
            assert sorted(multiplicities.values()) == [1, 3]
            tip = A[next(i for i, value in enumerate(a) if multiplicities[value] == 1)]
            coincidence = tuple(B[i] for i in pair)
            maps = [entry['permutation'] for entry in symmetries if entry['phase_preserving']
                    and entry['permutation'][5] == tip
                    and {entry['permutation'][v] for v in (0, 1, 4)} == set(A) - {tip}
                    and {entry['permutation'][v] for v in (2, 6)} == set(coincidence)]
            assert maps
            remaining.append({'a': a, 'x': x, 'y': y, 'beta': beta,
                              'tip': tip, 'coincident_pair': coincidence,
                              'canonical_permutation': maps[0],
                              'models': [i for i in range(1888) if witnesses >> i & 1]})
    assert counts == Counter(refined_cells=4786, individual_norm_exclusions=4286,
                             paired_norm_exclusions=160), counts
    assert len(remaining) == 340
    assert len({(r['a'], r['y'], r['beta']) for r in remaining}) == 60
    assert {(r['tip'], r['coincident_pair']) for r in remaining} == {
        (1, (2, 6)), (5, (2, 6)), (0, (3, 7)), (4, (3, 7))}
    # A cap-exchanging exact marked symmetry covers the reverse case.
    assert any({entry['permutation'][i] for i in A} == set(B)
               for entry in symmetries if entry['phase_preserving'])
    return counts, remaining


def write_cnf(path, variables, clauses):
    path.write_text(f'p cnf {variables} {len(clauses)}\n' + ''.join(
        ' '.join(map(str, row)) + ' 0\n' for row in clauses))


def main():
    if not __debug__:
        raise RuntimeError('run with assertions enabled')
    if len(sys.argv) > 2:
        raise SystemExit(__doc__)
    output = Path(sys.argv[1]) if len(sys.argv) == 2 else None
    if output:
        output.mkdir(parents=True, exist_ok=True)
    symmetries = marked_symmetries()
    variables, clauses, *_ = base_formula()
    models = enumerate_models(variables, clauses, symmetries)
    coverage = clauses + [[-(i + 1) * value for i, value in enumerate(model)] for model in models]
    assert SAT(variables, coverage).check() == -1
    print(f'PASS complete weak-sign cover: {len(models)} models', flush=True)
    cells = sign_cells(models)
    counts, remaining = classify(cells, symmetries)
    print('PASS 642 weak-order cells; ' + ', '.join(f'{k}={v}' for k, v in counts.items()), flush=True)
    print('PASS all 340 survivors map to A014 coincident, tip5, and B2=B6 with nonparallel arms3,7', flush=True)
    if output:
        write_cnf(output / 'one_collinear_model_coverage.cnf', variables, coverage)
        (output / 'one_collinear_cells.json').write_text(json.dumps({
            'counts': counts, 'remaining': remaining,
            'all_models': [''.join('+' if value > 0 else '-' for value in model) for model in models]
        }, indent=2) + '\n')
    print('Next certificate: remaining_one_v.py; this alone is a reduction, not an exclusion.')


if __name__ == '__main__':
    main()
