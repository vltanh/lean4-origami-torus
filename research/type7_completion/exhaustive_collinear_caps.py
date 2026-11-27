#!/usr/bin/env python3
"""Exclude both collinear caps on nonparallel limiting lines, at every rate.

Usage: python exhaustive_collinear_caps.py [OUTPUT_DIRECTORY]
The optional directory receives 12 necessary CNFs for the final
triple-cluster/out-and-back family.  The finite 5,476 weak-order cover
and stress inequalities are exact integer checks, not nonlinear SMT.
See exhaustive_collinear_caps.md for the analytic necessity argument.
"""
from collections import Counter
from itertools import combinations, product
from pathlib import Path
import sys

import sympy as s

import solver_chambers as chambers
from verify_nonparallel_corner import SAT, allowed_sum

A = (0, 1, 4, 5)
B = (2, 3, 6, 7)
MASK = ((1, 0, 1, 1), (1, 0, 0, 0), (1, 1, 1, 0), (0, 0, 1, 0))


def sign(x):
    return (x > 0) - (x < 0)


def weak_orders():
    return tuple(ranks for k in range(2, 5) for ranks in product(range(k), repeat=4)
                 if set(ranks) == set(range(k)))


def gap_steps(ranks):
    return tuple(tuple(int(ranks[(i+1) % 4] > gap) - int(ranks[i] > gap)
                       for i in range(4)) for gap in range(max(ranks)))


def stress_endpoints(ra, rb):
    """Coefficients of F at cos(theta)=+1 and -1 in positive gap variables."""
    plus, minus = [], []
    for a in gap_steps(ra):
        p, m = [], []
        for b in gap_steps(rb):
            q0 = (2*sum(MASK[i][j]*abs(a[i])*abs(b[j]) for i in range(4) for j in range(4))
                  - sum(map(abs, a))*sum(map(abs, b)))
            q1 = -2*sum(MASK[i][j]*a[i]*b[j] for i in range(4) for j in range(4))
            p.append(q0+q1)
            m.append(q0-q1)
        plus.append(p)
        minus.append(m)
    return plus, minus


def order_orbit(seeds, symmetries):
    result = set()
    for ra, rb in seeds:
        for reverse_a, reverse_b in product((False, True), repeat=2):
            aa = tuple(max(ra)-v if reverse_a else v for v in ra)
            bb = tuple(max(rb)-v if reverse_b else v for v in rb)
            values = dict(zip(A, aa)) | dict(zip(B, bb))
            for entry in symmetries:
                if not entry['phase_preserving']:
                    continue
                permutation = entry['permutation']
                pair = []
                for cap in (A, B):
                    ranks = [values[permutation[i]] for i in cap]
                    levels = {v: i for i, v in enumerate(sorted(set(ranks)))}
                    pair.append(tuple(levels[v] for v in ranks))
                result.add(tuple(pair))
    return result


def classify_orders(models, symmetries):
    all_bits = (1 << 70)-1
    model_bits = []
    for model in models:
        value = sum(1 << i for i, x in enumerate(model) if x > 0)
        model_bits += [value, all_bits ^ value]
    requirements = [(i, j, k, l, abs(chambers.lit((a, b, c, d)))-1,
                     -sign(chambers.lit((a, b, c, d))))
                    for (i, a), (j, b) in combinations(enumerate(A), 2)
                    for (k, c), (l, d) in combinations(enumerate(B), 2)]
    orders = weak_orders()
    assert len(orders) == 74
    survivors = set()
    counts = Counter()
    for ra, rb in product(orders, repeat=2):
        positive = negative = 0
        for i, j, k, l, index, direction in requirements:
            value = sign(ra[j]-ra[i])*sign(rb[l]-rb[k])*direction
            if value > 0:
                positive |= 1 << index
            elif value < 0:
                negative |= 1 << index
        if not any(positive & model == positive and negative & model == 0 for model in model_bits):
            counts['orientation_excluded'] += 1
            continue
        plus, minus = stress_endpoints(ra, rb)
        coefficients = sum(plus, []) + sum(minus, [])
        if all(value == 0 for value in coefficients):
            survivors.add((ra, rb))
            counts['zero_stress_family'] += 1
        else:
            assert all(value >= 0 for value in coefficients) or all(value <= 0 for value in coefficients)
            counts['strict_stress_excluded'] += 1
    assert counts == {'orientation_excluded': 4140, 'strict_stress_excluded': 1176,
                      'zero_stress_family': 160}
    corner = order_orbit([((0, 0, 0, 1), (0, 0, 0, 1))], symmetries)
    fold = order_orbit([((0, 0, 0, 1), rb) for rb in
                        ((1, 0, 1, 2), (0, 1, 0, 2), (0, 1, 0, 1), (0, 2, 0, 1))], symmetries)
    assert len(corner) == 32 and len(fold) == 128 and not corner & fold
    assert survivors == corner | fold
    print('PASS 5,476 weak-order pairs:', dict(counts), flush=True)
    print('PASS exact marked cover: 32 two-triple corners and 128 cluster/fold orders', flush=True)


def fold_formula(lambda_value, hierarchy):
    """Necessary formula; hierarchy -1/0/+1 means a dominates/comparable/b dominates."""
    n, clauses, *_ = chambers.base_formula()
    assert clauses[0] == [1]
    clauses = [list(row) for row in clauses[1:]]  # the four anchors fix the frame orientation
    keys = [(0,), (1,), (2,), (3,), (0, 2), (1, 3), 'ab']
    trits = {key: (n+2*i+1, n+2*i+2) for i, key in enumerate(keys)}
    n += 14
    clauses += [[-p, -m] for p, m in trits.values()]
    for i, j in ((0, 1), (2, 3)):
        clauses.append(list(trits[(i,)]) + list(trits[(j,)]))

    def deny(key, value):
        p, m = trits[key]
        return [-p] if value == 1 else [-m] if value == -1 else [p, m]

    for xa, ya, xb, yb, ab in product((-1, 0, 1), repeat=5):
        terms = [ab, -xa*yb, ya*xb]
        if any(terms) and (all(v >= 0 for v in terms) or all(v <= 0 for v in terms)):
            clauses.append(deny((0,), xa) + deny((1,), ya) + deny((2,), xb)
                           + deny((3,), yb) + deny('ab', ab))
    for i, j in ((0, 2), (1, 3)):
        if hierarchy == 0:
            clauses += [deny((i,), a) + deny((j,), b) + deny((i, j), c)
                        for a, b, c in product((-1, 0, 1), repeat=3) if not allowed_sum(a, b, c)]
        else:
            left = trits[(i if hierarchy == -1 else j,)]
            right = trits[(i, j)]
            clauses += [[-x, y] for x, y in zip(left, right)]
            clauses += [[x, -y] for x, y in zip(left, right)]

    ax, ay, bx, by = xs = s.symbols('ax ay bx by')
    eps, lam = s.symbols('eps lam')
    symbolic_points = {
        0: (0, 0, 0), 1: (eps*ax, eps*ay, 0),
        4: (eps*(ax+bx), eps*(ay+by), 0), 5: (1, 0, 0),
        2: (0, 0, 1), 3: (0, lam, 1), 6: (0, 0, 1), 7: (0, 1, 1),
    }
    points = {i: s.Matrix(p).subs(lam, lambda_value) for i, p in symbolic_points.items()}
    base = {i: p.subs(eps, 0) for i, p in points.items()}
    counts = Counter()
    possible_coefficients = {s.Integer(1), s.Integer(-1), lam, -lam, lam-1, 1-lam}
    for idx, quad in enumerate(combinations(range(8), 4), 1):
        a, *rest = quad
        rank = s.Matrix.hstack(*(base[v]-base[a] for v in rest)).rank()
        raw = s.expand(s.Matrix([[symbolic_points[v][k]-symbolic_points[a][k]
                                 for k in range(3)] for v in rest]).det())
        determinant = raw.subs(lam, lambda_value)
        if rank == 3:
            symbolic = s.expand(raw.coeff(eps, 0))
            assert symbolic in possible_coefficients
            leading = symbolic.subs(lam, lambda_value)
            assert leading != 0
            clauses.append([idx if leading > 0 else -idx])
            counts['constant'] += 1
        elif rank == 2 and len(set(quad) & {0, 1, 4}) >= 2:
            symbolic = s.expand(raw.coeff(eps, 1))
            # Every scalar coefficient is ±1, ±lam, or ±(lam-1), so the four
            # lambda cells cover every real nonzero lambda exactly.
            for _, coefficient in s.Poly(symbolic, *xs).terms():
                assert coefficient in possible_coefficients
            leading = s.expand(symbolic.subs(lam, lambda_value))
            coefficients, indices = [], []
            for powers, coefficient in s.Poly(leading, *xs).terms():
                assert sum(powers) == 1
                indices.append(powers.index(1))
                coefficients.append(coefficient)
            assert len(set(coefficients)) == 1 and coefficients[0] != 0
            key = tuple(sorted(indices))
            p, m = trits[key]
            direction = 1 if coefficients[0] > 0 else -1
            clauses += [[-p, direction*idx], [-m, -direction*idx]]
            counts['linear'] += 1
        elif set(quad) & {0, 1, 4} == {0, 1, 4} and len(set(quad) & set(B)) == 1:
            leading = determinant.coeff(eps, 2)
            ratio = s.cancel(leading/(ax*by-ay*bx))
            assert ratio in (-1, 1)
            p, m = trits['ab']
            clauses += [[-p, int(ratio)*idx], [-m, -int(ratio)*idx]]
            counts['quadratic'] += 1
    expected = {'constant': 12, 'linear': 24, 'quadratic': 4} if lambda_value == 1 else {
        'constant': 15, 'linear': 27, 'quadratic': 4}
    assert counts == expected
    return n, clauses, counts


def main():
    if not __debug__:
        raise RuntimeError('run with assertions enabled')
    if len(sys.argv) > 2:
        raise SystemExit(__doc__)
    output = Path(sys.argv[1]) if len(sys.argv) == 2 else None
    if output:
        output.mkdir(parents=True, exist_ok=True)
    symmetries = chambers.marked_symmetries()
    n, clauses, *_ = chambers.base_formula()
    models = chambers.enumerate_models(n, clauses, symmetries)
    classify_orders(models, symmetries)
    cells = (('negative', -1), ('between', s.Rational(1, 2)), ('equal', 1), ('above', 2))
    for (name, value), hierarchy in product(cells, (-1, 0, 1)):
        n, clauses, counts = fold_formula(value, hierarchy)
        assert SAT(n, clauses).check() == -1, (name, hierarchy)
        case = f'fold_{name}_hierarchy_{hierarchy:+d}'.replace('+', 'p').replace('-', 'm')
        print(f'PASS {case}: UNSAT; {n} variables, {len(clauses)} clauses; {dict(counts)}', flush=True)
        if output:
            (output/(case+'.cnf')).write_text(f'p cnf {n} {len(clauses)}\n' + ''.join(
                ' '.join(map(str, row))+' 0\n' for row in clauses))
    print('Scope: excludes both collinear caps on nonparallel limiting lines; common-line and finite-height systems remain open')


if __name__ == '__main__':
    main()
