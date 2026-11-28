#!/usr/bin/env python3
"""Exact sign certificate for the comparable-edge nonparallel two-stick corner.

Usage: python verify_nonparallel_corner.py [OUTPUT.cnf]

The output is a necessary Boolean relaxation, not a fixed-y ray-3 query.
It excludes the limiting configuration and common-scale hypotheses stated
in relative_cap_bounds.md.  Generated CNF files belong outside the source
tree.  Replay with orientation_checkpoint/check_unsat.cpp for an independent
exhaustive Boolean check; the expected result is UNSAT nodes 6137.
"""
from itertools import combinations, product
import json
from pathlib import Path
import sys

import sympy as s

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'linking_checkpoint'))
from verify_linking import CNF, SAT, data, formula, lit, short_pairs


def require_link_values(cnf, a, b, allowed):
    """Signed fan intersections, with the same exact counter as CNF.unlink."""
    events = []
    for i in range(1, len(a) - 1):
        tri = (a[0], a[i], a[i + 1])
        for u, v in zip(b, b[1:] + b[:1]):
            support = tuple(sorted(tri + (u, v)))
            signs = [(1 if vertex in tri else -1) * (-1)**j
                     * lit(support[:j] + support[j + 1:])
                     for j, vertex in enumerate(support)]
            terminal = lit(tri + (v,))
            assert (terminal in signs) != (-terminal in signs)
            if terminal not in signs:
                signs = [-value for value in signs]
            events.append((cnf.conjunction(signs),
                           cnf.conjunction([-value for value in signs])))
    old = {0: cnf.var()}
    cnf.C.append([old[0]])
    for i, (positive, negative) in enumerate(events):
        new = {k: cnf.var() for k in range(-i - 1, i + 2)}
        for k, state in old.items():
            cnf.C.extend([[-state, -positive, new[k + 1]],
                          [-state, -negative, new[k - 1]],
                          [-state, positive, negative, new[k]]])
        old = new
    cnf.C.extend([[-state] for k, state in old.items() if k not in allowed])


def sign(value):
    return (value > 0) - (value < 0)


def allowed_sum(left, right, total):
    if left == 0:
        return total == right
    if right == 0 or left == right:
        return total == left
    return True


def generate():
    n, clauses, _, _, _ = formula(7)
    assert clauses[0] == [1]
    # This formula uses the actual fixed anchor orientation.  The remaining
    # clauses and the absolute linking target are reflection invariant.
    clauses = [list(row) for row in clauses[1:]]
    cases = json.loads((ROOT / 'linking_checkpoint/cases.json').read_text())
    case = next(c for c in cases if c['file'] == 't7_ray_3.smt2')
    shifts, _, _ = data(case)
    extra = CNF(n)
    pairs = short_pairs(shifts)
    assert len(pairs) == 2
    for a, b in pairs:
        extra.unlink(a, b)
    require_link_values(extra, (0, 2, 4, 6), (1, 3, 5, 7), {-2, 2})
    clauses.extend(extra.C)
    n = extra.n

    # Four nonzero transverse tangent vectors a,b,c,d.  Coordinates and
    # their four independent two-term sums have exact three-valued signs.
    xs = s.symbols('ax ay bx by cx cy dx dy')
    ax, ay, bx, by, cx, cy, dx, dy = xs
    keys = [(i,) for i in range(8)] + [(0, 2), (1, 3), (4, 6), (5, 7)]
    trits = {}
    for key in keys:
        positive, negative = n + 1, n + 2
        n += 2
        trits[key] = positive, negative
        clauses.append([-positive, -negative])

    def deny(key, value):
        positive, negative = trits[key]
        return [-positive] if value == 1 else [-negative] if value == -1 else [positive, negative]

    truth_table = {row for row in product((-1, 0, 1), repeat=3) if allowed_sum(*row)}
    integer_witnesses = {(sign(a), sign(b), sign(a + b))
                         for a, b in product(range(-2, 3), repeat=2)}
    assert len(truth_table) == 13 and truth_table == integer_witnesses
    for i, j in keys[8:]:
        for left, right, total in product((-1, 0, 1), repeat=3):
            if not allowed_sum(left, right, total):
                clauses.append(deny((i,), left) + deny((j,), right) + deny((i, j), total))
    for i, j in ((0, 1), (2, 3), (4, 5), (6, 7)):
        clauses.append(list(trits[(i,)]) + list(trits[(j,)]))

    # Fix 0,2,5,7 by an affine map before taking the common collapsing
    # scale epsilon.  The collapsing edges' axial displacements are
    # o(epsilon).  Therefore these planar first-order surrogates give
    # exactly the constant and linear leading brackets; no assertion is
    # made about a vanishing coefficient's eventual bracket sign.
    eps = s.Symbol('eps')
    points = {
        0: (0, 0, 0), 1: (eps * ax, eps * ay, 0),
        4: (eps * (ax + bx), eps * (ay + by), 0), 5: (1, 0, 0),
        2: (0, 0, 1), 3: (eps * cx, eps * cy, 1),
        6: (eps * (cx + dx), eps * (cy + dy), 1), 7: (0, 1, 1),
    }
    base = {i: s.Matrix([s.sympify(v).subs(eps, 0) for v in point])
            for i, point in points.items()}
    constants = links = 0
    for idx, quad in enumerate(combinations(range(8), 4), 1):
        a, *rest = quad
        rank = s.Matrix.hstack(*(base[b] - base[a] for b in rest)).rank()
        if rank < 2:
            continue
        determinant = s.expand(s.Matrix(
            [[points[b][k] - points[a][k] for k in range(3)] for b in rest]).det())
        leading = s.Poly(determinant, eps).coeff_monomial(eps**(3 - rank))
        assert leading != 0
        if not leading.free_symbols:
            clauses.append([idx if leading > 0 else -idx])
            constants += 1
            continue
        coefficients, indices = [], []
        for powers, coefficient in s.Poly(leading, *xs).terms():
            assert sum(powers) == 1
            indices.append(powers.index(1))
            coefficients.append(coefficient)
        assert len(set(coefficients)) == 1
        key = tuple(sorted(indices))
        assert key in trits
        direction = 1 if coefficients[0] > 0 else -1
        positive, negative = trits[key]
        clauses.extend([[-positive, direction * idx], [-negative, -direction * idx]])
        links += 1
    assert constants == 9 and links == 42
    assert n == 433 and len(clauses) == 8543
    return n, clauses


def main():
    if not __debug__:
        raise RuntimeError('run this verifier with assertions enabled')
    if len(sys.argv) > 2:
        raise SystemExit(__doc__)
    n, clauses = generate()
    print(f'variables {n} clauses {len(clauses)}; 9 constant and 42 linear bracket links', flush=True)
    result = SAT(n, clauses).check()
    assert result == -1, f'expected UNSAT, received {result}'
    print('PASS necessary corner sign formula is UNSAT', flush=True)
    if len(sys.argv) == 2:
        path = Path(sys.argv[1])
        path.write_text(f'p cnf {n} {len(clauses)}\n' + ''.join(
            ' '.join(map(str, row)) + ' 0\n' for row in clauses))
        print(f'exported {path}', flush=True)
    print('Scope: nonparallel two-stick corner with four comparable collapsing edges; full ray 3 remains open')


if __name__ == '__main__':
    main()
