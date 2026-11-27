#!/usr/bin/env python3
"""Three exact sign certificates excluding the entire nonparallel two-stick limit.

Usage: python exhaustive_nonparallel_corner.py [OUTPUT_DIRECTORY]
No relative collapse rate is assumed.  The optional directory receives
three necessary CNFs for independent exhaustive replay.  The analytic
bridge is in exhaustive_nonparallel_corner.md.  This is an asymptotic
research exclusion, not a fixed-modulus or Lean theorem.
"""
from collections import Counter
from itertools import combinations, product
from pathlib import Path
import sys

import sympy as s

from verify_nonparallel_corner import generate, allowed_sum, SAT
from direct_metric import load_data

KEYS = [(i,) for i in range(8)] + [(0, 2), (1, 3), (4, 6), (5, 7)]
QUADS = {''.join(map(str, q)): i for i, q in enumerate(combinations(range(8), 4), 1)}
TRITS = {key: (410+2*k, 411+2*k) for k, key in enumerate(KEYS)}


def deny(key, value):
    positive, negative = TRITS[key]
    return [-positive] if value == 1 else [-negative] if value == -1 else [positive, negative]


def sum_clauses(i, j):
    return [deny((i,), a)+deny((j,), b)+deny((i, j), c)
            for a, b, c in product((-1, 0, 1), repeat=3) if not allowed_sum(a, b, c)]


def base_clauses():
    n, original = generate()
    assert n == 433
    # Remove all four common-scale addition rules.  Every B sum coordinate
    # remains free: this deliberately avoids any B-edge comparability premise.
    removed = sum((sum_clauses(i, j) for i, j in KEYS[8:]), [])
    assert len(removed) == 56
    counts = Counter(map(tuple, original))
    for row in removed:
        assert counts[tuple(row)] == 1
        counts[tuple(row)] -= 1
    clauses = [list(row) for row, count in counts.items() for _ in range(count)]
    assert len(clauses) == 8487
    return n, clauses


def cases():
    n, base = base_clauses()
    comparable = base + sum_clauses(0, 2) + sum_clauses(1, 3)
    dominant = list(base)
    for i, j in ((0, 2), (1, 3)):
        for a, b in zip(TRITS[(i,)], TRITS[(i, j)]):
            dominant += [[-a, b], [a, -b]]
    # The only allowed dominant-A directions are a=+E and b=+F.
    block = sum((deny((i,), value) for i, value in enumerate((1, 0, 0, 1))), [])
    result = [('comparable_a', n, comparable),
              ('dominant_a_direction_blocked', n, dominant+[block]),
              ('dominant_a_positive_cap', n, dominant+[[QUADS['0145']]])]
    assert [len(c) for _, _, c in result] == [8515, 8496, 8496]
    return result


def exact_checks():
    """Verify the marked symmetry and exact identities determining the cap sign."""
    faces, _, edges, _, _, kx, ky = load_data()
    sigma = (4, 1, 6, 3, 0, 5, 2, 7)
    assert {tuple(sorted(sigma[v] for v in face)) for face in faces} == {
        tuple(sorted(face)) for face in faces}
    offsets = [s.Rational(0) if i % 2 == 0 else -s.Rational(1, 2) for i in range(8)]
    for i, j in edges:
        assert offsets[j]-offsets[i] == -kx[sigma[i], sigma[j]]-kx[i, j]
        assert ky[sigma[i], sigma[j]] == ky[i, j]

    x = [s.Integer(0)]+list(s.symbols('x1:8'))
    g = [s.Integer(0)]+list(s.symbols('g1:8'))
    t, z = s.symbols('t z')
    X = lambda i, j: x[j]-x[i]+kx[i, j]
    G = lambda i, j: g[j]-g[i]
    D = lambda i, j: X(i, j)**2+ky[i, j]**2/t+2*ky[i, j]*G(i, j)+t*G(i, j)**2
    rings = ((0, 1, 4, 5), (2, 3, 6, 7))
    ae, be = [list(zip(ring, ring[1:]+ring[:1])) for ring in rings]
    stress = [[s.expand(X(a, b)*X(c, d)+t*G(a, b)*G(c, d)
                         -(D(a, d)+D(b, c)-D(a, c)-D(b, d))/2)
               for c, d in be] for a, b in ae]
    alpha = -X(0, 1)
    c0 = -x[2]+s.Rational(1, 4)+2*g[2]
    assert s.expand(c0-2*(stress[0][2]+stress[0][3])) == 0
    assert s.expand(G(0, 1)-alpha/2+stress[0][1]) == 0
    h1 = -c0+(1-2*x[2])*alpha+G(0, 1)+2*t*g[2]*G(0, 1)
    assert s.expand(D(0, 1)-D(1, 2)+D(0, 2)-h1) == 0
    h5 = x[5]+s.Rational(1, 4)+2*x[5]*x[2]+g[5]-2*g[2]+2*t*g[5]*g[2]
    assert s.expand(D(0, 5)-D(2, 5)+D(0, 2)-h5) == 0

    xlim = [0, 0, 0, 0, s.Rational(1, 2), 0, s.Rational(1, 2), 0]
    glim = [0, 0, -s.Rational(1, 8), -s.Rational(1, 8), 0, -z,
            -s.Rational(1, 8), s.Rational(1, 8)]
    limit = dict(zip(x[1:]+g[1:], xlim[1:]+glim[1:]))
    target = s.zeros(4)
    target[2, 2] = target[3, 3] = s.Rational(1, 4)-z
    target[2, 3] = target[3, 2] = s.Rational(1, 4)+z
    for i, j in product(range(4), repeat=2):
        assert s.expand(stress[i][j].subs(limit)-target[i, j]) == 0
    assert s.expand(h5.subs(limit).subs(t, 0)-(s.Rational(1, 2)-z)) == 0
    ax, ay, az, bx, by, bz = s.symbols('ax ay az bx by bz')
    assert s.expand(s.Matrix([[ax, ay, az], [bx, by, bz], [1, 0, 0]]).det()
                    -(ay*bz-az*by)) == 0
    assert s.expand(-2*(4*z-3)-(6-8*z)) == 0
    print('PASS exact marked symmetry, stress reconstruction, axial and cap-determinant identities', flush=True)


def main():
    if not __debug__:
        raise RuntimeError('run with assertions enabled')
    if len(sys.argv) > 2:
        raise SystemExit(__doc__)
    output = Path(sys.argv[1]) if len(sys.argv) == 2 else None
    if output:
        output.mkdir(parents=True, exist_ok=True)
    exact_checks()
    for name, n, clauses in cases():
        assert SAT(n, clauses).check() == -1, name
        print(f'PASS {name}: UNSAT; {n} variables, {len(clauses)} clauses', flush=True)
        if output:
            (output/(name+'.cnf')).write_text(f'p cnf {n} {len(clauses)}\n'+''.join(
                ' '.join(map(str, row))+' 0\n' for row in clauses))
    print('Scope: all relative rates of the labelled nonparallel two-stick limit; full ray 3 remains open')


if __name__ == '__main__':
    main()
