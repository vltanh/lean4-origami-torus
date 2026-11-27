#!/usr/bin/env python3
"""Finite sign certificates for the entire labelled nonparallel two-stick limit.

This strengthens verify_nonparallel_corner.py by covering every relative
collapse rate, including cancellation of the missing edge 26.  The analytic
bridge is in exhaustive_nonparallel_corner.md.  It is an asymptotic research
exclusion, not a fixed-modulus or Lean theorem.

Usage: python exhaustive_nonparallel_corner.py [OUTPUT_DIRECTORY]
The optional directory receives seven CNFs for independent exhaustive replay.
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
PATTERNS = {
    -1: [(1, 0, 0, 1, 0, -1, 0, -1)],
    0: [(1, 0, 0, 1, 0, -1, 0, -1), (1, 0, 0, 1, -1, 0, 1, 0)],
    1: [(1, 0, 0, 1, 0, -1, 0, -1),
        (1, 0, 0, 1, -1, 0, 0, -1),
        (1, 0, 0, 1, -1, -1, 0, -1)],
}


class Model:
    def __init__(self, quadratic=False):
        self.n, original = generate()
        self.trits = {key: (410 + 2*k, 411 + 2*k) for k, key in enumerate(KEYS)}
        assert self.n == 433
        removed = []
        for i, j in KEYS[8:]:
            removed += self.sum_clauses((i,), (j,), (i, j))
        assert len(removed) == 56
        counts = Counter(map(tuple, original))
        for row in removed:
            assert counts[tuple(row)] > 0
            counts[tuple(row)] -= 1
        self.clauses = [list(row) for row, count in counts.items() for _ in range(count)]
        assert len(self.clauses) == 8487
        if quadratic:
            for key in [''.join(p) for p in combinations('abcd', 2)] + ['aC', 'bC']:
                self.trits[key] = self.n + 1, self.n + 2
                self.n += 2
                self.clauses.append([-self.n + 1, -self.n])
            self.rank_two_axioms()

    def deny(self, key, value):
        positive, negative = self.trits[key]
        return [-positive] if value == 1 else [-negative] if value == -1 else [positive, negative]

    def fix(self, key, value):
        positive, negative = self.trits[key]
        self.clauses += [[positive if value == 1 else -positive],
                         [negative if value == -1 else -negative]]

    def sum_clauses(self, left, right, total):
        return [self.deny(left, a) + self.deny(right, b) + self.deny(total, c)
                for a, b, c in product((-1, 0, 1), repeat=3)
                if not allowed_sum(a, b, c)]

    def equal(self, left, right, sign=1):
        a = self.trits[left]
        b = self.trits[right][::sign]
        self.clauses += [[-x, y] for x, y in zip(a, b)]
        self.clauses += [[x, -y] for x, y in zip(a, b)]

    def scale_pair(self, pair, hierarchy):
        # -1: first edge dominates; 0: comparable; +1: second dominates.
        for coordinate in (0, 1):
            i, j = pair[0]*2 + coordinate, pair[1]*2 + coordinate
            if hierarchy == 0:
                self.clauses += self.sum_clauses((i,), (j,), (i, j))
            else:
                self.equal((i if hierarchy == -1 else j,), (i, j))

    def rank_two_axioms(self):
        # Six nonzero planar vectors E,F,a,b,c,d, with det(E,F)>0.
        # Eight coordinate trits already encode det(E,u)=uy and det(F,u)=-ux.
        def key(i, j):
            if (i, j) == (0, 1):
                return None, 1
            if i == 0:
                return (2*(j - 2) + 1,), 1
            if i == 1:
                return (2*(j - 2),), -1
            return 'abcd'[i - 2] + 'abcd'[j - 2], 1

        count = 0
        for quad in combinations(range(6), 4):
            pairs = [key(*pair) for pair in combinations(quad, 2)]
            keys = list(dict.fromkeys(k for k, _ in pairs if k is not None))
            for values in product((-1, 0, 1), repeat=len(keys)):
                env = dict(zip(keys, values))
                v = [sign*(1 if k is None else env[k]) for k, sign in pairs]
                terms = [v[0]*v[5], -v[1]*v[4], v[2]*v[3]]
                # Three summands of an exact zero sum cannot have one weak sign
                # with at least one strict term.  Zeros are retained throughout.
                if (all(x >= 0 for x in terms) or all(x <= 0 for x in terms)) and any(terms):
                    self.clauses.append(sum((self.deny(k, value)
                                             for k, value in zip(keys, values)), []))
                    count += 1
        assert count == 4800 and self.n == 449

    def quadratic_brackets(self):
        # A=a+b has the direction of a in every use of this method.
        forms = {
            '0123': ('ac', -1), '0124': ('ab', -1), '0126': ('aC', -1),
            '0134': ('ab', -1), '0136': ('ad', -1), '0146': ('ab', 1),
            '0147': ('ab', 1), '0234': ('ac', -1), '0236': ('cd', 1),
            '0246': ('aC', 1), '0346': ('ad', 1), '1234': ('bc', -1),
            '1236': ('cd', 1), '1246': ('bC', 1), '1346': ('bd', 1),
            '2346': ('cd', 1), '2356': ('cd', 1),
        }
        for quad, (key, direction) in forms.items():
            positive, negative = self.trits[key]
            idx = QUADS[quad]
            self.clauses += [[-positive, direction*idx], [-negative, -direction*idx]]

    def block_pattern(self, pattern):
        self.clauses.append(sum((self.deny((i,), value)
                                 for i, value in enumerate(pattern)), []))


def hierarchy_model(hierarchy):
    model = Model(quadratic=True)
    model.scale_pair((0, 1), -1)
    model.scale_pair((2, 3), hierarchy)
    for a in 'ab':
        if hierarchy == 0:
            model.clauses += model.sum_clauses(a + 'c', a + 'd', a + 'C')
        else:
            model.equal(a + ('c' if hierarchy == -1 else 'd'), a + 'C')
    model.quadratic_brackets()
    return model


def cancellation_model():
    model = Model(quadratic=True)
    model.scale_pair((0, 1), -1)
    for i, value in enumerate((1, 0, 0, 1, -1, 0, 1, 0)):
        model.fix((i,), value)
    # C=26 is normalized separately after the relative axial bound is proved.
    # Its scale need not match c,d or a.  No addition rule for c+d is imposed.
    model.equal('aC', (5, 7))
    model.equal('bC', (4, 6), sign=-1)
    model.clauses.append(list(model.trits[(4, 6)]) + list(model.trits[(5, 7)]))
    # The stress identity gives Cx+Cy>=0 in this separate directional limit.
    for x, y in product((-1, 0, 1), repeat=2):
        if x <= 0 and y <= 0 and min(x, y) < 0:
            model.clauses.append(model.deny((4, 6), x) + model.deny((5, 7), y))
    model.quadratic_brackets()
    # In the fixed affine frame [0125]+[0157]=axial(1)<0.
    model.clauses.append([-QUADS['0125'], -QUADS['0157']])
    return model


def exact_checks():
    """Verify cocycle symmetry and the algebraic identities used in the proof."""
    faces, _, edges, _, _, kx, ky = load_data()
    sigma = (4, 1, 6, 3, 0, 5, 2, 7)
    assert {tuple(sorted(sigma[v] for v in face)) for face in faces} == {
        tuple(sorted(face)) for face in faces}
    offsets = [s.Rational(0) if i % 2 == 0 else -s.Rational(1, 2) for i in range(8)]
    for i, j in edges:
        assert offsets[j] - offsets[i] == -kx[sigma[i], sigma[j]] - kx[i, j]
        assert ky[sigma[i], sigma[j]] == ky[i, j]

    x = [s.Integer(0)] + list(s.symbols('x1:8'))
    g = [s.Integer(0)] + list(s.symbols('g1:8'))
    t = s.Symbol('t')
    X = lambda i, j: x[j] - x[i] + kx[i, j]
    G = lambda i, j: g[j] - g[i]
    D = lambda i, j: X(i, j)**2 + ky[i, j]**2/t + 2*ky[i, j]*G(i, j) + t*G(i, j)**2
    rings = ((0, 1, 4, 5), (2, 3, 6, 7))
    ae, be = [list(zip(ring, ring[1:] + ring[:1])) for ring in rings]
    stress = [[s.expand(X(a, b)*X(c, d) + t*G(a, b)*G(c, d)
                         - (D(a, d) + D(b, c) - D(a, c) - D(b, d))/2)
               for c, d in be] for a, b in ae]
    alpha, beta, chi, delta = [-X(*e) for e in (ae[0], ae[1], be[0], be[1])]
    h = chi + delta
    total_gamma = G(*be[0]) + G(*be[1])
    c0 = -x[2] + s.Rational(1, 4) + 2*g[2]
    j = stress[0][1] + stress[1][1]
    assert s.expand(c0 - 2*(stress[0][2] + stress[0][3])) == 0
    assert s.expand(x[2] - h/2 + total_gamma + c0/2 + j) == 0
    rhs = (c0*h + total_gamma*(-1 + 2*h + 2*t*g[2])
           - 2*(1-h)*j + t*total_gamma**2)
    assert s.expand(D(0, 6) - D(0, 2) - rhs) == 0
    h1 = -c0 + (1 - 2*x[2])*alpha + G(0, 1) + 2*t*g[2]*G(0, 1)
    assert s.expand(D(0, 1) - D(1, 2) + D(0, 2) - h1) == 0
    h5 = x[5] + s.Rational(1, 4) + 2*x[5]*x[2] + g[5] - 2*g[2] + 2*t*g[5]*g[2]
    assert s.expand(D(0, 5) - D(2, 5) + D(0, 2) - h5) == 0
    mask = ((1, 0, 1, 1), (1, 0, 0, 0), (1, 1, 1, 0), (0, 0, 1, 0))
    assert s.expand(sum(mask[i][j]*stress[i][j] for i in range(4) for j in range(4)) - s.Rational(1, 2)) == 0

    # Check all 17 planar quadratic brackets before specializing A's hierarchy.
    ax, ay, bx, by, cx, cy, dx, dy = s.symbols('ax ay bx by cx cy dx dy')
    vectors = {'a': s.Matrix([ax, ay]), 'b': s.Matrix([bx, by]),
               'c': s.Matrix([cx, cy]), 'd': s.Matrix([dx, dy])}
    vectors['A'] = vectors['a'] + vectors['b']
    vectors['C'] = vectors['c'] + vectors['d']
    points = {0: (0, 0, 0), 1: (ax, ay, 0), 4: (ax+bx, ay+by, 0), 5: (1, 0, 0),
              2: (0, 0, 1), 3: (cx, cy, 1), 6: (cx+dx, cy+dy, 1), 7: (0, 1, 1)}
    forms = {'0123': ('a', 'c', -1), '0124': ('a', 'b', -1), '0126': ('a', 'C', -1),
             '0134': ('a', 'b', -1), '0136': ('a', 'd', -1), '0146': ('a', 'b', 1),
             '0147': ('a', 'b', 1), '0234': ('A', 'c', -1), '0236': ('c', 'd', 1),
             '0246': ('A', 'C', 1), '0346': ('A', 'd', 1), '1234': ('b', 'c', -1),
             '1236': ('c', 'd', 1), '1246': ('b', 'C', 1), '1346': ('b', 'd', 1),
             '2346': ('c', 'd', 1), '2356': ('c', 'd', 1)}
    for quad, (left, right, sign) in forms.items():
        a, *rest = map(int, quad)
        bracket = s.Matrix([[points[v][k] - points[a][k] for k in range(3)] for v in rest]).det()
        cross = s.det(s.Matrix.hstack(vectors[left], vectors[right]))
        assert s.expand(bracket - sign*cross) == 0
    print('PASS exact stress, missing-edge, mirror, and quadratic-bracket identities', flush=True)


def main():
    if not __debug__:
        raise RuntimeError('run with assertions enabled')
    if len(sys.argv) > 2:
        raise SystemExit(__doc__)
    output = Path(sys.argv[1]) if len(sys.argv) == 2 else None
    if output:
        output.mkdir(parents=True, exist_ok=True)
    exact_checks()
    cases = []
    for hierarchy in (-1, 0, 1):
        model = Model()
        model.scale_pair((0, 1), 0)
        model.scale_pair((2, 3), hierarchy)
        cases.append((f'comparable_a_{hierarchy:+d}', model))
    for hierarchy in (-1, 0, 1):
        model = hierarchy_model(hierarchy)
        # Check each claimed survivor exists; then block all six listed cells.
        for pattern in PATTERNS[hierarchy]:
            witness = hierarchy_model(hierarchy)
            for i, value in enumerate(pattern):
                witness.fix((i,), value)
            assert SAT(witness.n, witness.clauses).check() == 1
            model.block_pattern(pattern)
        cases.append((f'dominant_a_{hierarchy:+d}_blocked', model))
    cases.append(('nested_cancellation', cancellation_model()))
    for name, model in cases:
        assert SAT(model.n, model.clauses).check() == -1, name
        print(f'PASS {name}: UNSAT; {model.n} variables, {len(model.clauses)} clauses', flush=True)
        if output:
            (output / (name.replace('+', 'p').replace('-', 'm') + '.cnf')).write_text(
                f'p cnf {model.n} {len(model.clauses)}\n' + ''.join(
                    ' '.join(map(str, row)) + ' 0\n' for row in model.clauses))
    print('Scope: all relative rates of the labelled nonparallel two-stick limit; full ray 3 remains open')


if __name__ == '__main__':
    main()
