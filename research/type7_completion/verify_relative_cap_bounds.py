#!/usr/bin/env python3
"""Exact identities/constants for relative_cap_bounds.md; no solver search."""
from fractions import Fraction as F
import json
from pathlib import Path

import sympy as s

ROOT = Path(__file__).resolve().parents[1]
case = next(c for c in json.loads((ROOT / 'linking_checkpoint/cases.json').read_text())
            if c['file'] == 't7_ray_3.smt2')
K = {tuple(z['edge']): tuple(z['shift']) for z in case['edge_shifts']}
K.update({(j, i): (-m, -n) for (i, j), (m, n) in list(K.items())})
faces = [tuple(map(int, f)) for f in json.loads(
    (ROOT / 'linking_checkpoint/lutz_faces.json').read_text())['7'].split()]
A, B = (0, 1, 4, 5), (2, 3, 6, 7)


def ring(vertices):
    return list(zip(vertices, vertices[1:] + vertices[:1]))


EA, EB = ring(A), ring(B)
x, v, w = s.symbols('x0:8'), s.symbols('v0:8'), s.Symbol('w')


def intrinsic(a, b):
    m, n = K[a, b]
    return x[b] - x[a] + m + s.Rational(n, 2), v[b] - v[a] + n


def dot(a, b):
    return a[0] * b[0] + w * a[1] * b[1]


def dist2(a, b):
    u = intrinsic(a, b)
    return dot(u, u)


def stress(e, f):
    a, b = e
    c, d = f
    spatial_dot = (dist2(a, d) + dist2(b, c) - dist2(a, c) - dist2(b, d)) / 2
    return dot(intrinsic(*e), intrinsic(*f)) - spatial_dot


# Row/column, which of its two edges supplies gamma, sign of gamma.
table = [(0, 1, 0, -1), (1, 0, 0, 1), (2, 3, 0, -1), (3, 2, 0, 1),
         (3, 0, 1, -1), (2, 1, 1, 1), (1, 2, 1, -1), (0, 3, 1, 1)]
seen = []
for i, j, which, sign in table:
    e, f = EA[i], EB[j]
    chosen = (e, f)[which]
    X, V = intrinsic(*chosen)
    assert s.expand(stress(e, f) + X / 2 - sign * w * V) == 0
    seen.append(chosen)
assert sorted(seen) == sorted(EA + EB)
for R in (EA, EB):
    assert tuple(sum(K[e][k] for e in R) for k in (0, 1)) == (-1, 0)
    assert s.expand(sum(intrinsic(*e)[0] for e in R)) == -1
    assert s.expand(sum(intrinsic(*e)[1] for e in R)) == 0
for e in EA:
    assert s.expand(sum(stress(e, f) for f in EB) + intrinsic(*e)[0]) == 0
for f in EB:
    assert s.expand(sum(stress(e, f) for e in EA) + intrinsic(*f)[0]) == 0
areas = []
for a, b, c in faces:
    X, V = intrinsic(a, b)
    U, Z = intrinsic(a, c)
    areas.append(X * Z - U * V)
assert s.expand(sum(areas)) == -2
print('PASS eight exact short-edge stress identities, row/column sums, windings and area sum')

# Canonical phase baseline: both long alternating rings have V=-1/2.
ybase = [F(0)] * 8
for R in ((0, 2, 4, 6), (1, 3, 5, 7)):
    for a, b in zip(R, R[1:]):
        ybase[b] = ybase[a] - F(1, 2) - K[a, b][1]
chosen_thirds = (6, 2, 2, 6, 0, 4, 4, 0)
cyclic_faces = {f[i:] + f[:i] for f in faces for i in range(3)}
for (a, b), c in zip(EA + EB, chosen_thirds):
    assert (a, b, c) in cyclic_faces
    assert ybase[b] - ybase[a] + K[a, b][1] == 0
    assert ybase[c] - ybase[a] + K[a, c][1] == F(1, 2)
print('PASS eight oriented faces and canonical positive cross-height signs')

wmin = F(64)
assert F(1, 4) + F(49, 16) / wmin < F(11, 20) ** 2
assert F(8, 5) / (1 - F(11, 80)) == F(128, 69) < 2
assert F(1, 2) - F(7, 4) / wmin > 1 / wmin
assert 1 + 4 / wmin == F(17, 16) < F(33, 32) ** 2
assert F(1, 2) - F(7, 4) / wmin > F(15, 32)
assert F(7, 2) + F(5, 2) / wmin == F(453, 128)
assert F(453, 128) + F(1089, 1024) == F(4713, 1024)
assert F(4713, 1024) / (2 * F(15, 32)) == F(4713, 960) < 5
assert 1 - 25 / wmin == F(39, 64) > F(3, 4) ** 2
assert F(5) / F(15, 32) == F(32, 3) < 11
assert F(11, 2) / wmin < F(1, 2)
assert 33 * F(33, 32) ** 2 == F(35937, 1024) < 36
assert F(36) / F(3, 4) ** 2 == 64

# Normalized stress identity and sharper maximum-slope argument.
q, r, k = s.symbols('q r k')
norm_difference = 2 + (q*q+r*r)/w - 2*k
assert s.expand((norm_difference-(q-r)**2/w)/2-(1+q*r/w-k)) == 0
Fq = lambda z: z-s.Rational(1, 2)-2*z*z/w
assert s.factor(Fq(s.Rational(1, 2)+1/w)-(w*w-4*w-4)/(2*w**3)) == 0
assert s.expand(Fq(r)-Fq(q)-(r-q)*(1-2*(q+r)/w)) == 0
assert 1 - 8/wmin > 0
assert wmin*wmin-4*wmin-4 > 0

# Exact determinant expansion underlying the relative error estimate.
px, py, qx, qy, cx, cy, aa, bb, cc = s.symbols('px py qx qy cx cy aa bb cc')
matrix = s.Matrix([[px, py, aa], [qx, qy, bb], [cx, cy, cc]])
assert s.expand(matrix.det() - (cc * (px*qy-py*qx)
                                 + aa * (qx*cy-qy*cx)
                                 - bb * (px*cy-py*cx))) == 0
print('PASS all rational bounds and relative determinant expansion')
print('PASS relative cap estimates only; ray3_phase0 remains open')
