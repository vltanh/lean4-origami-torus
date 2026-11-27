#!/usr/bin/env python3
"""Exact embedded ray-2 six-vertex core in tilted C collapse.

This is not a full torus: vertices 0 and 7 are absent. It certifies the
14 core edge metrics, shortest lifts, coherent intrinsic faces, strict
neighbor support and all intersections among core simplices.
Requires SymPy. All identities/signs use rational algebra and intervals.
"""
from fractions import Fraction as Q
from itertools import combinations, product
from math import isqrt
from pathlib import Path
import sys
import sympy as S

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "type4_focus"))
from type4_gap_enum import E as ARCHIVE_E, F as ARCHIVE_F, SH as ARCHIVE_SH

W, Y = S.Integer(10)**12, S.Integer(10)**6
u, v = S.symbols("u v")
B = (5, 1, 6)
small = S.Rational(1, 4)/W
s = S.Rational(1, 2)-small
p = {
    4: S.Matrix([0, 0]),
    5: S.Matrix([-s, 5*s/(64*Y)]),
    1: S.Matrix([S.Rational(3, 16), -1/(16*Y)]),
    6: S.Matrix([S.Rational(29, 64)+3/(128*W), Y/2-21/(64*Y)]),
    2: S.Matrix([-S.Rational(7, 256)+5/(64*W), Y/2+u/Y]),
    3: S.Matrix([S.Rational(9, 128)+3/(256*W), -Y/2+v/Y]),
}
K = {
    (1, 5): (1, 0), (5, 6): (-1, 0), (1, 6): (0, 0),
    (2, 5): (0, 1), (1, 2): (1, -1), (2, 6): (0, 0),
    (3, 5): (1, -1), (1, 3): (0, 0), (3, 6): (0, -1),
}
K.update({(j, i): (-m, -n) for (i, j), (m, n) in list(K.items())})


def shift(i, j):
    m, n = K.get((i, j), (0, 0))
    return S.Matrix([m + S.Rational(n, 2), Y*n])


def gram(i, j):
    k = shift(i, j)
    return p[i].dot(p[j]) - (p[j]-p[i]).dot(k) - k.dot(k)/2


G = S.Matrix([[gram(i, j) for j in B] for i in B])
assert all(G[:j, :j].det() > 0 for j in (1, 2, 3))
r = {4: S.zeros(3, 1), 5: S.Matrix([1, 0, 0]),
     1: S.Matrix([0, 1, 0]), 6: S.Matrix([0, 0, 1])}
polys = {}
for i, variable in ((2, u), (3, v)):
    r[i] = (G.inv() * S.Matrix([gram(j, i) for j in B])).applyfunc(S.expand)
    equation = S.Poly(S.expand((r[i].T*G*r[i])[0] - p[i].dot(p[i])), variable)
    _, poly = equation.clear_denoms()
    _, poly = poly.primitive()
    if poly.LC() < 0:
        poly = -poly
    assert poly.degree() == 2
    polys[variable] = poly


def reduce(expression):
    return S.reduced(S.expand(expression),
                     [polys[u].as_expr(), polys[v].as_expr()], u, v)[1]


class Interval:
    def __init__(self, lo, hi=None):
        self.lo = Q(lo)
        self.hi = self.lo if hi is None else Q(hi)
        assert self.lo <= self.hi

    def __add__(self, other):
        other = other if isinstance(other, Interval) else Interval(other)
        return Interval(self.lo + other.lo, self.hi + other.hi)

    __radd__ = __add__

    def __mul__(self, other):
        other = other if isinstance(other, Interval) else Interval(other)
        values = [a*b for a in (self.lo, self.hi) for b in (other.lo, other.hi)]
        return Interval(min(values), max(values))

    __rmul__ = __mul__

    def __pow__(self, exponent):
        result = Interval(1)
        for _ in range(exponent):
            result = result*self
        return result


def root_interval(poly, upper):
    a, b, c = map(int, poly.all_coeffs())
    assert a > 0
    disc = b*b - 4*a*c
    assert disc > 0
    scale = 1 << 400
    floor = isqrt(disc*scale*scale)
    assert floor*floor <= disc*scale*scale < (floor+1)*(floor+1)
    lower, higher = Q(floor, scale), Q(floor+1, scale)
    if upper:
        return Interval((-b+lower)/(2*a), (-b+higher)/(2*a))
    return Interval((-b-higher)/(2*a), (-b-lower)/(2*a))


roots = {u: root_interval(polys[u], False), v: root_interval(polys[v], False)}


def interval(expression):
    result = Interval(0)
    for (i, j), coefficient in S.Poly(reduce(expression), u, v).terms():
        result += Q(int(S.numer(coefficient)), int(S.denom(coefficient))) * roots[u]**i * roots[v]**j
    return result


def positive(expression):
    bounds = interval(expression)
    assert bounds.lo > 0, (expression, bounds.lo, bounds.hi)


vertices = tuple(sorted(p))
edges = [e for e in combinations(vertices, 2) if e != (2, 3)]
assert edges == [e for e in ARCHIVE_E if set(e) <= set(vertices)]
for i, j in edges:
    assert K.get((i, j), (0, 0)) == ARCHIVE_SH[1].get(f"{i}{j}", (0, 0))
for i, j in edges:
    spatial = r[j]-r[i]
    intrinsic = p[j]-p[i]+shift(i, j)
    assert reduce((spatial.T*G*spatial)[0]-intrinsic.dot(intrinsic)) == 0
    x, y = intrinsic
    for value, bound in ((x, S.Rational(1, 2)),
                         (y+x/(2*Y), Y/2+1/(8*Y)),
                         (y-x/(2*Y), Y/2+1/(8*Y))):
        positive(bound-value)
        positive(bound+value)

faces = ((1, 5, 2), (1, 3, 4), (1, 4, 6),
         (1, 6, 5), (2, 6, 4), (3, 5, 6))
assert list(faces) == [f for f in ARCHIVE_F if set(f) <= set(vertices)]
for i, j, k in faces:
    a, b = p[j]-p[i]+shift(i, j), p[k]-p[i]+shift(i, k)
    assert shift(i, j)+shift(j, k)+shift(k, i) == S.zeros(2, 1)
    positive(-(a[0]*b[1]-a[1]*b[0]))

for tetrahedron in combinations(vertices, 4):
    a, *others = tetrahedron
    determinant = S.Matrix.hstack(*(r[j]-r[a] for j in others)).det()
    bounds = interval(determinant)
    assert bounds.lo > 0 or bounds.hi < 0

delta = r[3]-r[2]
d23 = (delta.T*G*delta)[0]
positive(d23)
for m, n in product(range(-1, 2), repeat=2):
    intrinsic = p[3]-p[2]+S.Matrix([m+S.Rational(n, 2), Y*n])
    positive(intrinsic.dot(intrinsic)-d23)

# All 15 affine brackets are strict, so every minimal affine circuit has
# five points. Their sign parts decide every possible disjoint intersection.
determinants = {}
for tetrahedron in combinations(vertices, 4):
    a, *others = tetrahedron
    determinant = S.Matrix.hstack(*(r[j]-r[a] for j in others)).det()
    bounds = interval(determinant)
    assert bounds.lo > 0 or bounds.hi < 0
    determinants[tetrahedron] = 1 if bounds.lo > 0 else -1

simplices = {tuple(sorted(f)) for f in faces}
simplices.update(edges)
simplices.update((i,) for i in vertices)
for five in combinations(vertices, 5):
    cofactor_signs = [(-1)**i*determinants[five[:i]+five[i+1:]] for i in range(5)]
    plus = tuple(k for k,t in zip(five, cofactor_signs) if t > 0)
    minus = tuple(k for k,t in zip(five, cofactor_signs) if t < 0)
    assert plus and minus
    assert not (plus in simplices and minus in simplices), (five, plus, minus)
    # A singleton Radon side is forbidden when the other vertices all
    # belong to its graph-neighborhood (strict-support premise).
    for singleton, rest in ((plus,minus),(minus,plus)):
        if len(singleton) == 1:
            i = singleton[0]
            assert not all(tuple(sorted((i,j))) in edges for j in rest), (five, i)

for i in (2, 3):
    weights = {4:1-sum(r[i]), 5:r[i][0], 1:r[i][1], 6:r[i][2]}
    for j,t in weights.items():
        positive(-t if j == 1 else t)

print("PASS: positive anchor Gram; 14 exact core edge equations and strict nearest lifts")
print("PASS: six coherent intrinsic faces; all 15 four-point brackets are nonzero")
print("PASS: strict chord23 contraction against all nine neighboring translates")
print("PASS: all six five-point Radon partitions avoid core simplex intersections")
print("PASS: strict neighbor support; both root affine-negative masks are {1}")
print("An embedded six-vertex core is certified; vertices 0/7 and the full torus remain absent.")
