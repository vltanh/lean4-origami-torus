#!/usr/bin/env python3
"""Exact diagnostic for the ray_2 core {1,2,3,4,5,6}.

Requires SymPy.  All identities are checked in a quotient of Q[u,v], and all
strict signs use rational intervals.  This is deliberately NOT an embedding:
the final check certifies edge 15 crossing the relative interior of face 264.
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
p = {
    4: S.Matrix([0, 0]),
    5: S.Matrix([-S.Rational(1, 4), 0]),
    1: S.Matrix([S.Rational(1, 4) + 1/(128*W), 0]),
    6: S.Matrix([S.Rational(9, 32), Y/4]),
    2: S.Matrix([0, Y/2 + u/Y]),
    3: S.Matrix([S.Rational(3, 32), -Y/2 + v/Y]),
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


roots = {u: root_interval(polys[u], True), v: root_interval(polys[v], False)}


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

# In the basis (r5,r1,r6), lambda6 is [451i]/[4516].
def M(i, j):
    return G[0, 0]*gram(i, j)-gram(5, i)*gram(5, j)


Delta = S.expand(M(1, 1)*M(6, 6)-M(1, 6)**2)
assert Delta > 0
for i in (2, 3):
    N = M(1, 1)*M(6, i)-M(1, 6)*M(1, i)
    assert reduce(N-Delta*r[i][2]) == 0
positive(-r[2][2])
positive(r[3][2])

# Exact Radon certificate: lambda1*r1+lambda5*r5 equals
# r2-lambda4*r4-lambda6*r6; every displayed weight is positive.
lambda5, lambda1, lambda6 = r[2]
lambda4 = 1-lambda5-lambda1-lambda6
for weight in (lambda1, lambda5, -lambda4, -lambda6):
    positive(weight)
assert all(reduce(z) == 0 for z in
           lambda1*r[1]+lambda5*r[5]-(r[2]-lambda4*r[4]-lambda6*r[6]))
assert reduce(lambda1+lambda5-(1-lambda4-lambda6)) == 0

print("PASS: positive anchor Gram; 14 exact edge equations and strict nearest lifts")
print("PASS: six coherently oriented intrinsic faces; 15 nonzero affine brackets")
print("PASS: all nine tested nonedge23 contraction bounds are strict")
print("PASS: [4512]*[4513] < 0")
print("PASS: exact proper crossing edge15 / face264 -- this is NOT an embedding")
