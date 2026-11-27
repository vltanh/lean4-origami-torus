#!/usr/bin/env python3
"""Exact cap identities, boundary kernels, and F1 cocycle substitutions.

This verifies necessary identities; it is not an infeasibility certificate.
"""
from pathlib import Path
import sys

import sympy as sp

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent / "type5_focus" / "fixed_elongated"))
import generate as fixed


def zero(expr):
    assert sp.expand(expr) == 0, sp.factor(expr)


h1, h2, b1, b2 = sp.symbols("h1 h2 b1 b2")
h3 = 1 - h1 - h2
s = h1 + h2 - sp.Rational(1, 2)
c = h1 * h2 - s
T = sp.Matrix([[h1**2, -c], [-c, h2**2]])
b = sp.Matrix([b1, b2])
B = T + b * b.T
D = (1 - 2*h1) * (1 - 2*h2) * (1 - 2*h3) / 4

zero(T.det() - D)
zero(B[0, 0] - (h1**2 + b1**2))
zero(B[1, 1] - (h2**2 + b2**2))
zero(B[0, 0] + B[1, 1] - 2*B[0, 1]
     - (h3**2 + (b2-b1)**2))
zero(B.det() - D - (b.T * T.adjugate() * b)[0])
zero(h2**2 * (B.det() - D) - (h2**2*b1 + c*b2)**2 - D*b2**2)
zero(h1**2 * (B.det() - D) - (h1**2*b2 + c*b1)**2 - D*b1**2)
print("PASS: cap Gram decomposition, product determinant, two division-free SOS identities")

w = sp.symbols("w")
zero((w*B).det() - w**2*(D+(b.T*T.adjugate()*b)[0]))
print("PASS: scaled determinant identity for an arbitrary nonzero lattice period")

# These are polynomial identities on whole faces, including face intersections.
zero((B.det() - (h2*b1-h1*b2)**2).subs(h1, sp.Rational(1, 2)))
zero((B.det() - (h2*b1-h1*b2)**2).subs(h2, sp.Rational(1, 2)))
zero((B.det() - (h2*b1+h1*b2)**2).subs(h2, sp.Rational(1, 2)-h1))
print("PASS: all three cap-collapse boundary kernels, including their intersections")

# Angular identity after multiplication by the positive factor 2*|u|*|v|.
hx, hy, vx, vy = sp.symbols("hx hy vx vy")
u = sp.Matrix([hx, vx])
v = sp.Matrix([hy, vy])
w = sp.Matrix([1-hx-hy, -vx-vy])
zero(w.dot(w) - u.dot(u) - v.dot(v) - 2*u.dot(v)
     - (2*w[0]-1))
print("PASS: exact cosine difference for cap exterior and intrinsic turns")

F1 = {"00020220", "00020221", "00020222", "00120220", "00120221"}
cells = {"".join(map(str, a)): (a, q) for a, q in fixed.rep}
assert F1 <= cells.keys()
for label in F1:
    a, _ = cells[label]
    assert all(a[i] == 0 for i in (0, 1, 4))
    assert all(a[i] == 2 for i in (3, 5, 6))

x = sp.symbols("x0:8")
v = sp.symbols("v0:8")
y = sp.symbols("y")


def displacement(i, j):
    m, n = fixed.K[i, j]
    return (x[j]-x[i]+sp.Rational(m)+sp.Rational(n, 2),
            v[j]-v[i]+n*y)


for cycle in ((1, 0, 4), (5, 6, 3)):
    edges = list(zip(cycle, cycle[1:] + cycle[:1]))
    assert sum(fixed.K[e][0] for e in edges) == 1
    assert sum(fixed.K[e][1] for e in edges) == 0
    zero(sum(displacement(*e)[0] for e in edges)-1)
    zero(sum(displacement(*e)[1] for e in edges))

gauge = {x[1]: 0, v[1]: 0}
substitutions = [
    ((1, 0, 4), (x[0], -x[4], 1+x[4]-x[0], v[0], v[4])),
    ((5, 6, 3), (x[6]-x[5]+sp.Rational(1, 2),
                  x[5]-x[3]+sp.Rational(1, 2), x[3]-x[6],
                  v[6]-v[5]+y, v[3]-v[5]+y)),
]
for (base, first, second), (a, d, e, p, q) in substitutions:
    first_edge = tuple(z.subs(gauge) for z in displacement(base, first))
    second_edge = tuple(z.subs(gauge) for z in displacement(base, second))
    opposite = tuple(z.subs(gauge) for z in displacement(first, second))
    zero(first_edge[0]-a)
    zero(first_edge[1]-p)
    zero(second_edge[0]+d)
    zero(second_edge[1]-q)
    zero(opposite[0]-e)
    zero(opposite[1]-(q-p))

print("PASS: archived sharp cocycle substitutions for 014 and 356 in all five F1 cells")
print("All checks passed. No localized cell is excluded by these identities alone.")
