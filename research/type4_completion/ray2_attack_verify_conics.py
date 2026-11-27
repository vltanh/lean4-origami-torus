#!/usr/bin/env python3
"""Exact formula checks for the uniform ray-2 core quadratics."""

from itertools import combinations
from pathlib import Path
import sys

import sympy as S

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "type4_focus"))
from type4_gap_enum import E as ARCHIVE_E, SH as ARCHIVE_SH


def main():
    s, T, a, R, b, Z, c, d, u, v, W = S.symbols(
        "s T a R b Z c d u v W", real=True
    )
    half, eighth = S.Rational(1, 2), S.Rational(1, 8)
    # Store scaled vertical coordinates H=y*Y, so dot products use H_i H_j/W.
    p = {
        4: (S.Integer(0), S.Integer(0)),
        5: (-s, T), 1: (a, R), 6: (b, Z),
        2: (c, W/2+u), 3: (d, -W/2+v),
    }
    shifts = {(1, 5): (1, 0), (1, 2): (1, -1),
              (2, 5): (0, 1), (3, 5): (1, -1),
              (3, 6): (0, -1), (5, 6): (-1, 0)}
    vertices = tuple(sorted(p))
    edges = [e for e in combinations(vertices, 2) if e != (2, 3)]
    assert edges == [e for e in ARCHIVE_E if set(e) <= set(vertices)]
    for i, j in edges:
        assert shifts.get((i, j), (0, 0)) == ARCHIVE_SH[1].get(f"{i}{j}", (0, 0))

    def norm(P):
        return P[0]**2 + P[1]**2/W

    def distance(i, j):
        if i > j:
            return distance(j, i)
        m, n = shifts.get((i, j), (0, 0))
        return norm((p[j][0]-p[i][0]+m+n*half,
                     p[j][1]-p[i][1]+W*n))

    def gram(i, j):
        return S.expand((norm(p[i])+norm(p[j])-distance(i, j))/2)

    basis = (5, 1, 6)
    G = S.Matrix([
        [s*s+T*T/W, -s*a+T*R/W+a+s-half, -s*b+T*Z/W+b+s-half],
        [-s*a+T*R/W+a+s-half, a*a+R*R/W, a*b+R*Z/W],
        [-s*b+T*Z/W+b+s-half, a*b+R*Z/W, b*b+Z*Z/W],
    ])
    for i in range(3):
        for j in range(i, 3):
            assert S.expand(G[i, j]-gram(basis[i], basis[j])) == 0

    V2 = S.Matrix([1+T/W, 1+R/W, Z/W])
    H2 = S.Matrix([(s+c)/2-s*c-T/2-eighth,
                    a*c+(a-c)/2-R/2-eighth, b*c+Z/2])
    V3 = S.Matrix([-1+T/W, R/W, -1+Z/W])
    H3 = S.Matrix([(s+d)/2-s*d+T/2-eighth,
                    a*d-R/2, b*d+(b-d)/2+Z/2-eighth])
    for root, phase, V, H in [(2, u, V2, H2), (3, v, V3, H3)]:
        for j, anchor in enumerate((5, 1, 6)):
            assert S.expand(gram(anchor, root)-(H+phase*V)[j]) == 0
        expected = ((c*c+W/4+u+u*u/W) if root == 2
                    else (d*d+W/4-v+v*v/W))
        assert S.expand(norm(p[root])-expected) == 0
    L = s*s+T*T/W
    for sign in (-1, 1):
        assert S.factor((sign+T/W)**2/L-1/W
                        -(W+2*sign*T-s*s)/(W*s*s+T*T)) == 0
        lhs = W+2*sign*T-s*s-S.Rational(4, 5)*(W*s*s+T*T)
        rhs = ((W-1)*(1-S.Rational(4, 5)*s*s)
               +(1-2*s)*(1+s)+(s+2*sign*T)
               +S.Rational(4, 5)*(s*s/4-T*T))
        assert S.expand(lhs-rhs) == 0
    print("PASS archived core edges and shifts; all six displayed anchor Gram entries")
    print("PASS six prescribed dot products and both radial norm formulas")
    print("PASS both Cauchy bounds and uniform positive decompositions")
    print("SCOPE: exact formula checks; four-branch core reduction, no row exclusion")


if __name__ == "__main__":
    main()
