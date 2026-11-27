#!/usr/bin/env python3
"""Exclude both metric completions of vertex 0 for core_attack_witness.

This is an exact statement about that fixed core, not all ray2_2 cores.
Four polarized equations give an invertible linear system; the remaining
radial equation is quadratic. Rational intervals certify that each root
forces edge 12 through the relative interior of actual face 045.
"""
from fractions import Fraction as Q
from itertools import combinations
from math import isqrt
import sympy as S
import core_attack_witness as C


class Interval:
    def __init__(self, lo, hi=None):
        self.lo = Q(lo)
        self.hi = self.lo if hi is None else Q(hi)
        assert self.lo <= self.hi

    def __add__(self, other):
        other = other if isinstance(other, Interval) else Interval(other)
        return Interval(self.lo+other.lo, self.hi+other.hi)

    __radd__ = __add__

    def __neg__(self):
        return Interval(-self.hi, -self.lo)

    def __sub__(self, other):
        return self + (-other if isinstance(other, Interval) else -Q(other))

    def __mul__(self, other):
        other = other if isinstance(other, Interval) else Interval(other)
        values = [x*y for x in (self.lo,self.hi) for y in (other.lo,other.hi)]
        return Interval(min(values),max(values))

    __rmul__ = __mul__

    def inverse(self):
        assert self.lo > 0 or self.hi < 0
        return Interval(1/self.hi, 1/self.lo)

    def __truediv__(self, other):
        other = other if isinstance(other, Interval) else Interval(other)
        return self*other.inverse()

    def sqrt(self):
        assert self.lo > 0
        scale = 1 << 400
        def floor(q):
            n = isqrt(q.numerator*scale*scale//q.denominator)
            assert Q(n*n,scale*scale) <= q < Q((n+1)**2,scale*scale)
            return n
        return Interval(Q(floor(self.lo),scale), Q(floor(self.hi)+1,scale))

    def sign(self):
        assert self.lo > 0 or self.hi < 0
        return 1 if self.lo > 0 else -1


def interval(expression):
    z = C.interval(expression)
    return Interval(z.lo,z.hi)


def reduced(expression):
    return C.reduce(S.expand(expression))


# Work in intrinsic (x,H/y) coordinates. Vertex 0 is adjacent to 1,2,3,4,5.
# For j in (1,2,3,5), put s_j=p_j+shift(0,j). Polarizing against vertex 4
# yields (G r_j).z - s_j.y*H/y = s_j.x*x + (|p_j|^2-|s_j|^2)/2.
J = (1,2,3,5)
assert set(J) | {4} == {j for i, j in C.ARCHIVE_E if i == 0}
assert (1, 2) in C.ARCHIVE_E
assert (0, 4, 5) in {tuple(sorted(f)) for f in C.ARCHIVE_F}
rows, rhs, direction = [], [], []
for j in J:
    m,n = C.ARCHIVE_SH[1].get(f"0{j}",(0,0))
    shifted = C.p[j] + S.Matrix([m+S.Rational(n,2), C.Y*n])
    rows.append([*(C.G*C.r[j]), -shifted[1]/C.Y])
    rhs.append(reduced((C.p[j].dot(C.p[j])-shifted.dot(shifted))/2))
    direction.append(shifted[0])
M = S.Matrix(rows)
D = reduced(M.det())
interval(D).sign()


def cramer(values):
    answer = []
    for column in range(4):
        changed = M.copy()
        changed[:,column] = S.Matrix(values)
        answer.append(reduced(changed.det()))
    return S.Matrix(answer)


P, T = cramer(rhs), cramer(direction)
# These symbolic identities prove the linear parametrization captures every
# leaf completion, since D is strictly nonzero at the selected core roots.
assert all(reduced(z)==0 for z in M*P-D*S.Matrix(rhs))
assert all(reduced(z)==0 for z in M*T-D*S.Matrix(direction))
Pz,Tz=P[:3,0],T[:3,0]
a=reduced((Tz.T*C.G*Tz)[0]-T[3]**2/C.W-D**2)
b=reduced(2*((Pz.T*C.G*Tz)[0]-P[3]*T[3]/C.W))
c=reduced((Pz.T*C.G*Pz)[0]-P[3]**2/C.W)
interval(a).sign()
discriminant=reduced(b*b-4*a*c)
disc_bounds=interval(discriminant)
assert disc_bounds.lo>0
x_intervals=[(-interval(b)+sign*disc_bounds.sqrt())/(2*interval(a)) for sign in (-1,1)]

# The leaf's homogeneous coordinate row is [D,Pz+x*Tz]. This row is D
# times its actual affine row. For the omitted-leaf cofactor multiply by D
# as well, so all five cofactor numerators share the same common factor D.
x=S.Symbol('x')
five=(0,1,2,4,5)
homogeneous={i:S.Matrix([[1,*C.r[i]]]) for i in five if i!=0}
homogeneous[0]=S.Matrix([[D,*(Pz+x*Tz)]])
cofactors=[]
for position in range(5):
    subset=five[:position]+five[position+1:]
    determinant=S.Matrix.vstack(*(homogeneous[i] for i in subset)).det()
    if position==0:
        determinant*=D
    polynomial=S.Poly(S.expand((-1)**position*determinant),x)
    assert polynomial.degree()<=1
    cofactors.append(tuple(reduced(polynomial.nth(k)) for k in range(2)))

for root_number,leaf_x in enumerate(x_intervals):
    signs=[(interval(constant)+interval(linear)*leaf_x).sign()
           for constant,linear in cofactors]
    plus={i for i,sign in zip(five,signs) if sign>0}
    minus=set(five)-plus
    assert {frozenset(plus),frozenset(minus)} == {frozenset((1,2)),frozenset((0,4,5))}
    print(f"PASS leaf0 quadratic root {root_number+1}: exact proper crossing edge12 / face045")

print("PASS: every metric completion of vertex 0 for this fixed core is excluded")
