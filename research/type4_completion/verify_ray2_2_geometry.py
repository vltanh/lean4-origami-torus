#!/usr/bin/env python3
"""Exact identities and local Radon test for the active ray2_2 case.

This is not an infeasibility checker for the full geometric case.
"""
from itertools import combinations, product
import sympy as S

a, s, R, T, W, c, d, u, v = S.symbols('a s R T W c d u v')
Q = S.Rational
A = a+s-Q(1, 2)
B = Q(1, 2)-a
C = Q(1, 2)-s
k = 1-a-s
q0 = A-a*s
L = s*s+T*T/W
n1 = a*a+R*R/W
g15 = q0+R*T/W
Delta = L*n1-g15*g15

def zero(expr):
    assert S.cancel(expr) == 0

zero(q0-(A/2-B*C))
zero(s*s*Delta-2*A*B*C*L-(s*s*R-q0*T)**2/W)

# Gram norm of x*r1+z*r5, with r4=0.
def norm(x, z):
    return x*x*n1+z*z*L+2*x*z*g15

ellA = a+s
ellB = s+k
ellC = a+k
GammaA = s*R+a*T
GammaB = s*R-ellB*T
GammaC = a*T-ellC*R
zero(norm(s, a)-2*a*s*A-GammaA**2/W)
zero(norm(s, -ellB)-2*s*k*B-GammaB**2/W)
zero(norm(-ellC, a)-2*a*k*C-GammaC**2/W)

S12 = (a-c)/2+u-R-Q(1, 8)
S25 = (s+c)/2+u-T-Q(1, 8)
S35 = (s+d)/2+T-v-Q(1, 8)
h2 = Q(1, 2)+u/W
h3 = -Q(1, 2)+v/W
n2 = c*c+W*h2*h2
n3 = d*d+W*h3*h3
E2 = s*S12+a*S25
E3 = a*S35
Gamma = GammaA
K = 2*a*s*A

# Edge polarization in the specified physical coordinates.
m12 = a*c+R*h2+S12
m52 = -s*c+T*h2+S25
m13 = a*d+R*h3
m53 = -s*d+T*h3+S35
zero(s*m12+a*m52-(Gamma*h2+E2))
zero(s*m13+a*m53-(Gamma*h3+E3))
zero((Gamma*h2+E2)**2-(K+Gamma**2/W)*n2-
     (E2**2+2*Gamma*h2*E2-K*n2-Gamma**2*c*c/W))
zero((Gamma*h3+E3)**2-(K+Gamma**2/W)*n3-
     (E3**2+2*Gamma*h3*E3-K*n3-Gamma**2*d*d/W))
zero(s*(m12-m13)+a*(m52-m53)-
     (Gamma*(h2-h3)+E2-E3))

# All coefficients of this five-point affine circuit are nonzero because
# every four-element subset is a strict K4. Strict support forbids 1+4;
# actual triangle/edge intersections forbid four of the ten 2+3 partitions.
labels = (1, 2, 4, 5, 6)
actual_faces = {tuple(sorted(q)) for q in ((1,4,6),(1,6,5),(1,5,2),(2,6,4))}
allowed = set()
for bits in product((-1, 1), repeat=4):
    lam = dict(zip((1,4,5,6), bits))
    signs = {2: 1, **{i: -b for i,b in lam.items()}}
    positive = tuple(i for i in labels if signs[i] > 0)
    negative = tuple(i for i in labels if signs[i] < 0)
    if sorted((len(positive),len(negative))) != [2,3]:
        continue
    triple = positive if len(positive)==3 else negative
    if triple in actual_faces:
        continue
    allowed.add(tuple(i for i in (1,4,5,6) if lam[i]<0))
expected = {(1,), (6,), (1,4), (1,6), (4,5), (5,6)}
assert allowed == expected, allowed
assert all(4 not in q for q in allowed if 6 in q)

print('PASS exact cap Gram factorization and all three opposite-edge identities')
print('PASS positive-deficit dot identities and Cauchy--Schwarz expansions')
print('PASS six local affine sign patterns; negative lambda6 requires positive lambda4')
print('The proposed metric sign implication remains unproved; ray2_2 remains open.')
