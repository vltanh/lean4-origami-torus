#!/usr/bin/env python3
"""Exact obstruction to the existing Type 4/7 trapezoid chamber on the
S-transformed sharp ray. SymPy identity checks only; no numerical search.
"""
import sympy as s
x,H,r=s.symbols('x H r',real=True)
w=2*x-x*x
a=H*x;D=H-1+a;q=H/D
T5=s.factor(((a*a-a+H*H*w)*q/H-1)/(1+q*q*w))
T3=s.factor(-(-a*a*q+2*a*H+a*q+H*H*q*w+H*q*q*r*w+H*r-H)/((H+q*r)*(q*q*w+1)))
P=[(0,0),(1-a-r,H+q*r),(s.Rational(1,2),0),
   (a+T3,H+q*T3),(1,0),(1+T5,q*T5),(a,H),(1-a,H)]
P=[tuple(s.factor(v) for v in p) for p in P]
def area(i,j,k):
 A,B,C=P[i],P[j],P[k]
 return s.factor((B[0]-A[0])*(C[1]-A[1])-(B[1]-A[1])*(C[0]-A[0]))
N=s.expand(D**2+H**2*w)
assert s.expand(N-(4*H**2*x+H**2-2*H*x-2*H+1))==0
A302,A214,A524,A674=[area(*q) for q in [(3,0,2),(2,1,4),(5,2,4),(6,7,4)]]
expected=[H**2*(H-1)*D/(2*(D+r)*N),-H*(D+r)/(2*D),
          H*(H-1)*(2*H*x-1)/(2*N),H*(2*H*x-1)]
for actual,formula in zip([A302,A214,A524,A674],expected):
 assert s.cancel(actual-formula)==0
assert s.cancel(2*A302*A214*A674+H**3*A524)==0
# Additional identities for the stronger all-chambers flatness obstruction.
assert s.cancel(area(2,1,7)+H*r*(2*H-1)/(2*D))==0
assert s.cancel((P[5][1]-H)+H**2*(2*H*x+H-1)/N)==0
assert s.cancel(area(7,4,5)-H*(H-1)*(2*H*x-1)*(2*H*x+H-1)/N)==0
assert s.cancel((-H+q*(a-s.Rational(1,2)))-H*(s.Rational(1,2)-H)/D)==0
# Reflection of -1/tau into the positive-real half plane.
y=s.symbols('y',positive=True)
xx=1/(2*(y*y+s.Rational(1,4)));ww=y*y/(y*y+s.Rational(1,4))**2
assert s.cancel(ww-(2*xx-xx**2))==0
print('PASS modular sharp arc w = 2*x - x^2')
print('PASS four exact oriented-area formulas')
print('PASS 2*A302*A214*A674 + H^3*A524 = 0')
print('PASS angular-order identities for the all-chambers obstruction')
print('Therefore the signs A302>0,A214<0,A524>0,A674<0 are impossible for H>0.')
print('The accompanying angle proof excludes every nondegenerate flat member of this trapezoid family.')
print('No Type 4/7 universality closure is claimed.')
