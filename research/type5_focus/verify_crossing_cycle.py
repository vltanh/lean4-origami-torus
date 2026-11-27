#!/usr/bin/env python3
"""Exact check of the forbidden projection quartet and the tied hexagonal family."""
from itertools import combinations, permutations
import sympy as S
from focused_system import F,E,K,B,cl,D

# Integral marking isometries and height orbit reduction.
faces={frozenset(f) for f in F}
auts=[p for p in permutations(range(8)) if {frozenset(p[i] for i in f) for f in F}==faces]
assert len(auts)==6

def winding(c):
    return S.Matrix([sum(K[i,j][k] for i,j in zip(c,c[1:]+c[:1])) for k in range(2)])
cycles=[(0,1,4),(0,1,5)]
base=S.Matrix.hstack(*(winding(c) for c in cycles));assert abs(base.det())==1
metric=S.Matrix([[2,1],[1,2]])
for p in auts:
    M=S.Matrix.hstack(*(winding(tuple(p[i] for i in c)) for c in cycles))*base.inv()
    assert M.T*metric*M==metric
    # Check the whole cocycle, modulo changing the vertex lifts.
    d={i:S.Matrix([0,0]) if i==1 else S.Matrix(K[p[1],p[i]]) for i in range(8)}
    for i,j in E:
        assert S.Matrix(K[p[i],p[j]])+d[i]-d[j]==M*S.Matrix(K[i,j])

def parity(q):return (-1)**sum(a>b for i,a in enumerate(q) for b in q[i+1:])
counts={}
for pat in D['patterns']:
    h=[(1 if pat[cl.index(tuple(sorted((1,2,5,i))))]=='+' else -1)*parity((1,2,5,i)) for i in B]
    h=tuple(x*h[1] for x in h);counts[h]=counts.get(h,0)+1
assert len(counts)==7 and counts[(1,1,1,1,1)]==102 and sorted(counts.values())==[6]*6+[102]
rep=dict(zip(B,(1,1,-1,-1,-1)));orbit=set()
for p in auts:
    hh=[rep[p[i]] for i in B];orbit.add(tuple(x*hh[1] for x in hh))
assert orbit==set(counts)-{(1,1,1,1,1)}
print('PASS: all six automorphisms preserve hex metric; 7 height patterns, 2 orbits, 102+6 representative clique patterns.')

# Exact affine solution family for r_i=p_i in the anchor plane.
q={1:S.zeros(2,1)}
for i in range(8):
    if i!=1:q[i]=S.Matrix(S.symbols(f'x{i} y{i}'))
Q=S.diag(1,3)
lin=[]
for i,j in E:
    a,b=K[i,j];k=S.Matrix([a+S.Rational(b,2),S.Rational(b,2)])
    if k!=S.zeros(2,1):lin.append(S.expand(2*(k.T*Q*(q[j]-q[i]))[0]+(k.T*Q*k)[0]))
variables=[z for i in range(8) if i!=1 for z in q[i]]
assert len(lin)==10 and S.linear_eq_to_matrix(lin,variables)[0].rank()==10
u,v,a,b=S.symbols('u v a b');d=u/3+v-a/3;h=b-d;c=a+S.Rational(1,2)-3*h/2
p={1:S.zeros(2,1),6:S.Matrix([u,v]),7:S.Matrix([a,b]),0:S.Matrix([a+S.Rational(1,2),b-S.Rational(1,6)]),2:S.Matrix([a+S.Rational(1,2),d+S.Rational(1,6)]),3:S.Matrix([c,(d+b)/2-S.Rational(1,6)]),4:S.Matrix([a,d]),5:S.Matrix([c,(d+b)/2+S.Rational(1,6)])}
sub={z:w for i in range(8) if i!=1 for z,w in zip(q[i],p[i])};assert all(S.expand(e.subs(sub))==0 for e in lin)
def det(a,b):return S.det(S.Matrix.hstack(a,b))
assert S.expand(det(p[1]-p[0],p[2]-p[0])+(a+S.Rational(1,2))*(S.Rational(1,3)-h))==0
assert S.expand(det(p[4],p[7])-a*h)==0
# Weak nearest constraints imply -1/2<=a<=0, from edges 14 and 10.
assert K[1,4]==K[1,0]==(0,0) and K[0,2]==K[4,7]==(0,0)
# Nondegenerate consistently oriented faces 012,147 imply 0<h<1/3.
# Translate and rescale x by 2, y by 6 to the following coordinates with s=3h.
s=S.symbols('s',real=True);P={4:(0,-s),7:(0,s),0:(1,s-1),2:(1,1-s),3:(1-s,-1),5:(1-s,1)}
for i in P:
    target=S.Matrix(P[i]).subs(s,3*h)
    assert all(S.expand(x)==0 for x in S.diag(2,6)*(p[i]-S.Matrix([a,(d+b)/2]))-target)

def o(i,j,k):return S.factor(det(S.Matrix(P[j])-S.Matrix(P[i]),S.Matrix(P[k])-S.Matrix(P[i])))
# Each row lists the two crossing edges, then four signs on 0<s<1.
quartet=[(2,7,4,5),(3,7,4,5),(0,5,2,4),(0,4,3,5)]
expected=[(1,-1,-1,1),(1,-1,-1,1),(-1,1,1,-1),(1,-1,-1,1)]
# Exact positivity by coefficients in the Bernstein basis on [0,1],
# with at least one positive coefficient (strict in its interior).
from math import comb
for (i,j,k,l),sign in zip(quartet,expected):
    for expr,sg in zip([o(i,j,k),o(i,j,l),o(k,l,i),o(k,l,j)],sign):
        poly=S.Poly(sg*expr,s);n=poly.degree()
        coeff=[sum(poly.nth(j)*S.Rational(comb(i,j),comb(n,j)) for j in range(i+1)) for i in range(n+1)]
        assert min(coeff)>=0 and max(coeff)>0
# Sign equalities from four face pairs: A=B, A=-R, B=-C, C=-R.
relations=[((2,3,7),(0,4,5),0,1,1,1),((2,7,4),(0,4,5),0,2,1,-1),((3,5,7),(0,4,5),1,3,1,-1),((0,2,4),(0,5,3),3,2,1,-1)]
for f,g,i,j,s_i,s_j in relations:
    assert frozenset(f) in faces and frozenset(g) in faces and len(set(f)&set(g))<=1
    for k,sg in [(i,s_i),(j,s_j)]:
        a,b,c,d=quartet[k];e1,e2=(a,b),(c,d)
        if sg<0:e1,e2=e2,e1
        assert set(e1)<=set(f) and set(e2)<=set(g)
assert S.prod(s_i*s_j for f,g,i,j,s_i,s_j in relations)==-1
print('PASS: all r=p hexagonal planar configurations with nondegenerate consistently oriented intrinsic faces have the forbidden crossing quartet; no vertical lift can embed.')
