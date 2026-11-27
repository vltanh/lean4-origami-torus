#!/usr/bin/env python3
"""Exact radical witness for H13 angular/metric relaxation, NOT embedded.
All intervals have integer endpoints on a fixed dyadic grid. Edge equalities
hold algebraically by the reconstruction, not by interval residual tests.
"""
from fractions import Fraction as Fq
from math import isqrt
from itertools import combinations
B=1<<200
class I:
    def __init__(self,x,y=None):
        if y is not None:self.lo,self.hi=x,y;return
        if isinstance(x,I):self.lo,self.hi=x.lo,x.hi;return
        q=Fq(x);self.lo=q.numerator*B//q.denominator;self.hi=-((-q.numerator*B)//q.denominator)
    def __add__(a,b):b=I(b);return I(a.lo+b.lo,a.hi+b.hi)
    __radd__=__add__
    def __neg__(a):return I(-a.hi,-a.lo)
    def __sub__(a,b):return a+-I(b)
    def __rsub__(a,b):return I(b)+-a
    def __mul__(a,b):
        b=I(b);v=[x*y for x in (a.lo,a.hi) for y in (b.lo,b.hi)]
        return I(min(v)//B,-((-max(v))//B))
    __rmul__=__mul__
    def __truediv__(a,b):
        b=I(b);assert b.sign()
        return I(min(x*B//y for x in (a.lo,a.hi) for y in (b.lo,b.hi)),max(-((-x*B)//y) for x in (a.lo,a.hi) for y in (b.lo,b.hi)))
    def sign(a):return 1 if a.lo>0 else -1 if a.hi<0 else 0
    def sqrt(a):
        assert a.lo>=0;l=isqrt(a.lo*B);h=isqrt(a.hi*B);return I(l,h+int(h*h<a.hi*B))
    def mid(a):return (a.lo+a.hi)/(2*B)
    def abslo(a):return min(abs(a.lo),abs(a.hi)) if a.sign() else 0

def plus(a,b):return [x+y for x,y in zip(a,b)]
def minus(a,b):return [x-y for x,y in zip(a,b)]
def scale(a,v):return [a*x for x in v]
def dot(a,b):return sum(x*y for x,y in zip(a,b))
def prod(A,x):return [dot(a,x) for a in A]
def h(a,b):return a[0]*b[0]+a[1]*b[1]+(a[0]*b[1]+a[1]*b[0])/2
def norm(a):return h(a,a)
def det2(a,b):return a[0]*b[1]-a[1]*b[0]
def det3(a,b,c):return a[0]*det2(b[1:],c[1:])-a[1]*det2([b[0],b[2]],[c[0],c[2]])+a[2]*det2(b[:2],c[:2])
def solve(A,b):
    n=len(b);M=[list(a)+[v] for a,v in zip(A,b)]
    assert all(len(a)==n+1 for a in M)
    for i in range(n):
        j=max(range(i,n),key=lambda k:M[k][i].abslo());assert M[j][i].sign()
        M[i],M[j]=M[j],M[i];M[i]=[v/M[i][i] for v in M[i]]
        for j in range(n):
            if i!=j:M[j]=minus(M[j],scale(M[j][i],M[i]))
    return [a[-1] for a in M]

faces=[tuple(map(int,s)) for s in '012 031 024 053 045 152 134 146 165 264 257 276 374 356 367 475'.split()]
F={tuple(sorted(f)) for f in faces};E={e for f in F for e in combinations(f,2)}
sh={'01':(-1,0),'03':(-1,0),'12':(1,0),'15':(0,1),'25':(-1,1),'27':(-1,1),'35':(1,0),'36':(1,-1),'56':(0,-1),'67':(-1,1)};K={}
for i,j in E:K[i,j]=list(map(I,sh.get(str(i)+str(j),(0,0))));K[j,i]=scale(-1,K[i,j])
for f in faces:assert all(sum(K[i,j][k].lo for i,j in zip(f,f[1:]+f[:1]))==0 for k in (0,1))
# The triangular period cycles 014 and 025 have independent periods.
def period(f):return [sum(K[i,j][k].lo for i,j in zip(f,f[1:]+f[:1]))//B for k in (0,1)]
assert abs(det2(period((0,1,4)),period((0,2,5))))==1
# Eight free rational scalars: six anchor coordinates, root x coordinates.
seed={0:('-0.33604660757808819','-0.16839806526308507'),1:('0.10979836963237599','0.26817309790842248'),2:('-0.36086629216900307','0.20834995426782357'),3:('0.52800108904971199','-0.31247171543088065'),4:('0','0'),5:('0.037302453201217493','-0.42670569419519416'),6:('-0.17271669726200217','0.3741754605889076'),7:('0.38772603462479516','-0.43024607244998059')}
p={i:list(map(I,seed[i])) for i in (4,5,1,6)};A=(5,1,6)
def d(i,j):return norm(plus(minus(p[j],p[i]),K[i,j]))
G=[[(norm(p[i])+norm(p[j])-(d(i,j) if i!=j else I(0)))/2 for j in A] for i in A]
assert G[0][0].sign()==1 and (G[0][0]*G[1][1]-G[0][1]*G[1][0]).sign()==1 and det3(*G).sign()==1
c={4:[I(0)]*3,5:[I(1),I(0),I(0)],1:[I(0),I(1),I(0)],6:[I(0),I(0),I(1)]}
def ext(u,v):return dot(u,prod(G,v))
def eqpoly(v0,dv,u0,du):return ext(dv,dv)-norm(du),2*(ext(v0,dv)-h(u0,du)),ext(v0,v0)-norm(u0)
def quadratic(a,b,c):
    assert a.sign();D=b*b-4*a*c;assert D.sign()==1
    return [(-b+s*D.sqrt())/(2*a) for s in (1,-1)]
def choose(j,rs):
    y=Fq(seed[j][1]);errs=[abs(Fq(t.mid())-y) for t in rs]
    i=min(range(2),key=lambda k:errs[k]);assert errs[i]<Fq(1,1000000) and errs[1-i]>Fq(1,1000000)
    return i,rs[i]
# Each root j adjacent to all anchors. Use v0+y*dv in anchor basis.
branches=[]
for j in (2,3):
    x=I(seed[j][0]);u0=[x,I(0)];du=[I(0),I(1)]
    s=[minus(p[i],K[i,j]) for i in A]
    b0=[h(t,u0)+(G[k][k]-norm(t))/2 for k,t in enumerate(s)]
    b1=[h(t,du) for t in s];v0=solve(G,b0);dv=solve(G,b1)
    k,y=choose(j,quadratic(*eqpoly(v0,dv,u0,du)));branches.append((j,k));p[j]=plus(u0,scale(y,du));c[j]=plus(v0,scale(y,dv))
# Four linear equations for (c_x,c_y,c_z,u_x), holding u_y free.
for j in (0,7):
    ns=[i for i in range(8) if i!=4 and (i,j) in K];assert len(ns)==4
    M=[];b0=[];b1=[]
    for i in ns:
        s=minus(p[i],K[i,j]);M.append(prod(G,c[i])+[-h(s,[I(1),I(0)])]);b0.append((ext(c[i],c[i])-norm(s))/2);b1.append(h(s,[I(0),I(1)]))
    z0=solve(M,b0);dz=solve(M,b1);u0=[z0[3],I(0)];du=[dz[3],I(1)];v0=z0[:3];dv=dz[:3]
    k,y=choose(j,quadratic(*eqpoly(v0,dv,u0,du)));branches.append((j,k));p[j]=plus(u0,scale(y,du));c[j]=plus(v0,scale(y,dv))
print('radical branch indices (0=positive sqrt)',branches)
# Reconstructed metric equalities hold identically. All further tests are strict.
areas=[];nearest=[]
for i,j,k in faces:areas.append(-det2(plus(minus(p[j],p[i]),K[i,j]),plus(minus(p[k],p[i]),K[i,k])))
for i,j in E:
    x,y=plus(minus(p[j],p[i]),K[i,j]);z=[2*x+y,x+2*y,x-y];nearest.extend([1+t for t in z]+[1-t for t in z])
assert all(a.sign()==1 for a in areas+nearest)
# H13 transverse order, normalizing ambient reflection using det(4,5,0,1).
def det(q):i,j,k,l=q;return det3(minus(c[j],c[i]),minus(c[k],c[i]),minus(c[l],c[i]))
ori=det((4,5,0,1)).sign();assert ori
Q=list(combinations(range(8),4));signs={q:ori*det(q).sign() for q in Q};assert all(signs.values())
W=(0,7,2,3,6,1);assert all(ori*det((4,5,i,j)).sign()==1 for i,j in combinations(W,2))
# All nonedge chord contractions, including the seven possible nearest shifts.
shifts=[(0,0),(1,0),(-1,0),(0,1),(0,-1),(1,-1),(-1,1)];chord=[]
for i,j in combinations(range(8),2):
    if (i,j) in E:continue
    v=minus(c[j],c[i]);dist=ext(v,v);assert dist.sign()==1
    for k in shifts:chord.append(norm(plus(minus(p[j],p[i]),list(map(I,k))))-dist)
assert all(t.sign()==1 for t in chord)
# A forbidden edge/face crossing suffices to refute embedding.
crossings=[]
for C in combinations(range(8),5):
    pos=tuple(v for k,v in enumerate(C) if (-1)**k*signs[C[:k]+C[k+1:]]>0);neg=tuple(v for v in C if v not in pos)
    if (pos in E and neg in F) or (neg in E and pos in F):crossings.append((pos,neg))
assert len(crossings)==10
H='-++-++--++--+-+--+-++++--++-+-+++++-++--+--+--+--++--+-+-++--+--++----';bad=[q for q,s in zip(Q,H) if signs[q]!=(1 if s=='+' else -1)]
assert len(bad)==17
print('minimum intrinsic face double-area bound',min(a.lo for a in areas)/B)
print('minimum nearest-lift slack bound',min(a.lo for a in nearest)/B)
print('minimum nonedge squared chord slack bound',min(a.lo for a in chord)/B)
print('H13 mismatched signs',len(bad),'crossing circuits',len(crossings),crossings)
print('PASS exact angular/metric relaxation witness; NOT embedded and NOT in H13')
