#!/usr/bin/env python3
"""Exact radical reconstruction of one square Type 5 paper torus.
Python stdlib only; all enclosures have integer endpoints. No numerical root solving.
The equations giving the radicals and the proof of sufficiency are in README.md.
"""
from fractions import Fraction as Fr
from math import isqrt
from itertools import combinations, product
B=1<<200
class I:
    def __init__(self,a,b=None):
        if b is not None:self.l,self.h=a,b;return
        if isinstance(a,I):self.l,self.h=a.l,a.h;return
        q=Fr(a);self.l=q.numerator*B//q.denominator;self.h=-((-q.numerator*B)//q.denominator)
    def __add__(a,b):b=I(b);return I(a.l+b.l,a.h+b.h)
    __radd__=__add__
    def __neg__(a):return I(-a.h,-a.l)
    def __sub__(a,b):return a+-I(b)
    def __rsub__(a,b):return I(b)+-a
    def __mul__(a,b):
        b=I(b);v=[x*y for x in (a.l,a.h) for y in (b.l,b.h)];return I(min(v)//B,-((-max(v))//B))
    __rmul__=__mul__
    def __truediv__(a,b):
        b=I(b);assert b.l>0 or b.h<0
        return I(min(x*B//y for x in (a.l,a.h) for y in (b.l,b.h)),max(-((-x*B)//y) for x in (a.l,a.h) for y in (b.l,b.h)))
    def sqrt(a):
        assert a.l>=0
        l=isqrt(a.l*B);h=isqrt(a.h*B);return I(l,h+(h*h<a.h*B))
    def sign(a):
        assert a.l>0 or a.h<0
        return 1 if a.l>0 else -1
    def abslo(a):return min(abs(a.l),abs(a.h)) if a.l*a.h>0 else 0
    def midpoint(a):return (a.l+a.h)/(2*B)

def dot(a,b):return sum(x*y for x,y in zip(a,b))
def add(a,b):return [x+y for x,y in zip(a,b)]
def sub(a,b):return [x-y for x,y in zip(a,b)]
def sc(a,b):return [a*x for x in b]
def sq(a):return dot(a,a)
def cross(a,b):return a[0]*b[1]-a[1]*b[0]
def det3(a,b,c):return a[0]*cross(b[1:],c[1:])-a[1]*cross([b[0],b[2]],[c[0],c[2]])+a[2]*cross(b[:2],c[:2])
def solve2(a,b,c,d,e,f):
    det=a*d-b*c;assert det.sign();return [(e*d-b*f)/det,(a*f-e*c)/det]
F=[tuple(map(int,f)) for f in '012 031 024 053 045 152 136 164 147 175 263 237 274 256 357 465'.split()]
E={tuple(sorted(e)) for f in F for e in combinations(f,2)}
A=[1,2,5];R=[3,4];L=[0,6,7]
assert E=={tuple(sorted((a,b))) for a in A for b in range(8) if a!=b}|{tuple(sorted((a,b))) for a in R for b in L}
# Gauge all shifts on edges out of vertex 1 to zero. Square lattice basis is (1,0),(0,1).
NZ={(0,4):(1,-1),(0,5):(1,0),(2,3):(0,-1),(2,4):(1,-1),(2,6):(0,-1),(2,7):(1,-1),(3,5):(1,0),(3,7):(1,0),(4,5):(0,1),(5,6):(0,-1)}
assert set(NZ)<=E
K={}
for i,j in E:K[i,j]=NZ.get((i,j),(0,0));K[j,i]=tuple(-v for v in K[i,j])
assert all(K[1,i]==(0,0) for i in range(8) if i!=1)
for i,j,k in F:assert tuple(sum(K[e][l] for e in ((i,j),(j,k),(k,i))) for l in range(2))==(0,0)
# These are the integral homology basis cycles of the triangulation; see proof notes.
C=[]
for cyc in [(0,1,4),(0,1,5)]:C.append([sum(K[e][l] for e in zip(cyc,cyc[1:]+cyc[:1])) for l in range(2)])
assert abs(C[0][0]*C[1][1]-C[0][1]*C[1][0])==1
# Exact rational base inputs, not approximations to an unspecified root.
p={1:[I(0),I(0)]}
for j,xy in {2:('0.444720882667740','-0.499972918103549'),5:('-0.039101278348661','-0.213154941393696'),3:('0.499999999999045','0.087262616850970'),4:('-0.081664706988789','0.418104802964447')}.items():p[j]=[I(x) for x in xy]
r={j:p[j]+[I(0)] for j in A}
assert cross(p[2],p[5]).sign()
def project(j,u):
    # Find extrinsic planar part for an intrinsic point u from the two subtracted anchor equations.
    s2=sub(p[2],K[2,j]);s5=sub(p[5],K[5,j]);v2=r[2][:2];v5=r[5][:2]
    rhs2=dot(s2,u)+(sq(v2)-sq(s2))/2;rhs5=dot(s5,u)+(sq(v5)-sq(s5))/2
    return solve2(v2[0],v2[1],v5[0],v5[1],rhs2,rhs5)
for j,sign in [(3,1),(4,-1)]:
    xy=project(j,p[j]);h=sq(p[j])-sq(xy);assert h.sign()==1;r[j]=xy+[sign*h.sqrt()]

def candidates(j):
    z=[I(0),I(0)];b=project(j,z);Ae=[sub(project(j,[I(int(i==k)) for i in range(2)]),b) for k in range(2)]
    def Am(u):return add(sc(u[0],Ae[0]),sc(u[1],Ae[1]))
    aa=[];bb=[]
    for k in R:
        s=sub(p[k],K[k,j]);aa.append([s[i]-dot(r[k][:2],Ae[i]) for i in range(2)]);bb.append((sq(r[k])-sq(s))/2-dot(r[k][:2],b))
    l=sub(sc(r[4][2],aa[0]),sc(r[3][2],aa[1]));m=r[4][2]*bb[0]-r[3][2]*bb[1];assert sq(l).sign()==1
    u0=sc(-m/sq(l),l);du=[-l[1],l[0]]
    v0=add(Am(u0),b)+[(dot(aa[0],u0)+bb[0])/r[3][2]];dv=Am(du)+[dot(aa[0],du)/r[3][2]]
    a=sq(dv)-sq(du);bq=2*(dot(v0,dv)-dot(u0,du));cq=sq(v0)-sq(u0)
    disc=bq*bq-4*a*cq;assert disc.sign()==1 and a.sign()
    for s in (1,-1):
        t=(-bq+s*disc.sqrt())/(2*a);yield s,add(u0,sc(t,du)),add(v0,sc(t,dv))

def valid(p,r):
    try:
        orient=[];minarea=B;total=I(0)
        for i,j,k in F:
            d=cross(add(sub(p[j],p[i]),K[i,j]),add(sub(p[k],p[i]),K[i,k]));orient.append(d.sign());minarea=min(minarea,d.abslo());total=total+d
        if len(set(orient))!=1:return None
        # Signed double area = twice integer degree times covolume (1 here).
        tt=orient[0]*total
        if not (tt.l>B and tt.h<3*B):return None
        # All edge lengths agree exactly by the reconstruction equations. The following
        # nearest-image inequalities are an additional strict check, not needed for sufficiency.
        minshort=B
        for i,j in E:
            u=add(sub(p[j],p[i]),K[i,j])
            for a in [[1,0],[0,1]]:
                z=2*dot(u,a);gap=min(B-z.h,B+z.l)
                if gap<=0:return None
                minshort=min(minshort,gap)
        signs={};margin=B
        for q in combinations(range(8),4):
            a,b,c,d=q;v=det3(sub(r[b],r[a]),sub(r[c],r[a]),sub(r[d],r[a]));signs[q]=v.sign();margin=min(margin,v.abslo())
        ff={tuple(sorted(f)) for f in F};pairs=0
        for q in combinations(range(8),5):
            ss=[(-1)**i*signs[q[:i]+q[i+1:]] for i in range(5)];pos=tuple(v for v,s in zip(q,ss) if s>0);neg=tuple(v for v,s in zip(q,ss) if s<0)
            if (pos in E and neg in ff) or (neg in E and pos in ff):return None
            pairs+=sum(not set(e)&set(f) and set(e)|set(f)==set(q) for e in E for f in ff)
        return minarea,minshort,margin,pairs
    except AssertionError:return None

cs=[list(candidates(j)) for j in L];wins=[]
for opts in product(*cs):
    pp=dict(p);rr=dict(r)
    for j,(s,u,v) in zip(L,opts):pp[j]=u;rr[j]=v
    ans=valid(pp,rr)
    if ans:
        wins.append(opts);print('PASS roots 3:+, 4:-; leaf signs',[z[0] for z in opts]);print('minimum oriented intrinsic area lower bound',ans[0]/B);print('minimum shortest-edge slack lower bound',ans[1]/B);print('minimum absolute affine determinant lower bound',ans[2]/B);print('disjoint edge-face checks',ans[3]);print('extrinsic coordinates (decimal display only)')
        for j in range(8):print(j,*[v.midpoint() for v in rr[j]])
assert len(wins)>=1
print('PASS exact algebraic square-torus realization of Type 5')
