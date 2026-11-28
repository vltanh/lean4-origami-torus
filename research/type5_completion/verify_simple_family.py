#!/usr/bin/env python3
"""Exact interval proof for a simple Type 5 family. Standard library only."""
from fractions import Fraction as Q
from itertools import combinations
from math import isqrt
import time
from collections import Counter
from pathlib import Path
import re
B=1<<100
class I:
    __slots__=('l','h')
    def __init__(self,a,b=None):
        if b is not None:self.l,self.h=a,b;return
        if isinstance(a,I):self.l,self.h=a.l,a.h;return
        if isinstance(a,int):self.l=self.h=a*B;return
        f=Q(a);self.l=f.numerator*B//f.denominator;self.h=-((-f.numerator*B)//f.denominator)
    def __add__(a,b):b=I(b);return I(a.l+b.l,a.h+b.h)
    __radd__=__add__
    def __neg__(a):return I(-a.h,-a.l)
    def __sub__(a,b):return a+-I(b)
    def __rsub__(a,b):return I(b)+-a
    def __mul__(a,b):
        b=I(b);v=(a.l*b.l,a.l*b.h,a.h*b.l,a.h*b.h);return I(min(v)//B,-((-max(v))//B))
    __rmul__=__mul__
    def __truediv__(a,b):
        b=I(b);assert b.l>0 or b.h<0
        vals=(a.l*B,a.h*B);den=(b.l,b.h)
        return I(min(x//y for x in vals for y in den),max(-((-x)//y) for x in vals for y in den))
    def __rtruediv__(a,b):return I(b)/a
    def sqrt(a):
        assert a.l>=0;lo=isqrt(a.l*B);hi=isqrt(a.h*B);return I(lo,hi+(hi*hi<a.h*B))
    def sign(a):
        assert a.l>0 or a.h<0
        return 1 if a.l>0 else -1
    def abslo(a):return min(abs(a.l),abs(a.h)) if a.l*a.h>0 else 0
    def meet(a,b):
        lo,hi=max(a.l,b.l),min(a.h,b.h);assert lo<=hi;return I(lo,hi)
    def __repr__(a):return f'[{a.l/B:.12g},{a.h/B:.12g}]'
ZERO=I(0);ONE=I(1)
class J:
    # Interval AD with an independently evaluated center and the mean-value intersection.
    __slots__=('v','m','d')
    delta=(ZERO,ZERO)
    def __init__(self,a,m=None,d=None):
        if isinstance(a,J):self.v,self.m,self.d=a.v,a.m,a.d
        elif m is None:self.v=self.m=I(a);self.d=(ZERO,ZERO)
        else:self.m,self.d=m,d;self.v=a.meet(m+sum(x*y for x,y in zip(d,J.delta)))
    def __add__(a,b):
        b=J(b);return J(a.v+b.v,a.m+b.m,tuple(x+y for x,y in zip(a.d,b.d)))
    __radd__=__add__
    def __neg__(a):return J(-a.v,-a.m,tuple(-x for x in a.d))
    def __sub__(a,b):return a+-J(b)
    def __rsub__(a,b):return J(b)+-a
    def __mul__(a,b):
        b=J(b);return J(a.v*b.v,a.m*b.m,tuple(x*b.v+a.v*y for x,y in zip(a.d,b.d)))
    __rmul__=__mul__
    def __truediv__(a,b):
        b=J(b);v=a.v/b.v;return J(v,a.m/b.m,tuple((x-v*y)/b.v for x,y in zip(a.d,b.d)))
    def __rtruediv__(a,b):return J(b)/a
    def sqrt(a):
        v=a.v.sqrt();return J(v,a.m.sqrt(),tuple(x/(2*v) for x in a.d))
    def sign(a):return a.v.sign()
    def abslo(a):return a.v.abslo()
    def __repr__(a):return repr(a.v)

def dot(a,b):return sum(x*y for x,y in zip(a,b))
def add(a,b):return [x+y for x,y in zip(a,b)]
def sub(a,b):return [x-y for x,y in zip(a,b)]
def sc(a,b):return [a*x for x in b]
def sq(a):return dot(a,a)
def cross(a,b):return a[0]*b[1]-a[1]*b[0]
def det3(a,b,c):return a[0]*cross(b[1:],c[1:])-a[1]*cross([b[0],b[2]],[c[0],c[2]])+a[2]*cross(b[:2],c[:2])
F=[tuple(map(int,f)) for f in '012 031 024 053 045 152 136 164 147 175 263 237 274 256 357 465'.split()]
E={tuple(sorted(e)) for f in F for e in combinations(f,2)};FF={tuple(sorted(f)) for f in F}
A=[1,2,5];R=[3,4];L=[0,6,7];CORE=A+R
NZ={(0,4):(1,-1),(0,5):(1,0),(2,3):(0,-1),(2,4):(1,-1),(2,6):(0,-1),(2,7):(1,-1),(3,5):(1,0),(3,7):(1,0),(4,5):(0,1),(5,6):(0,-1)}
K={}
for i,j in E:K[i,j]=NZ.get((i,j),(0,0));K[j,i]=tuple(-v for v in K[i,j])
assert all(K[1,i]==(0,0) for i in range(8) if i!=1)
for i,j,k in F:assert tuple(sum(K[e][l] for e in ((i,j),(j,k),(k,i))) for l in range(2))==(0,0)
assert E=={tuple(sorted((a,b))) for a in A for b in range(8) if a!=b}|{tuple(sorted((a,b))) for a in R for b in L}
# Degree/area identity: opposite directed sides cancel the quadratic terms;
# each linear coefficient is minus the sum of cocycle values in the link.
directed=Counter((a,b) for f in F for a,b in zip(f,f[1:]+f[:1]))
assert all(n==directed[b,a]==1 for (a,b),n in directed.items())
linear=[[0,0] for _ in range(8)]
for a,b,c in F:
    for v,e in [(a,(b,c)),(b,(c,a)),(c,(a,b))]:
        for i in range(2):linear[v][i]-=K[e][i]
assert not any(any(row) for row in linear)
assert sum(cross(K[a,b],K[a,c]) for a,b,c in F)==2

def audit_source():
    root=Path(__file__).resolve().parents[2]
    p=root/'OrigamiTorus/Type5/Square.lean'
    # Standalone copy is also runnable; in the repo check the actual inputs.
    if p.is_file():
        text=p.read_text().split('def positiveShift',1)[1].split('def squareShift',1)[0]
        table={(int(a),int(b)):(int(c),int(d)) for a,b,c,d in re.findall(r'\|\s*(\d+)\s*,\s*(\d+)\s*=>\s*\((-?\d+)\s*,\s*(-?\d+)\)',text)}
        assert table==NZ
        import json
        assert F==[tuple(map(int,f)) for f in json.loads((root/'research/type5_focus/lutz_faces.json').read_text())['5'].split()]
        print('PASS archived Type 5 faces and square cocycle')
# Explicit six low-denominator coordinates and one fixed perturbation.
eps=Q(1,2**20)
coord={1:(0,0),2:(Q(43,96),-Q(1,2)+eps),3:(Q(1,2)-eps,Q(3,32)),4:(-Q(1,12),Q(7,16)),5:(-Q(1,32),-Q(5,32))}

def verify(xlo,xhi,ylo,yhi,debug=False):
    bounds=((xlo,xhi),(ylo,yhi));hh=[I((hi-lo)/2).h for lo,hi in bounds];J.delta=tuple(I(-h,h) for h in hh)
    x,y=[J(I(I(lo).l,I(hi).h),I((lo+hi)/2),tuple(I(int(i==j)) for j in range(2))) for i,(lo,hi) in enumerate(bounds)]
    phys=lambda k:[J(k[0])+x*k[1],y*k[1]]
    p={i:[J(c[0]),y*c[1]] for i,c in coord.items()}
    p[2][1]=((-Q(1,2)+eps)*(x*x+y*y)-x*p[2][0])/y
    r={i:p[i]+[J(0)] for i in A}
    D=cross(p[2],p[5]);assert D.sign()
    def solve(e,f):
        a,b=p[2];c,d=p[5];return [(e*d-b*f)/D,(a*f-e*c)/D]
    def offset(i,j):return sub(p[i],phys(K[i,j]))
    def rhs(i,j):
        # ||p_i||^2 - ||p_i-K_ij||^2 = 2 p_i.K_ij - ||K_ij||^2
        k=phys(K[i,j]);return dot(p[i],k)-sq(k)/2
    def proj(j,u):return solve(dot(offset(2,j),u)+rhs(2,j),dot(offset(5,j),u)+rhs(5,j))
    for j,s in zip(R,(1,-1)):
        xy=proj(j,p[j]);h=sq(p[j])-sq(xy);assert h.sign()==1;r[j]=xy+[s*h.sqrt()]
    for j,s in zip(L,(1,-1,1)):
        c=solve(rhs(2,j),rhs(5,j));M=[solve(offset(2,j)[i],offset(5,j)[i]) for i in range(2)]
        def Am(u):return add(sc(u[0],M[0]),sc(u[1],M[1]))
        aa=[];bb=[]
        for k in R:
            ss=offset(k,j);aa.append([ss[i]-dot(r[k][:2],M[i]) for i in range(2)]);bb.append(rhs(k,j)-dot(r[k][:2],c))
        l=sub(sc(r[4][2],aa[0]),sc(r[3][2],aa[1]));m=r[4][2]*bb[0]-r[3][2]*bb[1];ll=sq(l);assert ll.sign()==1
        u0=sc(-m/ll,l);du=[-l[1],l[0]];v0=add(Am(u0),c)+[(dot(aa[0],u0)+bb[0])/r[3][2]];dv=Am(du)+[dot(aa[0],du)/r[3][2]]
        qa=sq(dv)-sq(du);qb=2*(dot(v0,dv)-dot(u0,du));qc=sq(v0)-sq(u0);assert qa.sign()
        link={tuple(sorted(v for v in f if v!=j)) for f in F if j in f}
        nonlink=set(combinations(sorted(CORE),2))-link
        assert len(nonlink)==5 and all(sum(i in e for e in nonlink)==2 for i in CORE)
        prod=J(1)
        for a,b in sorted(nonlink):
            if (a,b) in E:
                # exact difference of two intrinsic squared lengths, no nearly equal subtraction
                e=add(sub(p[b],p[a]),phys(K[a,b]));q=phys(tuple(K[a,j][i]-K[b,j][i]-K[a,b][i] for i in range(2)));S=dot(e,q)+sq(q)/2
            else:
                assert (a,b)==(3,4);S=(sq(sub(offset(a,j),offset(b,j)))-sq(sub(r[a],r[b])))/2
            assert S.sign()==1;prod=prod*S
        disc=8*prod/(D*D)
        assert disc.sign()==1
        if xlo==xhi and ylo==yhi:
            # Independent direct quadratic discriminant check at point tests.
            disc.v.meet((qb*qb-4*qa*qc).v)
        t=(-qb+s*disc.sqrt())/(2*qa)
        p[j]=add(u0,sc(t,du));r[j]=add(v0,sc(t,dv))
    amin=B;vmin=B
    total=J(0)
    for a,b,c in F:
        ar=cross(add(sub(p[b],p[a]),phys(K[a,b])),add(sub(p[c],p[a]),phys(K[a,c])));assert ar.sign()==1;amin=min(amin,ar.abslo());total=total+ar
    # The exact symbolic area identity was checked above.
    total.v.meet((2*y).v)
    signs={}
    for q in combinations(range(8),4):
        a,b,c,d=q;v=det3(sub(r[b],r[a]),sub(r[c],r[a]),sub(r[d],r[a]));signs[q]=v.sign();vmin=min(vmin,v.abslo())
    pairs=0
    for q in combinations(range(8),5):
        ss=[(-1)**i*signs[q[:i]+q[i+1:]] for i in range(5)];pos=tuple(v for v,s in zip(q,ss) if s>0);neg=tuple(v for v,s in zip(q,ss) if s<0)
        assert not (pos in E and neg in FF or neg in E and pos in FF)
        pairs+=sum(not set(e)&set(f) and set(e)|set(f)==set(q) for e in E for f in FF)
    assert pairs==138
    if debug:print('PASS',bounds,'minarea',amin/B,'minvol',vmin/B,'p/r',p,r)
    return amin,vmin

def cover(box,maxdepth=30):
    todo=[(box,0)];n=0;dep=0;ma=mv=B;st=time.time();last=st
    while todo:
        b,d=todo.pop()
        try:
            a,v=verify(*b);n+=1;dep=max(dep,d);ma=min(ma,a);mv=min(mv,v)
        except AssertionError:
            assert d<maxdepth,(b,d)
            axis=0 if b[1]-b[0]>b[3]-b[2] else 2
            assert b[axis+1]>b[axis]
            c=(b[axis]+b[axis+1])/2;b1=list(b);b2=list(b);b1[axis+1]=c;b2[axis]=c;todo.extend([(tuple(b2),d+1),(tuple(b1),d+1)])
        if time.time()-last>10:print('progress',n,'depth',dep,'frontier',len(todo),flush=True);last=time.time()
    print('PASS modulus box',box,n,'boxes depth',dep,'area lower',ma/B,'volume lower',mv/B,'seconds',time.time()-st,flush=True)
    return n,dep,ma,mv
if __name__=='__main__':
    audit_source()
    print('PASS directed edges, cocycle, degree-one area identity')
    verify(Q(0),Q(0),Q(1),Q(1),debug=True)
    boxes=[(Q(0),Q(0),Q(1),Q(131,128)),(Q(0),Q(0),Q(131,128),Q(41,40)),(Q(0),Q(1,1024),Q(1),Q(513,512))]
    expected=[188,16,256]
    for box,n in zip(boxes,expected):assert cover(box)[0]==n
