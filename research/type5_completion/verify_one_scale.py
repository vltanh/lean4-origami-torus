#!/usr/bin/env python3
"""Integer-interval certificate for a Type 5 core with one rational scale.
No numpy, scipy or symbolic solver needed. See one_scale.md for the proof.
"""
from fractions import Fraction as Q
from itertools import combinations
from collections import Counter
from math import isqrt
from pathlib import Path
import time,re,json,sys
B=1<<100
class I:
    __slots__=('l','h')
    def __init__(self,a,b=None):
        if b is not None:self.l,self.h=a,b;return
        if isinstance(a,I):self.l,self.h=a.l,a.h;return
        f=Q(a);self.l=f.numerator*B//f.denominator;self.h=-((-f.numerator*B)//f.denominator)
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
    def __rtruediv__(a,b):return I(b)/a
    def sqrt(a):
        assert a.l>=0;l=isqrt(a.l*B);h=isqrt(a.h*B);return I(l,h+(h*h<a.h*B))
    def sign(a):assert a.l>0 or a.h<0;return 1 if a.l>0 else -1
    def meet(a,b):
        l,h=max(a.l,b.l),min(a.h,b.h);assert l<=h;return I(l,h)
    def abslo(a):return min(abs(a.l),abs(a.h)) if a.l*a.h>0 else 0
    def __repr__(a):return f'[{a.l/B:.10g},{a.h/B:.10g}]'
ZERO=I(0)
class J:
    __slots__=('v','m','d')
    delta=(ZERO,)*3
    def __init__(self,a,m=None,d=None):
        if isinstance(a,J):self.v,self.m,self.d=a.v,a.m,a.d
        elif m is None:self.v=self.m=I(a);self.d=(ZERO,)*3
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
    def __repr__(a):return repr(a.v)
def dot(a,b):return sum(x*y for x,y in zip(a,b))
def add(a,b):return [x+y for x,y in zip(a,b)]
def sub(a,b):return [x-y for x,y in zip(a,b)]
def sc(a,b):return [a*x for x in b]
def sq(a):return dot(a,a)
def cross(a,b):return a[0]*b[1]-a[1]*b[0]
def det3(a,b,c):return a[0]*cross(b[1:],c[1:])-a[1]*cross([b[0],b[2]],[c[0],c[2]])+a[2]*cross(b[:2],c[:2])
F=[tuple(map(int,f)) for f in '012 031 024 053 045 152 136 164 147 175 263 237 274 256 357 465'.split()]
E={tuple(sorted(e)) for f in F for e in combinations(f,2)};FF={tuple(sorted(f)) for f in F};A=[1,2,5];R=[3,4];L=[0,6,7];CORE=A+R
NZ={(0,4):(1,-1),(0,5):(1,0),(2,3):(0,-1),(2,4):(1,-1),(2,6):(0,-1),(2,7):(1,-1),(3,5):(1,0),(3,7):(1,0),(4,5):(0,1),(5,6):(0,-1)}
K={}
for i,j in E:K[i,j]=NZ.get((i,j),(0,0));K[j,i]=tuple(-z for z in K[i,j])
assert len(E)==24 and len(F)==16 and all(K[1,i]==(0,0) for i in range(8) if i!=1)
assert E=={tuple(sorted((a,b))) for a in A for b in range(8) if a!=b}|{tuple(sorted((a,b))) for a in R for b in L}
for i,j,k in F:assert add(add(K[i,j],K[j,k]),K[k,i])==[0,0]
directed=Counter((a,b) for f in F for a,b in zip(f,f[1:]+f[:1]));assert all(n==directed[b,a]==1 for (a,b),n in directed.items())
linear=[[0,0] for _ in range(8)]
for a,b,c in F:
    for v,e in [(a,(b,c)),(b,(c,a)),(c,(a,b))]:
        for i in range(2):linear[v][i]-=K[e][i]
assert not any(any(row) for row in linear) and sum(cross(K[a,b],K[a,c]) for a,b,c in F)==2
# The special deficits are S_12 for leaf 6 and S_13 for leaf 7.
# Each is equal to eps times the squared length of its comparison period.
SPECIAL={6:(1,2),7:(1,3)}
EXCEPT={(1,2,3,6),(1,3,5,7)}
for j,e,mid,shift in [(6,(1,2),3,(0,1)),(7,(1,3),5,(-1,0))]:
    i,k=e;assert tuple(K[i,j][d]-K[k,j][d]-K[i,k][d] for d in range(2))==shift
    assert tuple(sorted((j,i,mid))) in FF and tuple(sorted((j,k,mid))) in FF
    assert set(combinations(sorted((i,k,mid,j)),2))<=E

def audit_source():
    root=Path(__file__).resolve().parent.parent.parent;p=root/'OrigamiTorus/Type5/Square.lean'
    if p.is_file():
        code=p.read_text().split('def positiveShift',1)[1].split('def squareShift',1)[0]
        assert {(int(a),int(b)):(int(c),int(d)) for a,b,c,d in re.findall(r'\|\s*(\d+)\s*,\s*(\d+)\s*=>\s*\((-?\d+)\s*,\s*(-?\d+)\)',code)}==NZ
        assert F==[tuple(map(int,f)) for f in json.loads((root/'research/type5_focus/lutz_faces.json').read_text())['5'].split()]
        print('PASS source face and shift tables')

def points(box):
    J.delta=tuple(I(-I((hi-lo)/2).h,I((hi-lo)/2).h) for lo,hi in box)
    x,y,s=[J(I(I(lo).l,I(hi).h),I((lo+hi)/2),tuple(I(int(i==j)) for j in range(3))) for i,(lo,hi) in enumerate(box)]
    a=Q(1,19);e=s*s;phys=lambda k:[J(k[0])+x*k[1],y*k[1]]
    p={1:[J(0),J(0)],2:[J(Q(1,2)-a),((-Q(1,2)+e)*(x*x+y*y)-x*(Q(1,2)-a))/y],3:[Q(1,2)-e,y*(3*a/2)],4:[J(-3*a/2),y*(Q(1,2)-3*a/2)],5:[J(-2*a/3),-4*a*y]}
    r={i:p[i]+[J(0)] for i in A};D=cross(p[2],p[5]);D.sign()
    def solve(e,f):
        a,b=p[2];c,d=p[5];return [(e*d-b*f)/D,(a*f-e*c)/D]
    def offset(i,j):return sub(p[i],phys(K[i,j]))
    def rhs(i,j):
        k=phys(K[i,j]);return dot(p[i],k)-sq(k)/2
    def proj(j,u):return solve(dot(offset(2,j),u)+rhs(2,j),dot(offset(5,j),u)+rhs(5,j))
    for j,sign in [(3,1),(4,-1)]:
        xy=proj(j,p[j]);h=sq(p[j])-sq(xy);assert h.sign()==1;r[j]=xy+[sign*h.sqrt()]
    for j,sign in [(0,1),(6,-1),(7,1)]:
        c=solve(rhs(2,j),rhs(5,j));M=[solve(offset(2,j)[i],offset(5,j)[i]) for i in range(2)]
        def Am(u):return add(sc(u[0],M[0]),sc(u[1],M[1]))
        aa=[];bb=[]
        for k in R:
            ss=offset(k,j);aa.append([ss[i]-dot(r[k][:2],M[i]) for i in range(2)]);bb.append(rhs(k,j)-dot(r[k][:2],c))
        l=sub(sc(r[4][2],aa[0]),sc(r[3][2],aa[1]));m=r[4][2]*bb[0]-r[3][2]*bb[1];ll=sq(l);assert ll.sign()==1
        u0=sc(-m/ll,l);du=[-l[1],l[0]];v0=add(Am(u0),c)+[(dot(aa[0],u0)+bb[0])/r[3][2]];dv=Am(du)+[dot(aa[0],du)/r[3][2]]
        qa=sq(dv)-sq(du);qb=2*(dot(v0,dv)-dot(u0,du));qa.sign()
        link={tuple(sorted(v for v in f if v!=j)) for f in F if j in f};nonlink=set(combinations(sorted(CORE),2))-link
        assert len(nonlink)==5 and all(sum(i in e for e in nonlink)==2 for i in CORE)
        prod=J(1)
        for i,k in sorted(nonlink):
            if SPECIAL.get(j)==(i,k):
                # S = s^2 ||(x,y)||^2 (leaf 6), or s^2 (leaf 7).
                # The corresponding factor s^2 is taken outside the square root.
                S=x*x+y*y if j==6 else J(1)
            elif (i,k) in E:
                d=add(sub(p[k],p[i]),phys(K[i,k]));q=phys(tuple(K[i,j][h]-K[k,j][h]-K[i,k][h] for h in range(2)));S=dot(d,q)+sq(q)/2
            else:
                assert (i,k)==(3,4);S=(sq(sub(offset(i,j),offset(k,j)))-sq(sub(r[i],r[k])))/2
            assert S.sign()==1;prod=prod*S
        root=(8*prod/(D*D)).sqrt()
        if j in SPECIAL:root=s*root
        t=(-qb+sign*root)/(2*qa);p[j]=add(u0,sc(t,du));r[j]=add(v0,sc(t,dv))
    areas=[cross(add(sub(p[b],p[a]),phys(K[a,b])),add(sub(p[c],p[a]),phys(K[a,c]))) for a,b,c in F]
    volumes={q:det3(sub(r[q[1]],r[q[0]]),sub(r[q[2]],r[q[0]]),sub(r[q[3]],r[q[0]])) for q in combinations(range(8),4)}
    return areas,volumes

def separate(signs):
    pairs=0
    for q in combinations(range(8),5):
        ss=[(-1)**i*signs[q[:i]+q[i+1:]] for i in range(5)];pos=tuple(v for v,s in zip(q,ss) if s>0);neg=tuple(v for v,s in zip(q,ss) if s<0)
        assert not (pos in E and neg in FF or neg in E and pos in FF)
        pairs+=sum(not set(e)&set(f) and set(e)|set(f)==set(q) for e in E for f in FF)
    assert pairs==138

def check(box,reference):
    areas,volumes=points(box);assert all(z.sign()==1 for z in areas)
    # For the two zero-limit determinants, verify the derivative sign, not an artificial volume margin.
    ss={q:(v.d[2].sign() if q in EXCEPT else v.sign()) for q,v in volumes.items()};assert ss==reference
    return min(z.v.abslo() for z in areas),min(v.v.abslo() for q,v in volumes.items() if q not in EXCEPT),min(v.d[2].abslo() for q,v in volumes.items() if q in EXCEPT)

def cover(box,reference,maxdepth=34):
    todo=[(box,0)];n=dep=0;mins=[B,B,B];st=time.time();last=st
    while todo:
        b,d=todo.pop()
        try:
            m=check(b,reference);mins=[min(a,b) for a,b in zip(mins,m)];n+=1;dep=max(dep,d)
        except AssertionError:
            assert d<maxdepth,(b,d)
            axis=max(range(3),key=lambda i:b[i][1]-b[i][0]);lo,hi=b[axis];assert lo<hi;c=(lo+hi)/2;b1=list(b);b2=list(b);b1[axis]=(lo,c);b2[axis]=(c,hi);todo.extend([(tuple(b2),d+1),(tuple(b1),d+1)])
        if time.time()-last>8:print('progress',n,'depth',dep,'frontier',len(todo),flush=True);last=time.time()
    print('PASS',box,'accepted',n,'depth',dep,'lower bounds',*[z/B for z in mins], 'time',time.time()-st,flush=True)
    return n

def main():
    audit_source();zero=Q(0);one=Q(1);a,v=points(((zero,zero),(one,one),(zero,zero)))
    assert all(z.sign()==1 for z in a);ref={q:(z.d[2].sign() if q in EXCEPT else z.sign()) for q,z in v.items()};separate(ref)
    print('PASS boundary reference, 68 ordinary brackets and two exceptional derivatives',[(q,ref[q],v[q].d[2]) for q in sorted(EXCEPT)],flush=True)
    boxes={
        'square':((zero,zero),(one,one),(zero,Q(1,512))),
        'boundary':((zero,Q(1,4096)),(one,Q(4097,4096)),(zero,zero))}
    for label in sys.argv[1:] or boxes:
        n=cover(boxes[label],ref);assert n=={'square':64,'boundary':32}[label]
if __name__=='__main__':main()
