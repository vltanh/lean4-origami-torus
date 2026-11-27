#!/usr/bin/env python3
"""Exact embedded six-vertex partial realization in B1.1.
Rational anchor Gram matrix; the remaining two points use quadratic radicals.
Run with assertions enabled. No numeric arithmetic is trusted.
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
from pathlib import Path
import sys,json
P=Path(__file__).resolve().parent
sys.path.insert(0,str(P.parent.parent))
import focused_system as fs
from satgeom import Q,lit
V=(1,2,3,4,5,7); A=(1,2,7); R=(3,4)
E=[e for e in fs.E if set(e)<=set(V)]
F=[f for f in fs.F if set(f)<=set(V)]
# Gauge vertex 5 as universal origin on this induced subcomplex.
g={i:fs.K[5,i] if i!=5 else (0,0) for i in V}
def phys(a,b):return [Fr(2*a+b,2),Fr(b,2)]
K={e:phys(*(z[i]+g[e[0]][i]-g[e[1]][i] for i in range(2))) for e,z in fs.K.items() if set(e)<=set(V)}
assert all(K[5,i]==[0,0] for i in V if i!=5)
def d(u,v):return u[0]*v[0]+3*u[1]*v[1]
def gram(u,v,k):return d(u,v)-d(sub(v,u),k)-d(k,k)/2
# All inputs are exact rational numbers in scaled hexagonal coordinates.
p={i:list(map(Fr,xy)) for i,xy in {
 1:('0.057681158541','-0.100369943614'),
 2:('0.427853619773','-0.051339001055'),
 7:('-0.213447364921','-0.044536031579'),
 5:('0','0')}.items()}
H=[[d(p[i],p[i]) if i==j else gram(p[i],p[j],K[i,j]) for j in A] for i in A]
D=det3(*H)
assert H[0][0]>0 and H[0][0]*H[1][1]-H[0][1]**2>0 and D>0
# The cofactor formula in exact rational arithmetic.
J=[[(-1)**(i+j)*cross([H[k][l] for l in range(3) if l!=i],[H[m][l] for l in range(3) if l!=i])/D for j in range(3) for k,m in [tuple(l for l in range(3) if l!=j)]] for i in range(3)]
assert [[dot(h,j) for j in zip(*J)] for h in H]==[[int(i==j) for j in range(3)] for i in range(3)]
def mv(M,v):return [dot(row,v) for row in M]
def quad(v):return dot(v,mv(H,v))
def bcol(i,q):return [gram(p[a],q,K[a,i]) for a in A]
def root(i,x):
 def f(y):
  q=[x,y];b=bcol(i,q);return dot(b,mv(J,b))-d(q,q)
 c=f(Fr(0));a=(f(Fr(1))+f(Fr(-1)))/2-c;b=(f(Fr(1))-f(Fr(-1)))/2
 assert a!=0 and b*b-4*a*c>0
 for sg in (1,-1):
  y=(I(-b)+sg*I(b*b-4*a*c).sqrt())/I(2*a)
  q=[I(x),y];w=mv(J,bcol(i,q));yield sg,q,w
r={5:[I(0)]*3,**{i:[I(int(k==j)) for k in range(3)] for j,i in enumerate(A)}}
# All 14 chambers have the same signs on this six-vertex subset.
ch=json.loads((P.parent/'branches.json').read_text())[0];assert ch['id']=='B1.1' and len(ch['chambers'])==14
s=[];an=lit((1,2,5,3))
for pat in ch['chambers']:
 z=[1 if x=='+' else -1 for x in pat];s.append([v*z[abs(an)-1]*(1 if an>0 else -1) for v in z])
common={q:s[0][j] for j,q in enumerate(Q) if all(t[j]==s[0][j] for t in s)}
assert len(common)==64
V5=(1,2,3,5,7)
for z in s:
    rad=[(-1)**k*z[Q.index(V5[:k]+V5[k+1:])] for k in range(5)]
    assert {v for v,t in zip(V5,rad) if t==rad[0]}=={1,3,7}
T=list(combinations(V,4));assert all(q in common for q in T)
# The anchor's Euclidean basis is chosen with negative ambient orientation.
def ori(q):a,*v=q;return -det3(*(sub(r[i],r[a]) for i in v))
def check():
 margins={}
 def pos(name,z):
  z=I(z);assert z.l>0,(name,z.midpoint());margins[name]=min(margins.get(name,B),z.l)
 for i,j in E:
  u=add(sub(p[j],p[i]),K[i,j]);pos('edge nonzero',d(u,u))
  for a,b in [(1,0),(0,1),(-1,1)]:
   z=2*d(u,phys(a,b));pos('shortest slack',1-z);pos('shortest slack',1+z)
 for a,b,c in F:
  pos('face double area',-cross(add(sub(p[b],p[a]),K[a,b]),add(sub(p[c],p[a]),K[a,c])))
 for q in T:pos('affine determinant (basis coords)',common[q]*ori(q))
 # The unique nonedge 34 has distance strictly less than every torus translate.
 assert set(combinations(V,2))-set(E)=={(3,4)}
 for i in R:pos('covering radius slack',I(Fr(1,3))-d(p[i],p[i]))
 dist=quad(sub(r[4],r[3]));pos('nonedge distance positive',dist);pos('diameter slack',I(Fr(1,3))-dist)
 for a,b in product(range(-2,3),repeat=2):
  u=add(sub(p[4],p[3]),phys(a,b));pos('nonedge contraction slack',d(u,u)-dist)
 # With no coplanar 4-subsets, only 5-point circuits can intersect disjoint
 # simplices. A (2,3) circuit is forbidden if its supports are an edge and face.
 Tf={tuple(sorted(f)) for f in F};Es=set(E)
 for C in combinations(V,5):
  signs=[(-1)**i*ori(C[:i]+C[i+1:]).sign() for i in range(5)]
  for sg in (1,-1):
   U=tuple(x for x,v in zip(C,signs) if v==sg);W=tuple(x for x,v in zip(C,signs) if v!=sg)
   assert not (U in Es and W in Tf)
 return margins
passed=[]
for (sg3,q3,w3),(sg4,q4,w4) in product(root(3,Fr('-0.281057368722')),root(4,Fr('0.064852921665'))):
 p.update({3:q3,4:q4});r.update({3:w3,4:w4})
 try:m=check()
 except AssertionError:continue
 passed.append((sg3,sg4));print('root choices',sg3,sg4,'PASS')
 print('intrinsic positions:',[(i,[I(x).midpoint() for x in p[i]]) for i in V])
 print('basis coordinates:',[(i,[I(x).midpoint() for x in r[i]]) for i in V])
 for k,v in m.items():print(k,': lower bound',v/B)
assert passed
print('PASS:',len(V),'vertices,',len(E),'edges,',len(F),'faces,',len(T),'strict common orientations; all inherited simplex intersections excluded.')
