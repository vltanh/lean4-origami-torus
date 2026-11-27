#!/usr/bin/env python3
"""Exact verification using SymPy, no floating point or numerical search."""
import sympy as s
from itertools import combinations
from sympy.polys.matrices import DomainMatrix
Q=s.Rational
x,w,h,t=s.symbols('x w h t'); L=Q(1,200)
H=Q(33,20);r=-Q(13,60);a=H*x;D=H-1+a;q=H/D
T5=((a*a-a+H*H*w)*q/H-1)/(1+q*q*w)
T3=-(-a*a*q+2*a*H+a*q+H*H*q*w+H*q*q*r*w+H*r-H)/((H+q*r)*(q*q*w+1))
P=[(0,0),(1-a-r,H+q*r),(Q(1,2),0),(a+T3,H+q*T3),(1,0),(1+T5,q*T5),(a,H),(1-a,H)]
P=[tuple(s.cancel(s.sympify(b)) for b in p) for p in P]
F=[tuple(map(int,f)) for f in '356 325 364 302 341 310 506 524 547 570 674 601 617 214 207 271'.split()]
G=[f for f in F if f not in [(3,5,6),(3,2,5)]]+[(6,3,2),(6,2,5)]
Lutz4=[tuple(map(int,f)) for f in '012 031 024 053 045 152 134 146 165 264 257 276 374 356 367 475'.split()]
perm=[2,1,4,0,3,7,5,6]
def canon(F):return {tuple(sorted(f)) for f in F}
assert canon([tuple(perm[i] for i in f) for f in G])==canon(Lutz4)
def edges(F):return {tuple(sorted(e)) for f in F for e in combinations(f,2)}

def area(a,b,c):
 A,B,C=[P[i] for i in (a,b,c)]
 return s.cancel((B[0]-A[0])*(C[1]-A[1])-(B[1]-A[1])*(C[0]-A[0]))

def poly_sign(p):
 p=s.Poly(s.expand(p.subs(w,h+1-x*x)),h)
 if p.is_zero:return 0
 def coeffs(c):
  g=s.Poly(c.subs(x,L*t),t);n=max(0,g.degree()) if not g.is_zero else 0
  return [sum(g.nth(j)*s.binomial(i,j)/s.binomial(n,j) for j in range(i+1)) for i in range(n+1)]
 B=[coeffs(p.nth(i)) for i in range(p.degree()+1)]
 if all(c>=0 for b in B for c in b) and min(B[0])>0:return 1
 if all(c<=0 for b in B for c in b) and max(B[0])<0:return -1
 return 0

def sign(p):
 a,b=s.fraction(s.cancel(p));return poly_sign(a)*poly_sign(b)
sg=[sign(area(*f)) for f in F]
assert sg==[1,1,-1,1,1,-1,-1,1,-1,1,-1,1,1,-1,-1,-1]
assert [sign(area(*f)) for f in [(3,5,6),(3,5,2),(6,2,3),(6,2,5)]]==[1,-1,-1,1]
print('PASS face orientations and convex diagonal flip')

# Use a rational function field for cone angles and planar developments.
K=s.QQ.frac_field(x,w);W=K.gens[1];X=K.gens[0];zero=K.zero;one=K.one
pp=[[K.convert(b) for b in p] for p in P]
def sub(a,b):return [u-v for u,v in zip(a,b)]
def add(a,b):return [u+v for u,v in zip(a,b)]
def mul(a,b):return [a*u for u in b]
def dot(a,b):return a[0]*b[0]+W*a[1]*b[1]
def cross(a,b):return a[0]*b[1]-a[1]*b[0]
def cm(a,b):return [a[0]*b[0]-W*a[1]*b[1],a[0]*b[1]+a[1]*b[0]]
# Product of unnormalized complex numbers of arguments theta in (0,pi).
# Physical complex representation of (A,B) is A+i*sqrt(w)*B.
for i in range(8):
 R=[one,zero]
 for f,S in zip(F,sg):
  if i not in f:continue
  j=f.index(i);b,c=f[(j+1)%3],f[(j+2)%3];u,v=sub(pp[b],pp[i]),sub(pp[c],pp[i]);R=cm(R,[dot(u,v),S*cross(u,v)])
 assert R[1]==zero and R[0]!=zero
 # Each factor nonzero on the domain. At square the product is positive,
 # and throughout it stays real and nonzero.
 assert K.to_sympy(R[0]).subs({x:0,w:1})>0
# At the square base use exact bounds by pi/4 to ensure the cone angle <4pi;
# positive and multiple of 2pi then implies exactly 2pi.
for i in range(8):
 bound=0
 for f,S in zip(F,sg):
  if i not in f:continue
  j=f.index(i);b,c=f[(j+1)%3],f[(j+2)%3];u,v=sub(pp[b],pp[i]),sub(pp[c],pp[i]);d=K.to_sympy(dot(u,v)).subs({x:0,w:1});cr=K.to_sympy(S*cross(u,v)).subs({x:0,w:1});assert cr>0
  bound+=1 if d>cr else 2 if d>0 else 3 if d>-cr else 4
 assert bound<16,(i,bound)
print('PASS all cone angles identically 2pi by continuity')

# Deterministic tree-cotree marking of the fundamental group of the torus.
E={}
for i,f in enumerate(F):
 for e in combinations(sorted(f),2):E.setdefault(e,[]).append(i)
assert all(len(v)==2 for v in E.values())
def tree(es,n):
 parent=list(range(n));out=[]
 def root(i):
  while parent[i]!=i:i=parent[i]
  return i
 for e,i,j in es:
  a,b=root(i),root(j)
  if a!=b:parent[b]=a;out.append(e)
 assert len(out)==n-1
 return set(out)
T=tree([(e,*e) for e in sorted(E)],8)
DT=tree([(e,*E[e]) for e in sorted(E) if e not in T],16)
R=sorted(set(E)-T-DT);assert len(R)==2
chart={0:{v:[pp[v][0],pp[v][1]*sg[0]] for v in F[0]}}
queue=[0]
for i in queue:
 for e in sorted(DT):
  if i not in E[e]:continue
  j=next(v for v in E[e] if v!=i)
  if j in chart:continue
  a,b=e;f=F[j]
  if f[(f.index(a)+1)%3]!=b:a,b=b,a
  assert F[i][(F[i].index(b)+1)%3]==a
  c=next(v for v in f if v not in e);pa,pb=chart[i][a],chart[i][b];u,v=sub(pp[b],pp[a]),sub(pp[c],pp[a]);rr=dot(u,u);d=dot(u,v)/rr;k=cross(u,v)*sg[j]/rr;dv=sub(pb,pa)
  pc=add(pa,add(mul(d,dv),mul(k,[-W*dv[1],dv[0]])))
  chart[j]={a:pa,b:pb,c:pc};queue.append(j)
assert len(chart)==16
periods=[sub(chart[E[e][1]][e[0]],chart[E[e][0]][e[0]]) for e in R]
u,v=periods;v=add(u,v);den=dot(u,u)
assert dot(u,v)/den==X and cross(u,v)/den==one
print('PASS marked modulus x+i*sqrt(w)')

# The 7x7 horizontal cone-angle Jacobian minor, with rows divided by sqrt(w).
J=[[zero]*16 for i in range(7)]
for f,S in zip(F,sg):
 for i in range(3):
  a,b,c=f[i:]+f[:i]
  if a==7:continue
  for v,sig in [(b,-S),(c,S)]:
   u=sub(pp[v],pp[a]);n=dot(u,u);row=[-sig*u[1]/n,sig*u[0]/n]
   for k in range(2):J[a][2*v+k]+=row[k];J[a][2*a+k]-=row[k]
cols=[1,2,5,6,10,13,15];det=DomainMatrix([[row[j] for j in cols] for row in J],(7,7),K).det()
assert sign(K.to_sympy(det))==-1
print('PASS horizontal rank seven; explicit two-parameter family supplies the remaining modulus directions')

# Generic vertical lift. A quadruple must contain a strictly noncollinear triple.
qs=list(combinations(range(8),4));assert all(any(sign(area(*tri)) for tri in combinations(q,3)) for q in qs)
Z=[Q(3,13),-Q(3,8),-Q(3,7),Q(12,13),1,-1,1,0]
S={q:sign(sum((-1)**(i+1)*Z[a]*area(*[b for b in q if b!=a]) for i,a in enumerate(q))) for q in qs}
assert sum(bool(v) for v in S.values())==67
for typ,f in [(7,F),(4,G)]:
 def get(q):return S[tuple(sorted(q))]*(-1)**sum(a>b for i,a in enumerate(q) for b in q[i+1:])
 n=0
 for a,b in edges(f):
  for c,d,e in f:
   if len({a,b,c,d,e})!=5:continue
   v0,v1,v2,v3,v4=[get(q) for q in [(b,c,d,e),(a,c,d,e),(a,b,d,e),(a,b,c,e),(a,b,c,d)]]
   assert max(v0*v1,v2*v3,v3*v4,-v2*v4)>0,(typ,a,b,c,d,e)
   n+=1
 assert n==(144 if typ==7 else 140)
 print('PASS type',typ,'all',n,'edge/face separation witnesses')
print('PASS both types on 0<=x<=1/200, w>=1-x^2')
