#!/usr/bin/env python3
"""Exact algebra checks for the ray_4 transport and limiting obstruction."""
from collections import Counter
from itertools import combinations, product
from pathlib import Path
import json
import sympy as S
D=Path(__file__).resolve().parent.parent/'linking_checkpoint'
c=next(c for c in json.loads((D/'cases.json').read_text()) if c['file']=='t7_ray_4.smt2')
models=json.loads((D/'ring4_full_signs.json').read_text())
A=(0,2,4,6); B=(1,3,5,7); V=tuple(range(8)); E=list(product(A,B)); Q=list(combinations(V,4))
K={tuple(z['edge']):tuple(z['shift']) for z in c['edge_shifts']}
K.update({(j,i):(-m,-n) for (i,j),(m,n) in list(K.items())})
gauge=(-1,-1,-1,-1,0,-2,-1,-2)
K={(i,j):(m,n+gauge[j]-gauge[i]) for (i,j),(m,n) in K.items()}
ring=lambda R:list(zip(R,R[1:]+R[:1]))
assert all(sum(K[e][k] for e in ring(R))==(1,0)[k] for R in (A,B) for k in (0,1))
plus=lambda a,b:tuple(x+y for x,y in zip(a,b))
minus=lambda a,b:tuple(x-y for x,y in zip(a,b))
x=S.symbols('x0:8'); gamma=S.symbols('g0:8'); Dlt={}; exc=[]
for i,(a,b) in enumerate(ring(A)):
 for j,(c,d) in enumerate(ring(B)):
  shifts=[K[a,c],minus(K[a,d],K[c,d]),plus(K[b,c],K[a,b]),minus(plus(K[b,d],K[a,b]),K[c,d])]
  common,n=Counter(shifts).most_common(1)[0];assert n==3
  k=next(k for k,s in enumerate(shifts) if s!=common);assert k in (1,2)
  p,q=((a,c),(a,d),(b,c),(b,d))[k];exc.append((p,q))
  m,n=K[p,q];dm,dn=minus(common,shifts[k]);dx=dm+S.Rational(dn,2)
  assert n in (0,-1) and dn==-(2*n+1) and abs(dx)==S.Rational(1,2)
  X=x[q]-x[p]+m+S.Rational(n,2)
  Dlt[i,j]=S.expand(dx*X+S.Rational(1,8)+dn*(gamma[q]-gamma[p]))
assert sorted(exc)==sorted(E)
for i,(a,b) in enumerate(ring(A)):assert S.expand(sum(Dlt[i,j] for j in range(4))-(x[b]-x[a]+K[a,b][0]))==0
for j,(c,d) in enumerate(ring(B)):assert S.expand(sum(Dlt[i,j] for i in range(4))-(x[d]-x[c]+K[c,d][0]))==0
print('PASS: 16 exceptional edges, affine slack transport, unit marginals')

def parity(p):return (-1)**sum(i>j for i,j in combinations(p,2))
def sign(model,p):return parity(p)*(1 if model[Q.index(tuple(sorted(p)))]=='+' else -1)
for ix,delta,sigma in ((0,1,1),(2,-1,-1)):
 model=models[ix]
 assert all(sign(model,T+(v,))==-1 for T in combinations(A,3) for v in B)
 assert all(sign(model,T+(v,))==1 for T in combinations(B,3) for v in A)
 for i,ee in enumerate(ring(A)):
  for j,ff in enumerate(ring(B)):assert sign(model,ee+ff)==(1 if (j-i)%4==delta%4 else -1)
 # At t=0 all-ring quadruples vanish; rotation by +2 preserves remaining signs up to global reflection.
 pp=tuple((v+2)%8 for v in V)
 mixed=[q for q in Q if q not in (A,B)];r=sign(model,tuple(pp[v] for v in mixed[0]))*sign(model,mixed[0])
 assert all(sign(model,tuple(pp[v] for v in q))==r*sign(model,q) for q in mixed)
 # The rotation preserves the marking up to lattice isometry and integral gauge.
 for transform in (lambda m,n:(m,n),lambda m,n:(-m,-n),lambda m,n:(m+n,-n),lambda m,n:(-m-n,n)):
  g={0:(0,0)}
  for _ in V:
   for (i,j),k in K.items():
    if i in g and j not in g:g[j]=plus(g[i],minus(K[pp[i],pp[j]],transform(*k)))
  if len(g)==8 and all(minus(K[pp[i],pp[j]],transform(*k))==minus(g[j],g[i]) for (i,j),k in K.items()):break
 else:raise AssertionError('rotation marking')
 # Limiting parallelogram minors in a negatively oriented unit basis, heights 0 and 1.
 a,c=S.symbols('a c');b=S.Rational(1,2)-a;d=S.Rational(1,2)-c
 P={0:(0,0,0),2:(a,0,0),4:(a,b,0),6:(0,b,0),1:(0,0,1),3:(sigma*c,0,1),5:(sigma*c,sigma*d,1),7:(0,sigma*d,1)}
 def minor(q):return -S.Matrix([[P[i][k]-P[q[0]][k] for k in range(3)] for i in q[1:]]).det()
 assert S.expand(sign(model,(0,1,4,5))*minor((0,1,4,5))-(a-c)/2)==0
 assert S.expand(sign(model,(2,3,6,7))*minor((2,3,6,7))+(a-c)/2)==0
 # Collapse e0 and f_delta. Opposite signs for the same remaining quadruple force parallelism.
 j=delta%4;collapse={v:v for v in V};collapse[2]=0;collapse[B[(j+1)%4]]=B[j]
 signs={}
 for q in Q:
  z=tuple(collapse[v] for v in q)
  if len(set(z))==4:signs.setdefault(tuple(sorted(z)),set()).add(sign(model,q)*parity(z))
 target=(0,1,3,4) if delta==1 else (0,4,5,7)
 assert signs[target]=={-1,1}
 # In both triangles order surviving edges as (base, down, up).
 base,down,up=(0,2,3) if delta==1 else (2,0,1)
 assert sign(model,ring(A)[1]+ring(B)[down])==1
 assert all(sign(model,ring(A)[i]+ring(B)[k])==-1 for i,k in ((2,down),(3,up),(3,down)))
print('PASS: both weak orientation families, rotations, parallelogram and triangle minors')
# The correction equations' two exact null vectors.
M=S.zeros(16,14);rr={v:i+1 for i,v in enumerate(range(2,8))};gg={v:i+7 for i,v in enumerate(range(1,8))}
for k,(i,j) in enumerate(E):
 n=K[i,j][1];M[k,0]=1
 for v,z in ((i,-1),(j,1)):
  if v in rr:M[k,rr[v]]=z
  if v in gg:M[k,gg[v]]=-(1+2*n)*z
N0=S.Matrix([0,0,-1,1,1,0,0,-1,-1,1,0,0,0,-1,1,0]);N1=S.Matrix([1,-1,0,0,0,1,-1,0,0,0,1,-1,-1,0,0,1]);assert M.rank()==14 and M.T*N0==M.T*N1==S.zeros(14,1)
# Four symbolic ring edge vectors: first three independent formal vectors,
# fourth is minus their sum. Dot products are independent Gram symbols.
a=S.symbols('a0:4');b=S.symbols('b0:4');h=S.symbols('h');x={0:0,1:h}
P={0:S.zeros(3,1),1:S.zeros(3,1)}
for R,ell in ((A,a),(B,b)):
 for i,j,u in zip(R,R[1:],ell):x[j]=x[i]+u-K[i,j][0]
 for k in range(1,4):P[R[k]]=S.Matrix([int(j<k) for j in range(3)])
C=S.Matrix(3,3,lambda i,j:S.Symbol(f'C{i}{j}'))
GA=S.Matrix(3,3,lambda i,j:S.Symbol(f'G{min(i,j)}{max(i,j)}'))
GB=S.Matrix(3,3,lambda i,j:S.Symbol(f'H{min(i,j)}{max(i,j)}'))
RHS=[]
for i,j in E:
 m,n=K[i,j];X=x[j]-x[i]+m+S.Rational(n,2);u,v=P[i],P[j]
 RHS.append(S.expand(X**2-(u.T*GA*u+v.T*GB*v-2*u.T*C*v)[0]))
RHS=S.Matrix(RHS);res=[S.expand(n.dot(RHS)) for n in (N0,N1)]
# Parallelograms.
a0,b0=S.symbols('a c');U,VV,W,Z=S.symbols('U V W Z');T=S.Matrix([[1,0],[0,1],[-1,0]])
sub={a[0]:a0,a[1]:S.Rational(1,2)-a0,a[2]:a0,b[0]:b0,b[1]:S.Rational(1,2)-b0,b[2]:b0}
for X,Y in ((C,T*S.Matrix([[U,VV],[W,Z]])*T.T),):sub.update({X[i,j]:Y[i,j] for i in range(3) for j in range(3)})
# GA/GB cancel from each residual because the null vectors have zero row/column sums.
assert S.expand(res[0].subs(sub,simultaneous=True)-(4*U-4*VV+4*W+4*Z+8*a0*b0-4*a0+4*h+1)/2)==0
assert S.expand(res[1].subs(sub,simultaneous=True)-(4*U-4*VV+4*W+4*Z-8*a0*b0+4*a0-4*h-1)/2)==0
# Triangles: use base, down, up as names. Their vector sums are zero, so it
# suffices to substitute the induced bilinear products in the two independent vectors.
for j in (1,3):
 A1,A2,B0,B2,uv=S.symbols('a c d e uv')
 base,down,up=(0,2,3) if j==1 else (2,0,1)
 # scalar sides: base A=a, down A=c; base B=d, up B=e.
 sub={a[0]:0,a[1]:A1,a[2]:A2,a[3]:1-A1-A2,b[j]:0,b[base]:B0,b[up]:B2,b[down]:1-B0-B2}
 # A vectors represented by (base,down); B vectors by (base,up).
 PA={0:S.zeros(2,1),1:S.Matrix([1,0]),2:S.Matrix([0,1]),3:S.Matrix([-1,-1])}
 PB={j:S.zeros(2,1),base:S.Matrix([1,0]),up:S.Matrix([0,1]),down:S.Matrix([-1,-1])}
 z1,z2=S.symbols('z1 z2');D0=S.Matrix([[A1*B0,z1],[z2,uv]])
 sub.update({C[i,k]:(PA[i].T*D0*PB[k])[0] for i in range(3) for k in range(3)})
 assert S.expand(sum(res).subs(sub,simultaneous=True)-(2*(A2*B2-uv)+2*A1+2*B0-1)*(1 if j==1 else -1))==0
print('PASS: all exact limiting polynomial identities')
