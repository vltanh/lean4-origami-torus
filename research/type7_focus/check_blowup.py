#!/usr/bin/env python3
"""Exact finite and polynomial checks of the second blow-up limit reduction."""
from collections import Counter
from itertools import combinations, product
from pathlib import Path
import json
import sympy as S
D=Path(__file__).resolve().parent.parent/'linking_checkpoint'
case=next(c for c in json.loads((D/'cases.json').read_text()) if c['file']=='t7_ray_4.smt2')
models=json.loads((D/'ring4_full_signs.json').read_text())
A=(0,2,4,6); B=(1,3,5,7); V=tuple(range(8)); E=list(product(A,B)); Q=list(combinations(V,4)); H=S.Rational(1,2)
K={tuple(z['edge']):tuple(z['shift']) for z in case['edge_shifts']}
K.update({(j,i):(-m,-n) for (i,j),(m,n) in list(K.items())})
gauge=(-1,-1,-1,-1,0,-2,-1,-2); K={(i,j):(m,n+gauge[j]-gauge[i]) for (i,j),(m,n) in K.items()}
ring=lambda R:list(zip(R,R[1:]+R[:1]))
plus=lambda a,b:tuple(x+y for x,y in zip(a,b)); minus=lambda a,b:tuple(x-y for x,y in zip(a,b))
def sign(model,p):return (-1)**sum(i>j for i,j in combinations(p,2))*(1 if model[Q.index(tuple(sorted(p)))]=='+' else -1)
for ix,d in ((0,1),(2,-1)):
 model=models[ix]
 assert all(sign(model,T+(v,))==-1 for T in combinations(A,3) for v in B)
 assert all(sign(model,T+(v,))==1 for T in combinations(B,3) for v in A)
 assert all(sign(model,ee+ff)==(1 if (j-i)%4==d%4 else -1) for i,ee in enumerate(ring(A)) for j,ff in enumerate(ring(B)))
 assert sign(model,(0,1,4,5))==sign(model,(2,3,6,7))
 for pp in (tuple((v+2)%8 for v in V),tuple((1-v)%8 for v in V)):
  mixed=[q for q in Q if q not in (A,B)];r=sign(model,tuple(pp[v] for v in mixed[0]))*sign(model,mixed[0])
  assert all(sign(model,tuple(pp[v] for v in q))==r*sign(model,q) for q in mixed)
  for transform in (lambda m,n:(m,n),lambda m,n:(-m,-n),lambda m,n:(m+n,-n),lambda m,n:(-m-n,n)):
   g={0:(0,0)}
   for _ in V:
    for (i,j),k in K.items():
     if i in g and j not in g:g[j]=plus(g[i],minus(K[pp[i],pp[j]],transform(*k)))
   if len(g)==8 and all(minus(K[pp[i],pp[j]],transform(*k))==minus(g[j],g[i]) for (i,j),k in K.items()):break
  else:raise AssertionError('marking stabilizer')
 j=d%4;collapse={v:v for v in V};collapse[2]=0;collapse[B[(j+1)%4]]=B[j];signs={}
 for q in Q:
  z=tuple(collapse[v] for v in q)
  if len(set(z))==4:signs.setdefault(tuple(sorted(z)),set()).add(sign(model,q)*(-1)**sum(i>j for i,j in combinations(z,2)))
 assert signs[(0,1,3,4) if d==1 else (0,4,5,7)]=={-1,1}
 base,down,up=(0,2,3) if d==1 else (2,0,1)
 assert sign(model,ring(A)[1]+ring(B)[down])==1
 assert all(sign(model,ring(A)[i]+ring(B)[k])==-1 for i,k in ((2,down),(3,up),(3,down)))
 bs=(0,1,1,0)
 for i,j in ((0,1),(0,2),(2,3)):
  assert {sign(model,(A[i],A[j],B[k],B[l]))*(bs[l]-bs[k]) for k,l in combinations(range(4),2) if bs[l]!=bs[k]}=={-1,1}
 assert sign(model,ring(A)[0 if d==1 else 1]+ring(B)[0])==(-1 if d==1 else 1)
print('PASS mixed signs, collapsed duplicate minors and marking symmetries')
# In a common-line metric limit use horizontal ring steps a,b and signed projected extrinsic steps p,q.
a=S.symbols('a:4');b=S.symbols('b:4');p=S.symbols('p:4');q=S.symbols('q:4');h=S.Symbol('h');x={0:0,1:h};z={0:0,1:0}
for R,ell,v in ((A,a,p),(B,b,q)):
 for i,j,l,f in zip(R,R[1:],ell,v):x[j]=x[i]+l-K[i,j][0];z[j]=z[i]+f
X={(i,j):x[j]-x[i]+K[i,j][0]+H*K[i,j][1] for i,j in E}
N0=S.Matrix([0,0,-1,1,1,0,0,-1,-1,1,0,0,0,-1,1,0]);N1=S.Matrix([1,-1,0,0,0,1,-1,0,0,0,1,-1,-1,0,0,1])
M=S.zeros(16,14);rr={v:i+1 for i,v in enumerate(range(2,8))};gg={v:i+7 for i,v in enumerate(range(1,8))}
for k,(i,j) in enumerate(E):
 M[k,0]=1;n=K[i,j][1]
 for v,sg in ((i,-1),(j,1)):
  if v in rr:M[k,rr[v]]=sg
  if v in gg:M[k,gg[v]]=-(1+2*n)*sg
assert M.rank()==14 and M.T*N0==M.T*N1==S.zeros(14,1)
F=S.expand((N0+N1).dot(S.Matrix([X[i,j]**2-(z[j]-z[i])**2 for i,j in E])))
# Parallelogram, with q=sigma*p after equal scaling.
u,v=S.symbols('u v');alpha=S.Symbol('alpha');beta=H-alpha
for sg in (1,-1):
 sub=dict(zip(a+b+p+q,(alpha,beta,alpha,beta)*2+(u,v,-u,-v)+(sg*u,sg*v,-sg*u,-sg*v)))
 assert S.expand(F.subs(sub,simultaneous=True)-4*sg*(u*u+v*v))==0
# Rank-two triangles: common base points in the same projected direction.
alpha,beta,U,W,L,J=S.symbols('alpha beta U W L J')
for j in (1,3):
 base,down,up=(0,2,3) if j==1 else (2,0,1)
 bb=[None]*4;qq=[None]*4;bb[j]=qq[j]=0;bb[base]=qq[base]=beta;bb[up]=J;qq[up]=W;bb[down]=1-beta-J;qq[down]=-beta-W
 sub=dict(zip(a+b+p+q,(0,alpha,L,1-alpha-L)+tuple(bb)+(0,alpha,U,-alpha-U)+tuple(qq)))
 assert S.expand(F.subs(sub,simultaneous=True)-(2*(L*J-U*W)+2*alpha+2*beta-1)*(1 if j==1 else -1))==0
# Rank-one adjacent sticks in B, horizontal projection of n normalized to +1.
sub=dict(zip(b+q,(H,H,0,0,H,-H,0,0)))
assert S.expand(F.subs(sub,simultaneous=True)-(-a[0]-2*a[1]-a[2]+p[0]-p[2]+1))==0
print('PASS projected residual identities for every nonzero cross-product rank')
# Recover the eight free horizontal/vertical variables from transport exactly.
gamma=S.symbols('g:8');delta={};other={}
for i,(r,s) in enumerate(ring(A)):
 for j,(u,v) in enumerate(ring(B)):
  shifts=[K[r,u],minus(K[r,v],K[u,v]),plus(K[s,u],K[r,s]),minus(plus(K[s,v],K[r,s]),K[u,v])]
  common,n=Counter(shifts).most_common(1)[0];assert n==3;k=next(k for k,v in enumerate(shifts) if v!=common);assert k in (1,2)
  P,T=((r,u),(r,v),(s,u),(s,v))[k];dm,dn=minus(common,shifts[k]);dx=dm+H*dn;assert abs(dx)==H and dn==-(1+2*K[P,T][1])
  delta[i,j]=dx*X[P,T]+S.Rational(1,8)+dn*(gamma[T]-gamma[P]);other[i,j]=delta[i,j]-2*dx*X[P,T]
unknown=(h,)+gamma[1:]; equations=[(delta[i,j]-a[i]*b[j]+p[i]*q[j]).subs(gamma[0],0) for i,j in product(range(4),repeat=2)]
M,rhs=S.linear_eq_to_matrix(equations,unknown);inds=list(M.T.rref()[1]);assert M.rank()==8;solution=dict(zip(unknown,M[inds,:].inv()*rhs[inds,:]));solution[gamma[0]]=S.S(0)
u=S.Symbol('u');e=S.Rational(1,8)
families=[
 ((H-u,H,0,u),(H-u,-H,0,u),-u,(e-u/2,2*e-u/2,-e-u/2,-u/2,e-u/2,-u/2,e-u/2)),
 ((H-u,u,0,H),(u-H,-u,0,H),-H,(-e,u/2-2*e,-3*e,-2*e,-e,-2*e,-e)),
 ((0,u,H-u,H),(0,u,H-u,-H),-H,(-e,0,e,-u/2,-e,-2*e,-e)),
 ((0,H,H-u,u),(0,H,u-H,-u),-H,(-e,0,e,-2*e,-e,-u/2,-e)),
]
for i,(aa,pp,hh,gg) in enumerate(families,1):
 sub=dict(zip(a+b+p+q,aa+(H,H,0,0)+pp+(H,-H,0,0)))
 exp=dict(zip(unknown,(hh,)+gg));exp[gamma[0]]=0
 assert all(S.expand(solution[v].subs(sub,simultaneous=True)-w)==0 for v,w in exp.items())
 assert all(S.expand(f.subs(sub,simultaneous=True).subs(exp,simultaneous=True))==0 for f in equations)
 vals=[S.expand(f.subs(sub,simultaneous=True).subs(exp,simultaneous=True)) for f in other.values()]
 xs=[S.expand(f.subs(sub,simultaneous=True).subs(exp,simultaneous=True)) for f in X.values()]
 # All constraints here are affine in u, so the endpoint checks cover the interval.
 for t in (0,H):
  assert all(f.subs(u,t)>=0 for f in vals) and all(abs(f.subs(u,t))<=H for f in xs)
 G=[S.sympify(w) for w in (0,)+gg]; pairs=[S.expand(x-y) for x,y in product(G,repeat=2)]
 assert 3*e in pairs and all(abs(f.subs(u,t))<=3*e for f in pairs for t in (0,H))
 print('PASS family',i,'exact h,gamma; vertical spread 3/8 throughout')
print('PASS four affine families of necessary common-line limit data')
