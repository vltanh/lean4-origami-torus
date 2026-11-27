#!/usr/bin/env python3
"""Exact SAT certificates for both 04 local-tetrahedron relaxations.

These are intrinsic edge metrics with every K4 individually Euclidean.
No simultaneous spatial realization or embedded torus is asserted.
The checks use the archived cocycle and direct rational Gram determinants,
independently of the quartic formulas in remaining_local_metric.py.
"""
from fractions import Fraction as F
from itertools import combinations, permutations
from pathlib import Path
import json

ROOT=Path(__file__).resolve().parents[1]

def determinant(M):
 n=len(M)
 return sum((-1)**sum(p[i]>p[j] for i,j in combinations(range(n),2))*
            product(M[i][p[i]] for i in range(n))
            for p in permutations(range(n)))

def product(v):
 out=F(1)
 for x in v:out*=x
 return out

def witness(mark,y=10**6):
 assert mark in (1,2) and y>=10**6
 t=F(1,y*y)
 if mark==1:a,b,Q,R=F(9,20),F(2,5),F(11,200),F(1,100)
 else:a,b,Q,R=F(47,100),F(7,50),F(1,20),F(1,10)
 h=[a+t/100,b,F(1,2)-t/100,b]*2
 v=[F(1,2)-t*(2*Q+R),t*Q,t*R,t*Q]*2
 return h,v

def verify(mark,y=10**6):
 t=F(1,y*y);h,v=witness(mark,y)
 cases=json.loads((ROOT/'linking_checkpoint/cases.json').read_text())
 case=next(c for c in cases if c['file']==f't7_ray_{mark}.smt2')
 K={tuple(e['edge']):tuple(e['shift']) for e in case['edge_shifts']}
 K.update({(j,i):(-m,-n) for (i,j),(m,n) in list(K.items())})
 faces=[tuple(map(int,f)) for f in json.loads((ROOT/'linking_checkpoint/lutz_faces.json').read_text())['7'].split()]
 # Reconstruct vertex coordinates from the actual archive, not cyclic
 # shortcut formulas. Last-edge closure checks the marking as well.
 x=[F(0)];z=[F(0)]
 for i in range(7):
  m,n=K[i,i+1];x.append(x[-1]-h[i]-m-F(n,2));z.append(z[-1]+v[i]-n)
 intrinsic={};D={}
 for (i,j),(m,n) in K.items():
  X=x[j]-x[i]+m+F(n,2);V=z[j]-z[i]+n
  intrinsic[i,j]=(X,V);D[i,j]=X*X+y*y*V*V
  assert abs(X)<F(1,2)
  assert abs(V)+t*abs(X)/2<F(1,2)+t/8
  assert D[i,j]>0
 for i in range(8):
  assert intrinsic[i,(i+1)%8]==(-h[i],v[i])
 assert {i for i in range(8) if abs(v[i])>=F(1,1000)}=={0,4}
 assert all(abs(v[i])<F(1,1000) for i in (1,2,3,5,6,7))
 areas=[]
 for a,b,c in faces:
  u,vv=intrinsic[a,b];p,q=intrinsic[a,c]
  assert (u+intrinsic[b,c][0],vv+intrinsic[b,c][1])==(p,q)
  areas.append(u*q-vv*p)
 assert min(areas)>0 and sum(areas)==2
 cliques=[S for S in combinations(range(8),4) if all((a,b) in D for a,b in combinations(S,2))]
 assert len(cliques)==16
 for S in cliques:
  a,*rest=S
  G=[[(D[a,i]+D[a,j]-(D[i,j] if i!=j else 0))/2 for j in rest] for i in rest]
  # Sylvester's criterion proves each six-edge metric is a genuine
  # nondegenerate Euclidean tetrahedron, with no solver trust.
  for n in range(1,4):assert determinant([r[:n] for r in G[:n]])>0,(mark,S,n)
 return dict(marking=mark,mask='04',y=y,nearest_edges=24,positive_faces=16,positive_definite_cliques=16)

if __name__=='__main__':
 for mark in (1,2):print(json.dumps(verify(mark)))
 print('PASS exact local SAT certificates; global metric/embedding remains open')
