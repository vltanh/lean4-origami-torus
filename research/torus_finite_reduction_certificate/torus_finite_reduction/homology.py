import json,itertools as it
from fractions import Fraction
from pathlib import Path
import sympy as s
F={int(k):[tuple(map(int,f)) for f in v.split()] for k,v in json.load(open(Path(__file__).with_name('lutz_faces.json'))).items()}
def edge(a,b):return tuple(sorted((a,b)))
def hdata(f):
 E=sorted({edge(a,b) for t in f for a,b in it.combinations(t,2)}); idx={e:i for i,e in enumerate(E)}
 def vec(c):
  w=[0]*len(E)
  for a,b in zip(c,c[1:]+c[:1]):w[idx[edge(a,b)]]+=1 if a<b else -1
  return w
 # spanning tree on original graph
 p=list(range(8));T=[]
 def r(i):
  while i!=p[i]:i=p[i]
  return i
 for e in E:
  a,b=map(r,e)
  if a!=b:p[b]=a;T.append(e)
 # cocycles (antisymmetric oriented edge labels) zero on tree, sum zero on face
 M=s.Matrix([vec(c) for c in f]+[[int(e==g) for e in E] for g in T]);ns=M.nullspace();assert len(ns)==2
 C=s.Matrix.hstack(*ns);assert all(v.q==1 for v in C)
 tris=[c for c in it.combinations(range(8),3) if all(edge(a,b) in idx for a,b in it.combinations(c,2)) and tuple(sorted(c)) not in {tuple(sorted(f0)) for f0 in f}]
 H={c:tuple(s.Matrix([vec(c)])*C) for c in tris};H={c:u for c,u in H.items() if u!=(0,0)}
 a,b=next((a,b) for a,b in it.combinations(H,2) if abs(s.det(s.Matrix([H[a],H[b]])))==1);U=s.Matrix([H[a],H[b]]);C=C*U.inv();H={c:tuple(s.Matrix([vec(c)])*C) for c in H};assert all(v.q==1 for v in C)
 return E,T,C,H,(a,b)
if __name__=='__main__':
 for typ in [3,4,5,6,7]:
  E,T,C,H,basis=hdata(F[typ]);classes=sorted({min(a,tuple(-v for v in a)) for a in H.values()});V=[(-1,0),(1,0),(0,1),(0,-1),(-1,1),(1,-1)]
  mats=[]
  for a,b in it.product(V,repeat=2):
   M=s.Matrix([a,b]);
   if M.det()!=1:continue
   if all(tuple(s.Matrix([u])*M) in V for u in classes):mats.append(M)
  print('type',typ,'basis',basis,'classes',classes,'counts',len(mats),flush=True)
  print(' triangles:',H,flush=True)
