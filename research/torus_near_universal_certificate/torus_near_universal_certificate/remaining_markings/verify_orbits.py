#!/usr/bin/env python3
"""Exact marking-orbit counts, including the extra hexagonal symmetry."""
from homology import F,hdata,edge,s,it
V0=[(-1,0),(1,0),(0,1),(0,-1),(-1,1),(1,-1)]
V1=V0+[(1,1),(-1,-1)]
Q=s.Matrix([[2,1],[1,2]])
Bhex=[s.Matrix([a,b]) for a,b in it.product(V0,repeat=2) if abs(s.det(s.Matrix([a,b])))==1 and s.Matrix([a,b])*Q*s.Matrix([a,b]).T==Q]
assert len(Bhex)==12
counts={}
for typ in [4,5,7]:
 f=F[typ];E,T,C,H,basis=hdata(f);idx={e:i for i,e in enumerate(E)};fs={tuple(sorted(t)) for t in f};acts=set()
 for p in it.permutations(range(8)):
  if {tuple(sorted(p[i] for i in t)) for t in f}!=fs:continue
  rows=[]
  for cyc in basis:
   cyc=tuple(p[i] for i in cyc);v=s.zeros(1,2)
   for a,b in zip(cyc,cyc[1:]+cyc[:1]):v+=(1 if a<b else -1)*C[idx[edge(a,b)],:]
   rows.append(list(v))
  A=s.Matrix(rows);assert abs(A.det())==1;acts.add(tuple(A))
 for region,V,B in [('interior',V1,[s.eye(2),-s.eye(2)]),('ray',V0,[s.eye(2),-s.eye(2),s.Matrix([[-1,0],[-1,1]]),s.Matrix([[1,0],[1,-1]])]),('hex',V0,Bhex)]:
  mats={tuple(a+b) for a,b in it.product(V,repeat=2) if abs(s.det(s.Matrix([a,b])))==1 and all(tuple(s.Matrix([u])*s.Matrix([a,b])) in V for u in H.values())};remain=set(mats);orbits=[]
  while remain:
   m=min(remain);orb={tuple(s.Matrix(2,2,a)*s.Matrix(2,2,m)*b) for a in acts for b in B};assert orb<=mats;remain-=orb;orbits.append((m,len(orb)))
  counts[typ,region]=len(orbits)
  print('type',typ,region,'orbits',orbits)
assert [counts[t,'ray'] for t in [4,5,7]]==[2,1,4]
assert [counts[t,'hex'] for t in [4,5,7]]==[1,1,2]
assert counts[5,'interior']==2
print('remaining families',counts[5,'interior']+sum(counts[t,'ray'] for t in [4,5,7]))
print('hexagonal endpoint marking orbits',sum(counts[t,'hex'] for t in [4,5,7]))
