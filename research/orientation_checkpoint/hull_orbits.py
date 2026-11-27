#!/usr/bin/env python3
from satgeom import *
from collections import Counter
TRI=list(it.combinations(V,3));index={t:i for i,t in enumerate(TRI)}
def run(t):
 n,C,T,E,N=formula(t);T=set(T);auto=[p for p in it.permutations(V) if {tuple(sorted(p[i] for i in f)) for f in T}==T]; print('type',t,'automorphisms',len(auto),flush=True)
 H=[]
 for tri in TRI:
  ds=[lit((*tri,j)) for j in V if j not in tri];a,b,h=range(n+1,n+4);n+=3;H.append(h)
  for v,D in [(a,ds),(b,[-l for l in ds])]:
   C.extend([[-v,l] for l in D]);C.append([v]+[-l for l in D])
  C.extend([[-a,h],[-b,h],[-h,a,b]])
 s=SAT(n,C);ct=Counter();results=[];allh=0
 while s.check()==1:
  m=s.model(n);h=tuple(tri for tri,i in zip(TRI,H) if m[i-1]==1);orb={tuple(sorted(tuple(sorted(p[i] for i in f)) for f in h)) for p in auto};h0=min(orb);allh+=len(orb);hv=set(sum(h,()));ct[(len(hv),len(set(h)&T))]+=1;results.append({'hull':h0,'orbit_size':len(orb)})
  for h1 in orb:
   J=set(h1);s.add([(-1 if tri in J else 1)*i for tri,i in zip(TRI,H)])
  if len(results)%20==0:print('progress',len(results),'labelled',allh,flush=True)
 print('DONE',t,'orbits',len(results),'labelled',allh,'by (hull vertices, surface faces on hull)',dict(ct),flush=True)
 (Path(__file__).resolve().parent / f'hull_orbits{t}.json').write_text(json.dumps(results,indent=2))
for t in map(int,sys.argv[1:]):run(t)
