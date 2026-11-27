#!/usr/bin/env python3
"""Exhaust split height orbit B1; order clique branches by chamber count."""
from pathlib import Path
import sys,json,itertools as it
from collections import defaultdict
P=Path(__file__).resolve().parent
sys.path.insert(0,str(P.parent))
import focused_system as fs
from satgeom import SAT,formula,lit,ids,Q
h=[lit((1,2,5,i)) for i in fs.B];sign=(1,1,-1,-1,-1)
n,C,T,E,N=formula(5)
for i in range(5):
 if i==1: continue
 a,b=h[i]*sign[i],h[1]
 C.extend([[a,-b],[-a,b]])
s=SAT(n,C);groups=defaultdict(list)
while True:
 status=s.check()
 if status==-1:break
 assert status==1,status
 m=s.model();pat=''.join('+' if m[ids[q]-1]>0 else '-' for q in fs.cl)
 groups[pat].append(''.join('+' if z>0 else '-' for z in m));s.add([-v*(i+1) for i,v in enumerate(m)])
assert len(groups)==6 and sum(map(len,groups.values()))==236
# Independent replay of the full orbit archive: expand all six automorphisms.
faces={frozenset(f) for f in fs.F};auts=[p for p in it.permutations(range(8)) if {frozenset(p[i] for i in f) for f in fs.F}==faces];assert len(auts)==6
archive=set()
for pat in json.loads((P.parent/'full_sign_orbits5.json').read_text()):
 m=[1 if x=='+' else -1 for x in pat]
 for p in auts:
  L=[lit(tuple(p[i] for i in q)) for q in Q]
  v=[m[abs(z)-1]*(1 if z>0 else -1) for z in L];v=[x*v[0] for x in v]
  if all(v[abs(z)-1]*(1 if z>0 else -1)*sign[i]==v[abs(h[1])-1]*(1 if h[1]>0 else -1) for i,z in enumerate(h)):
   archive.add(''.join('+' if z>0 else '-' for z in v))
assert archive==set(it.chain.from_iterable(groups.values()))
branches=[dict(id=f'B1.{i+1}',clique_pattern=pat,chambers=sorted(a),status='open') for i,(pat,a) in enumerate(sorted(groups.items(),key=lambda x:(len(x[1]),x[0])))]
(P/'branches.json').write_text(json.dumps(branches,indent=2)+'\n')
for b in branches:print(b['id'],b['clique_pattern'],len(b['chambers']))
print('PASS: SAT enumeration exhausted and matches independently expanded orbit archive, 236 models.')
