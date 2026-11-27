from satgeom import *
from collections import Counter

def run(t):
 n,C,T,E,N=formula(t);T=set(T);aut=[p for p in it.permutations(V) if {tuple(sorted(p[i] for i in f)) for f in T}==T];maps=[[(abs(lit(tuple(p[i] for i in q)))-1,1 if lit(tuple(p[i] for i in q))>0 else -1) for q in Q] for p in aut];s=SAT(n,C);out=[];count=0
 while s.check()==1:
  m=s.model();orb=set()
  for M in maps:
   a=tuple(m[i]*v for i,v in M);a=tuple(v*a[0] for v in a);orb.add(a)
  count+=len(orb);out.append(min(orb))
  for a in orb:s.add([-v*(i+1) for i,v in enumerate(a)])
  if len(out)%100==0:print('type',t,len(out),'labelled',count,flush=True)
 assert s.check()==-1
 print('DONE',t,len(out),'labelled',count,flush=True)
 (Path(__file__).resolve().parent / f'full_sign_orbits{t}.json').write_text(json.dumps([''.join('+' if a>0 else '-' for a in p) for p in out]))
for t in map(int,sys.argv[1:]):run(t)
