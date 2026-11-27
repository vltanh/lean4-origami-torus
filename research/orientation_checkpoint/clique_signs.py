#!/usr/bin/env python3
from satgeom import *
from collections import Counter

def run(t):
 n,C,T,E,N=formula(t);cliques=[q for q in Q if set(it.combinations(q,2))<=E];cl=[ids[q] for q in cliques];s=SAT(n,C);masks=set();cnt=0
 while s.check()==1:
  m=s.model();signs=tuple(m[i-1] for i in cl);signs=tuple(x*signs[0] for x in signs);masks.add(signs)
  for v in [signs,tuple(-x for x in signs)]:s.add([-a*i for a,i in zip(v,cl)])
  cnt+=1
  if cnt%1000==0:print('progress',t,cnt,flush=True)
 print('type',t,'K4s',len(cl),'projected patterns modulo reflection',len(masks),flush=True)
 P=[sum((1<<i) for i,a in enumerate(v) if a>0) for v in masks];full=(1<<len(cl))-1
 # Choose a spanning 3-tree by the 4-subsets it uses, independent of insertion order.
 G={q:set(q) for q in cliques};chains={};ci={q:i for i,q in enumerate(cliques)}
 def dfs(S,used,order):
  if len(S)==8:
   k=tuple(sorted(used));chains.setdefault(k,order);return
  for j in sorted(set(V)-S):
   for A in it.combinations(sorted(N[j]&S),3):
    q=tuple(sorted(A+(j,)))
    if q not in G:continue
    dfs(S|{j},used+(ci[q],),order+[(j,A)])
 for q in cliques:dfs(set(q),(ci[q],),[(q[3],q[:3])])
 # cache projection by 5 clique index set; relative sign normalized to first
 stats=[];best=None
 for k,order in chains.items():
  M=sum(1<<i for i in k);ss={min(v&M,(~v)&M) for v in P};a=len(ss)
  if best is None or a<best[0]:best=(a,k,order,ss)
  stats.append(a)
 print('chains',len(chains),'counts',dict(Counter(stats)),flush=True);a,k,order,ss=best
 print('best',a,'order',order,'cliques',[cliques[i] for i in k],flush=True)
 out={'type':t,'cliques':cliques,'patterns':[''.join('+' if a>0 else '-' for a in v) for v in sorted(masks)],'best_tree':order,'best_tree_cliques':[cliques[i] for i in k],'best_tree_signs':[''.join('+' if m&(1<<i) else '-' for i in k) for m in sorted(ss)]}
 (Path(__file__).resolve().parent / f'clique_signs{t}.json').write_text(json.dumps(out,indent=2))
for t in map(int,sys.argv[1:]):run(t)
