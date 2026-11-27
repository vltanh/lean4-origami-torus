from satgeom import *
from collections import Counter
for t in (4,5,7):
 z=json.loads((Path(__file__).resolve().parent / f'clique_signs{t}.json').read_text());cl=[tuple(q) for q in z['cliques']];ci={q:i for i,q in enumerate(cl)};P=[sum(1<<i for i,s in enumerate(v) if s=='+') for v in z['patterns']];chains={}
 def dfs(S,edges,used,order):
  if len(S)==8:
   k=tuple(sorted(used));chains.setdefault(k,order);return
  for j in sorted(set(V)-S):
   for A in it.combinations(sorted(S),3):
    q=tuple(sorted(A+(j,)))
    if q not in ci or not set(it.combinations(A,2))<=edges:continue
    dfs(S|{j},edges|{tuple(sorted((a,j))) for a in A},used+(ci[q],),order+[(j,A)])
 for q in cl:dfs(set(q),set(it.combinations(q,2)),(ci[q],),[(q[3],q[:3])])
 best=None;stats=[]
 for k,order in chains.items():
  M=sum(1<<i for i in k);ss={min(v&M,(~v)&M) for v in P};a=len(ss)
  if best is None or a<best[0]:best=(a,k,order,ss)
  stats.append(a)
 print(t,'true 3-trees',len(chains),'counts',dict(Counter(stats)),'best',best[:3],flush=True)
 a,k,order,ss=best;z.update(true_tree=order,true_tree_cliques=[cl[i] for i in k],true_tree_signs=[''.join('+' if m&(1<<i) else '-' for i in k) for m in sorted(ss)]);(Path(__file__).resolve().parent / f'clique_signs{t}.json').write_text(json.dumps(z,indent=2))
