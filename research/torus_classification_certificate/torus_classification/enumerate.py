from itertools import combinations, permutations
import networkx as nx, json
V=range(8)
missing=[list(g.edges()) for g in nx.graph_atlas_g() if g.number_of_edges()==4 and all(g.degree(v)>0 for v in g)]+[[(0,1),(2,3),(4,5),(6,7)]]
reps=[]
for miss in missing:
 E=set(combinations(V,2))-set(miss)
 T=[t for t in combinations(V,3) if set(combinations(t,2))<=E]
 TE={t:set(combinations(t,2)) for t in T}
 sol=[]
 def f(rem, avail, ts):
  if not rem:
   if len(ts)!=16:return
   for v in V:
    adj={w:set() for w in V if tuple(sorted((v,w))) in E}
    for t in ts:
     if v in t:
      a,b=[w for w in t if w!=v];adj[a].add(b);adj[b].add(a)
    seen=set(); stack=[next(iter(adj))]
    while stack:
     x=stack.pop()
     if x not in seen:seen.add(x);stack+=list(adj[x]-seen)
    if len(seen)!=len(adj):return
   # orientability
   orient={ts[0]:1};stack=[ts[0]]
   def sign(t,e):return -1 if (t[0],t[2])==e else 1
   while stack:
    t=stack.pop()
    for e in TE[t]:
     u=next(u for u in ts if u!=t and e in TE[u]);s=-orient[t]*sign(t,e)*sign(u,e)
     if u in orient and orient[u]!=s:return
     if u not in orient:orient[u]=s;stack.append(u)
   sol.append(tuple(sorted(ts)));return
  e=min(rem,key=lambda e:sum(e in TE[t] for t in avail)-rem[e]); choices=[t for t in avail if e in TE[t]]
  for c in combinations(choices,rem[e]):
   n=rem.copy()
   for t in c:
    for a in TE[t]:n[a]-=1
   if min(n.values())<0:continue
   n={a:b for a,b in n.items() if b}
   f(n,[t for t in avail if TE[t]<=n.keys()],ts+list(c))
 f(dict.fromkeys(E,2),T,[])
 aut=[p for p in permutations(V) if {tuple(sorted(p[i] for i in e)) for e in E}==E]
 remaining=set(sol); count=0
 while remaining:
  r=min(remaining); orbit={tuple(sorted(tuple(sorted(p[i] for i in t)) for t in r)) for p in aut}; remaining-=orbit; count+=1
  deg=sorted(sum(v in e for e in E) for v in V); reps.append(dict(degree=''.join(map(str,deg)),faces=r,orbit=len(orbit)))
 print(miss,len(sol),count,flush=True)
json.dump(reps,open('triangulations.json','w'),indent=2)
print([(r['degree'],r['orbit']) for r in reps])
