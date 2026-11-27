from itertools import combinations, permutations
from collections import Counter
V=range(8); E=set(combinations(V,2))-{(0,1),(0,2),(0,3),(1,2)}
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
print(len(sol)); print(sol[0]);print('automorphism group',sum({tuple(sorted(p[i] for i in t)) for t in sol[0]}==set(sol[0]) for p in permutations(V)))

representative=sol[0]
orbit={tuple(sorted(tuple(sorted(p[i] for i in t)) for t in representative)) for p in permutations(V) if {tuple(sorted(p[i] for i in e)) for e in E}==E}
assert set(sol)==orbit
print("All enumerated triangulations form one orbit of size",len(orbit))
