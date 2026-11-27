from itertools import combinations,product
V=range(8);Q=list(combinations(V,4)); ids={q:i+1 for i,q in enumerate(Q)}
T=((0,4,6),(0,4,7),(0,5,6),(0,5,7),(1,3,5),(1,3,6),(1,4,5),(1,4,7),(1,6,7),(2,3,4),(2,3,7),(2,4,5),(2,5,6),(2,6,7),(3,4,6),(3,5,7))
E={e for t in T for e in combinations(t,2)}; N={i:{j for j in V if tuple(sorted((i,j))) in E} for i in V}
def lit(q):return ids[tuple(sorted(q))]*(-1)**sum(a>b for i,a in enumerate(q) for b in q[i+1:])
clauses=[[1]]
for s in combinations(V,2):
 for a,b,c,d in combinations(sorted(set(V)-set(s)),4):
  L=[lit((*s,a,b)),lit((*s,c,d)),-lit((*s,a,c)),lit((*s,b,d)),lit((*s,a,d)),lit((*s,b,c))]
  for B in product([-1,1],repeat=6):
   if B[0]*B[1]==B[2]*B[3]==B[4]*B[5]:clauses.append([-x*y for x,y in zip(L,B)])
for C in combinations(V,5):
 s=[(-1)**i*lit(C[:i]+C[i+1:]) for i in range(5)]
 clauses.extend([s,[-x for x in s]])
 def forbid(A):
  L=[x if v in A else -x for x,v in zip(s,C)];clauses.extend([L,[-x for x in L]])
 for A in combinations(C,2):
  if A in E and tuple(v for v in C if v not in A) in T:forbid(A)
 for v in C:
  if set(C)-{v}<=N[v]:forbid({v})
nvar=70
for v in (0,1,2):
 ms=[]
 for t in T:
  if v in t:
   nvar+=1;ms.append(nvar);D=[lit((*t,w)) for w in sorted(N[v]-set(t))];clauses.extend([[-nvar]+D,[-nvar]+[-d for d in D]])
 clauses.append(ms)
print(nvar,len(clauses))
from pathlib import Path
with open(Path(__file__).with_name('torus.cnf'),'w') as f:
 print('p cnf',nvar,len(clauses),file=f)
 for c in clauses:print(*c,0,file=f)
