#!/usr/bin/env python3
"""Exact Boolean and planar line-order obstruction for Type 7 caps
0145 and 2367. No numerical geometry, no archived orientation models.
Requires Python 3 and shared libz3.
"""
from pathlib import Path
import sys
sys.path.insert(0,str(Path(__file__).resolve().parent.parent/'linking_checkpoint'))
from verify_linking import *
A=(0,1,4,5); B=(2,3,6,7)
R=lambda a:list(zip(a,a[1:]+a[:1]))
n,C,T,E,N=formula(7)
assert all(tuple(sorted(e)) in E for P in (A,B) for e in R(P))
assert all(tuple(sorted(e)) in E for e in it.product(A,B))
extra=CNF(n)
# Only this pair needs zero linking; no aspect ratio premise in this step.
extra.unlink(A,B)
C=C+extra.C
for P,S in ((A,B),(B,A)):
 for tri in it.combinations(P,3):
  s=lit(tri+(S[0],))
  for j in S[1:]:
   u=lit(tri+(j,));C.extend([[-s,u],[s,-u]])
assert extra.n==215 and len(C)==7818
print('vars',extra.n,'clauses',len(C),flush=True)
sol=SAT(extra.n,C);models=[]
while True:
 result=sol.check()
 if result==-1:break
 assert result==1
 m=sol.model()
 models.append(''.join('+' if x==1 else '-' for x in m))
 sol.add([-x*(i+1) for i,x in enumerate(m)])
 # For heights 0 and 1, mixed tetrahedron signs are minus the
 # planar cross products of the two directed edge vectors.
 signs=[(i,4+j,-sign_lit((a,b,c,d),m))
        for i,(a,b) in enumerate(R(A)) for j,(c,d) in enumerate(R(B))]
 for k,P,S,sg in ((0,A,B,1),(4,B,A,-1)):
  for i in range(4):
   a,b,c=(P[(i+j)%4] for j in range(3))
   signs.append((k+i,k+(i+1)%4,sg*sign_lit((a,b,c,S[0]),m)))
 # Write each nonzero planar vector as a signed positive multiple
 # of a unit vector with angle in a common interval of length pi.
 # The sign of a cross product then determines the strict order
 # of the two angles, possibly reversed by their two signs.
 # Global reversal of all eight vectors changes no cross products.
 for z0 in it.product((-1,1),repeat=7):
  z=(1,)+z0;graph={i:set() for i in V}
  for i,j,s in signs:
   if z[i]*z[j]*s<0:i,j=j,i
   graph[i].add(j)
  left=set(V)
  while left:
   rem={i for i in left if not (graph[i]&left)}
   if not rem:break
   left-=rem
  assert left,(models[-1],z)
assert len(models)==len(set(models))==16
print('PASS complete Boolean enumeration: 16 models, every one of 128 signed line orders cyclic')

# Export the exact blocked formula for the independent exhaustive DPLL
# checker already in orientation_checkpoint/check_unsat.cpp.
if len(sys.argv)>1:
 D=C+[[-(i+1)*(1 if x=='+' else -1) for i,x in enumerate(m)] for m in sorted(models)]
 assert len(D)==7834
 Path(sys.argv[1]).write_text(f'p cnf {extra.n} {len(D)}\n'+''.join(' '.join(map(str,row))+' 0\n' for row in D))
 print('exported blocked CNF:',extra.n,len(D))
