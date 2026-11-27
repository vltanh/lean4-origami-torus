#!/usr/bin/env python3
"""Type 5 at hexagonal modulus, split into the two height-sign representatives.
The algebraic metric equations are written as inner-product identities after
using the universal vertex as origin; this exposes the three independent
linear systems for the leaves. No numerical results are assumed.
"""
import json
from pathlib import Path
from itertools import combinations, permutations
from generate_base import op,add,mul,neg,sub,num,rat,all_,any_,determinant
P=Path(__file__).resolve().parent
case=next(c for c in json.loads((P/'cases.json').read_text()) if c['type']==5 and c['sharp'])
F=[tuple(map(int,t)) for t in json.loads((P/'lutz_faces.json').read_text())['5'].split()];E=sorted({tuple(sorted(e)) for f in F for e in combinations(f,2)})
K={tuple(v['edge']):tuple(v['shift']) for v in case['edge_shifts']};K.update({(b,a):tuple(-x for x in z) for (a,b),z in list(K.items())})
g={i:K[1,i] if i!=1 else (0,0) for i in range(8)};K={e:tuple(z[i]+g[e[0]][i]-g[e[1]][i] for i in range(2)) for e,z in K.items()}
A=[1,2,5];R=[3,4];L=[0,6,7];B=[0,3,4,6,7];assert all(K[1,i]==(0,0) for i in range(8) if i!=1)
assert all(K[e]==(0,0) for e in combinations(A,2))
D=json.loads((P/'clique_signs5.json').read_text());cl=[tuple(q) for q in D['cliques']]

def generate(branch, full=True, projection=True):
 lines=['(set-logic QF_NRA)','; Type 5, hexagonal torus, anchor 125.']
 def decl(a):lines.append(f'(declare-fun {a} () Real)');return a
 def define(a,b):lines.append(f'(define-fun {a} () Real {b})');return a
 def assertion(a):lines.append(op('assert',a))
 p={i:['0','0'] if i==1 else [decl(f'p{i}{k}') for k in range(2)] for i in range(8)}
 r={i:p[i]+['0'] if i in A else [decl(f'r{i}{k}') for k in range(3)] for i in range(8)}
 def diff(u,v):return [sub(a,b) for a,b in zip(u,v)]
 def dot(u,v):return add(mul(u[0],v[0]),mul('3',u[1],v[1]),*([mul(u[2],v[2])] if len(u)==3 and len(v)==3 else []))
 def norm(u):return dot(u,u)
 def phys(a,b):return [rat(2*a+b,2),rat(b,2)]
 def direction(i,j):return [add(v,w) for v,w in zip(diff(p[j],p[i]),phys(*K[i,j]))]
 def cross(u,v):return sub(mul(u[0],v[1]),mul(u[1],v[0]))
 # Anchor is universal, so the five norm equations fix the diagonal of the metric Gram matrix.
 for j in B:assertion(op('=',norm(r[j]),norm(p[j])))
 # The slack matrix is linear in intrinsic positions. Off-diagonal equations
 # involving a leaf are linear in that leaf's five coordinates for fixed core.
 for i,j in E:
  if i!=1 and j!=1 and not ({i,j}<=set(A)):
   k=phys(*K[i,j]);s=sub(neg(dot(diff(p[j],p[i]),k)),mul('(/ 1 2)',norm(k)))
   assertion(op('=',dot(r[i],r[j]),add(dot(p[i],p[j]),s)))
  u=direction(i,j)
  for a,b in [(1,0),(0,1),(-1,1)]:
   expr=add(mul(num(2*a+b),u[0]),mul(num(3*b),u[1]));assertion(all_([op('<',expr,'1'),op('>',expr,'(- 1)')]))
 for i,j in combinations(range(8),2):
  v=diff(r[j],r[i]);d=define(f'D{i}{j}',norm(v));assertion(op('<=',d,'(/ 1 3)'))
  if (i,j) in E:continue
  for a in range(-1,2):
   for b in range(-1,2):
    u=[add(z,k) for z,k in zip(diff(p[j],p[i]),phys(a,b))];assertion(op('<=',d,norm(u)))
 areas=[define(f'A{i}',cross(direction(a,b),direction(a,c))) for i,(a,b,c) in enumerate(F)]
 assertion(any_([all_([op('>',a,'0') for a in areas]+[op('=',add(*areas),'1')]),all_([op('<',a,'0') for a in areas]+[op('=',add(*areas),'(- 1)')])]))
 # Reflection fixes r3_z > 0. The two representatives cover all height patterns
 # by the hexagonal lattice symmetries and six automorphisms of Type 5.
 for j,sg in zip(B,branch):assertion(op('>' if sg==1 else '<',r[j][2],'0'))
 # K4 determinants and the exact Boolean projection. Normalization is modulo ambient reflection.
 minors={}
 def minor(S,axes):
  key=(S,axes)
  if key not in minors:
   a,*rest=S;M=[[sub(r[b][k],r[a][k]) for k in axes] for b in rest]
   minors[key]=define('d'+''.join(map(str,S))+'c'+''.join(map(str,axes)),determinant(M))
  return minors[key]
 v=[minor(q,(0,1,2)) for q in cl]
 # Retain only the projected patterns compatible with the selected height signs.
 def parity(q):return (-1)**sum(a>b for i,a in enumerate(q) for b in q[i+1:])
 # The determinant ordering (1,2,5,j) gives sign(d(anchor)) times sign(z_j).
 # A sign of d(anchor) can be either one; reflection is not quotiented twice.
 hp=[cl.index(tuple(sorted((1,2,5,i)))) for i in B];hs=[parity((1,2,5,i)) for i in B]
 good=[]
 for pat in D['patterns']:
  pat=[1 if x=='+' else -1 for x in pat];h=[pat[i]*s for i,s in zip(hp,hs)]
  if tuple(x*h[1] for x in h)==branch:
   good.extend([pat,[-x for x in pat]])
 assert good
 assertion(any_([all_([op('>' if s==1 else '<',z,'0') for z,s in zip(v,pat)]) for pat in good]))
 if projection:
  from projection_cycles import forbidden_cycles
  C,cycles=forbidden_cycles(F,E)
  def opposite(a,b):return any_([all_([op('>',a,'0'),op('<',b,'0')]),all_([op('<',a,'0'),op('>',b,'0')])])
  def orient(i,j,k):return cross(diff(r[j][:2],r[i][:2]),diff(r[k][:2],r[i][:2]))
  cs=[]
  for ix,((i,j),(k,l)) in enumerate(C):
   v=all_([opposite(orient(i,j,k),orient(i,j,l)),opposite(orient(k,l,i),orient(k,l,j))])
   name=f'crossing{ix}';lines.append(f'(define-fun {name} () Bool {v})');cs.append(name)
  for cyc in cycles:assertion(op('not',all_([cs[i] for i in cyc])))
 if full:
  # Exact intersection exclusions with affine circuits, including coplanar cases.
  simplex={(i,) for i in range(8)}|set(E)|{tuple(sorted(f)) for f in F}
  for n in range(2,6):
   for S in combinations(range(8),n):
    parts=[]
    for k in range(1,min(3,n-1)+1):
     for A0 in combinations(S,k):
      if S[0] not in A0:continue
      B0=tuple(i for i in S if i not in A0)
      if A0 in simplex and B0 in simplex:parts.append(A0)
    if not parts:continue
    if n==2:
     assertion(any_([op('distinct',r[S[0]][k],r[S[1]][k]) for k in range(3)]));continue
    rank=all_([op('=',minor(S,axes),'0') for axes in combinations(range(3),n-1)]) if n<=4 else 'true'
    for A0 in parts:
     tests=[]
     for axes in combinations(range(3),n-2):
      coeff=[minor(S[:i]+S[i+1:],axes) for i in range(n)]
      signed=[c if ((i%2==0)==(w in A0)) else neg(c) for i,(c,w) in enumerate(zip(coeff,S))]
      tests.append(any_([all_([op('>',z,'0') for z in signed]),all_([op('<',z,'0') for z in signed])]))
     assertion(op('not',all_([rank,any_(tests)])))
 lines.append('(check-sat)')
 return '\n'.join(lines)+'\n',len(good)//2
if __name__=='__main__':
 out=P/'systems';out.mkdir(exist_ok=True)
 for name,h in [('one_side',(1,1,1,1,1)),('split_side',(1,1,-1,-1,-1))]:
  s,n=generate(h);(out/(name+'.smt2')).write_text(s);print(name,'clique patterns up to reflection',n,'bytes',len(s))
