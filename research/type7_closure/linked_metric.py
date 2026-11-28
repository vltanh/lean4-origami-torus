#!/usr/bin/env python3
"""Generate one degeneracy-complete Type 7 ray_3 metric/embedding system,
with necessary generic sign completion and |long-ring linking|=2.
Usage: python linked_metric.py OUTPUT [Y [TIMEOUT_MS]]
The generate() API also supports localized ray-1/2 masks, retaining both
possible nonzero long-ring linking magnitudes; its default is unchanged.
The optional solver run is an experiment, not a certificate unless its
result is independently validated. Output files should be in scratch.
"""
import importlib.util,sys,json
from pathlib import Path
from fractions import Fraction as F
from itertools import combinations
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'linking_checkpoint'))
from verify_linking import CNF,formula,data,short_pairs,lit
sp=importlib.util.spec_from_file_location('remaining',ROOT/'type7_focus/generate_remaining.py')
m=importlib.util.module_from_spec(sp);sp.loader.exec_module(m)
op,add,mul,sub,neg,det,all_,any_=m.op,m.add,m.mul,m.sub,m.neg,m.det,m.all_,m.any_

def generate(y,mark=3,mask='phase0'):
 assert mark in (1,2,3)
 assert y>=4 if mark==3 else y>=10**6
 assert mask=='phase0' if mark==3 else mask in m.MASKS
 m.Y=y;m.W=y*y;m.t=F(1,y*y)
 case=next(c for c in json.loads((ROOT/'linking_checkpoint/cases.json').read_text()) if c['file']==f't7_ray_{mark}.smt2')
 faces=[tuple(map(int,f)) for f in json.loads((ROOT/'linking_checkpoint/lutz_faces.json').read_text())['7'].split()]
 K,_,_=data(case)
 L=m.gen(mark,K,faces,mask).removesuffix('(check-sat)\n').splitlines()
 def define(a,b):L.append(f'(define-fun {a} () Real {b})');return a
 def require(a):L.append(op('assert',a))
 # Inner-product coordinates are the image of the unique rank-three
 # realization under a nonsingular map. Their determinant orientation is
 # normalized by anchor 0123, which has determinant det(G)>0.
 U={0:['0']*3}
 for i in range(1,8):U[i]=[f'G{min(i,j)}{max(i,j)}' for j in (1,2,3)]
 minors={}
 def minor(S,axes):
  key=(tuple(S),tuple(axes))
  if key not in minors:
   a,*rest=S
   minors[key]=define('a'+''.join(map(str,S))+'c'+''.join(map(str,axes)),det([[sub(U[b][k],U[a][k]) for k in axes] for b in rest]))
  return minors[key]
 n,clauses,tri,edges,_=formula(7)
 extra=CNF(n)
 for a,b in short_pairs(K):extra.unlink(a,b)
 clauses+=extra.C
 for i in range(1,extra.n+1):L.append(f'(declare-fun b{i} () Bool)')
 def bool_lit(i):return f'b{i}' if i>0 else op('not',f'b{-i}')
 for C in clauses:require(any_([bool_lit(i) for i in C]))
 for i,S in enumerate(combinations(range(8),4),1):
  d=minor(S,(0,1,2))
  # Actual nonclique minors may vanish. A generic perturbation supplies
  # these Boolean signs without changing the necessary topological data.
  require(op('ite',f'b{i}',op('>=',d,'0'),op('<=',d,'0')))
 # Algebraic intersection of the second long ring with a triangular fan
 # of the first, evaluated only on the generic Boolean sign completion.
 A=(0,2,4,6);B=(1,3,5,7);terms=[]
 for k in range(1,len(A)-1):
  T=(A[0],A[k],A[k+1])
  for u,v in zip(B,B[1:]+B[:1]):
   S=tuple(sorted(T+(u,v)))
   C=[(1 if w in T else -1)*(-1)**j*lit(S[:j]+S[j+1:]) for j,w in enumerate(S)]
   terminal=lit(T+(v,))
   assert (terminal in C)!=(-terminal in C)
   if terminal not in C:C=[-c for c in C]
   terms.extend([op('ite',all_([bool_lit(c) for c in C]),'1.0','0.0'),
                 neg(op('ite',all_([bool_lit(-c) for c in C]),'1.0','0.0'))])
 lk=define('long_link',add(*terms))
 # The audited alternating-ring theorem forces nonzero linking in every
 # marking. For ray 3 the linking form strengthens this to magnitude two.
 # Rays 1/2 have not been proved to have magnitude one; retain both.
 magnitudes=(2,) if mark==3 else (1,2)
 require(any_([op('=',lk,v) for k in magnitudes
               for v in (f'{k}.0',f'(- {k}.0)')]))
 # Full minimal affine-circuit tests for disjoint simplices, including
 # nongeneric configurations; distances already exclude coincidences.
 simplex={(i,) for i in range(8)}|edges|set(tri)
 count=0
 for npts in range(3,6):
  for S in combinations(range(8),npts):
   parts=[a for k in range(1,min(3,npts-1)+1) for a in combinations(S,k)
          if S[0] in a and a in simplex and tuple(v for v in S if v not in a) in simplex]
   if not parts:continue
   rank=all_([op('=',minor(S,axes),'0') for axes in combinations(range(3),npts-1)]) if npts<=4 else 'true'
   for a in parts:
    tests=[]
    for axes in combinations(range(3),npts-2):
     vals=[minor(S[:i]+S[i+1:],axes) for i in range(npts)]
     signed=[v if ((i%2==0)==(j in a)) else neg(v) for i,(v,j) in enumerate(zip(vals,S))]
     tests.append(any_([all_([op('>',v,'0') for v in signed]),all_([op('<',v,'0') for v in signed])]))
    require(op('not',all_([rank,any_(tests)])));count+=1
 L.append('(check-sat)')
 return '\n'.join(L)+'\n',dict(y=y,real_variables=18,boolean_variables=extra.n,cnf_clauses=len(clauses),circuit_partitions=count)
if __name__=='__main__':
 y=int(sys.argv[2]) if len(sys.argv)>2 else 10**6
 text,meta=generate(y);Path(sys.argv[1]).write_text(text)
 print(json.dumps(meta),flush=True)
 print('bytes',len(text),flush=True)
 if len(sys.argv)>3:print('solver',m.solve(text,int(sys.argv[3])),flush=True)
