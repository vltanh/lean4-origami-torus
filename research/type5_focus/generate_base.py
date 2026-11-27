#!/usr/bin/env python3
"""Generate low-degree, exact, degeneracy-complete SMT systems at the hexagonal metric.
Usage: python generate.py CASES_JSON LUTZ_FACES_JSON OUTPUT_DIR
Only the four hexagonal marking representatives are selected. Coordinates are
scaled so that the squared norm is X^2+3Y^2+Z^2. No algebraic coefficients.
"""
import json, sys
from pathlib import Path
from itertools import combinations, permutations

def op(f,*a): return '('+f+' '+' '.join(a)+')'
def add(*a): return '0' if not a else a[0] if len(a)==1 else op('+',*a)
def mul(*a): return '1' if not a else a[0] if len(a)==1 else op('*',*a)
def neg(a):return op('-',a)
def sub(a,b):return op('-',a,b)
def num(n):return str(n) if n>=0 else neg(str(-n))
def rat(n,d):return op('/',num(n),num(d))
def all_(a):return 'true' if not a else a[0] if len(a)==1 else op('and',*a)
def any_(a):return 'false' if not a else a[0] if len(a)==1 else op('or',*a)
def determinant(M):
 n=len(M);return add(*(neg(mul(*(M[i][p[i]] for i in range(n)))) if sum(p[i]>p[j] for i in range(n) for j in range(i+1,n))%2 else mul(*(M[i][p[i]] for i in range(n))) for p in permutations(range(n))))

def generate(case,faces):
 f=[tuple(map(int,t)) for t in faces.split()];edges=sorted({tuple(sorted(e)) for t in f for e in combinations(t,2)})
 K={tuple(v['edge']):tuple(v['shift']) for v in case['edge_shifts']};K.update({(b,a):tuple(-x for x in z) for (a,b),z in list(K.items())});assert set(K)=={e for a,b in edges for e in ((a,b),(b,a))}
 anchor=f[0];v0=anchor[0];g={i:(0,0) for i in range(8)}
 for i in anchor[1:]:g[i]=K[v0,i]
 K={e:tuple(z[i]+g[e[0]][i]-g[e[1]][i] for i in range(2)) for e,z in K.items()}
 assert all(K[v0,i]==(0,0) for i in anchor[1:])
 assert all(tuple(sum(K[e][i] for e in ((a,b),(b,c),(c,a))) for i in range(2))==(0,0) for a,b,c in f)
 lines=['(set-logic QF_NRA)','; Exact fixed hexagonal metric. Squared norm in scaled coordinates: X^2+3Y^2+Z^2.']
 def decl(a):lines.append(f'(declare-fun {a} () Real)');return a
 def define(a,b):lines.append(f'(define-fun {a} () Real {b})');return a
 def assertion(a):lines.append(op('assert',a))
 p={i:['0','0'] if i==v0 else [decl(f'p{i}{k}') for k in range(2)] for i in range(8)}
 r={i:p[i]+['0'] if i in anchor else [decl(f'r{i}{k}') for k in range(3)] for i in range(8)}
 def direction(i,j):
  a,b=K[i,j];return [add(sub(p[j][0],p[i][0]),rat(2*a+b,2)),add(sub(p[j][1],p[i][1]),rat(b,2))]
 def norm(v):return add(mul(v[0],v[0]),mul('3',v[1],v[1]),*( [mul(v[2],v[2])] if len(v)==3 else []))
 for i,j in edges:
  u=[define(f'u{i}{j}{k}',z) for k,z in enumerate(direction(i,j))];v=[sub(r[j][k],r[i][k]) for k in range(3)]
  if not {i,j}<=set(anchor):assertion(op('=',norm(u),norm(v)))
  # Strict nearest-image constraints at hexagonal lattice.
  for a,b in [(1,0),(0,1),(-1,1)]:
   expr=add(mul(num(2*a+b),u[0]),mul(num(3*b),u[1]));assertion(all_([op('<',expr,'1'),op('>',expr,'(- 1)')]))
 # Every pair of points satisfies the global metric contraction inequality.
 # At the hexagonal lattice the squared covering radius is 1/3.
 for i,j in combinations(range(8),2):
  v=[sub(r[j][k],r[i][k]) for k in range(3)];d=define(f'D{i}{j}',norm(v));assertion(op('<=',d,'(/ 1 3)'))
  if (i,j) in edges:continue
  # Any lattice shift gives a valid intrinsic competitor, so all such
  # inequalities are necessary. A small finite subset is a useful tightening.
  for a in range(-2,3):
   for b in range(-2,3):
    u=[add(sub(p[j][0],p[i][0]),rat(2*a+b,2)),add(sub(p[j][1],p[i][1]),rat(b,2))]
    assertion(op('<=',d,norm(u)))
 # Consistent orientation and degree one of intrinsic PL triangulation.
 areas=[]
 for i,(a,b,c) in enumerate(f):
  u,v=direction(a,b),direction(a,c);areas.append(define(f'A{i}',sub(mul(u[0],v[1]),mul(u[1],v[0]))))
 # Lattice area is 1/2 in scaled coordinates, so |sum double areas|=1.
 assertion(any_([all_([op('>',a,'0') for a in areas]+[op('=',add(*areas),'1')]),all_([op('<',a,'0') for a in areas]+[op('=',add(*areas),'(- 1)')])]))
 # All simplex intersections (including coplanarity and collinearity): forbid every
 # sign-compatible minimal affine dependence supported on disjoint simplices.
 simplex={tuple([i]) for i in range(8)}|set(edges)|{tuple(sorted(t)) for t in f}
 minors={}
 def minor(S,axes):
  key=(S,axes)
  if key not in minors:
   a,*rest=S
   # determinant of affine coordinate differences; degree <=3
   M=[[sub(r[b][k],r[a][k]) for k in axes] for b in rest]
   minors[key]=define('d'+''.join(map(str,S))+'c'+''.join(map(str,axes)),determinant(M))
  return minors[key]
 counts={}
 for n in range(2,6):
  count=0
  for S in combinations(range(8),n):
   parts=[]
   for k in range(1,min(3,n-1)+1):
    for A in combinations(S,k):
     if S[0] not in A:continue
     B=tuple(v for v in S if v not in A)
     if A in simplex and B in simplex:parts.append(A)
   if not parts:continue
   if n==2:
    assertion(any_([op('distinct',r[S[0]][k],r[S[1]][k]) for k in range(3)]));count+=1;continue
   # rank of augmented points <=n-1 (automatic when n=5).
   rank=all_([op('=',minor(S,axes),'0') for axes in combinations(range(3),n-1)]) if n<=4 else 'true'
   for A in parts:
    tests=[]
    for axes in combinations(range(3),n-2):
     coeff=[minor(S[:i]+S[i+1:],axes) for i in range(n)]
     signed=[c if ((i%2==0)==(v in A)) else neg(c) for i,(c,v) in enumerate(zip(coeff,S))]
     tests.append(any_([all_([op('>',v,'0') for v in signed]),all_([op('<',v,'0') for v in signed])]))
    assertion(op('not',all_([rank,any_(tests)])));count+=1
  counts[n]=count
 lines.append('(check-sat)');return '\n'.join(lines)+'\n',counts

def main():
 cases=json.loads(Path(sys.argv[1]).read_text());faces=json.loads(Path(sys.argv[2]).read_text());out=Path(sys.argv[3]);out.mkdir(parents=True,exist_ok=True)
 counts={4:0,5:0,7:0}
 for c in cases:
  t=c['type'];
  if not c['sharp'] or counts[t]>=(2 if t==7 else 1):continue
  counts[t]+=1;s,n=generate(c,faces[str(t)]);name=f't{t}_hex_{counts[t]}.smt2';(out/name).write_text(s);print(name,len(s),'bytes',n,flush=True)
 assert counts=={4:1,5:1,7:2}
if __name__=='__main__':main()
