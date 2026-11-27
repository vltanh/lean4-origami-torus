"""Enumerate winding markings and emit exact semialgebraic feasibility queries.
Requires Python and SymPy, no solver needed to generate. A query is for a fixed
metric when w (and x if needed) is constrained, or tests existence for any metric
in the stated region otherwise. Universality itself requires forall parameters.
"""
import itertools as it,json,sys
from pathlib import Path
from homology import F,hdata,edge,s
ROOT=Path(__file__).parent
V0=[(-1,0),(1,0),(0,1),(0,-1),(-1,1),(1,-1)]
V1=V0+[(1,1),(-1,-1)]
def markings(typ,sharp):
 f=F[typ];E,T,C,H,basis=hdata(f);idx={e:i for i,e in enumerate(E)};fs={tuple(sorted(t)) for t in f};V=V0 if sharp else V1
 mats={tuple(a+b) for a,b in it.product(V,repeat=2) if abs(s.det(s.Matrix([a,b])))==1 and all(tuple(s.Matrix([u])*s.Matrix([a,b])) in V for u in H.values())};acts=set();autos=0
 for p in it.permutations(range(8)):
  if {tuple(sorted(p[i] for i in t)) for t in f}!=fs:continue
  autos+=1;rows=[]
  for cyc in basis:
   cyc=tuple(p[i] for i in cyc);v=s.zeros(1,2)
   for a,b in zip(cyc,cyc[1:]+cyc[:1]):v+=(1 if a<b else -1)*C[idx[edge(a,b)],:]
   rows.append(list(v))
  A=s.Matrix(rows);assert abs(A.det())==1;acts.add(tuple(A))
 B=[s.eye(2),-s.eye(2)]
 if sharp:B += [s.Matrix([[-1,0],[-1,1]]),s.Matrix([[1,0],[1,-1]])]
 remain=set(mats);orbits=[]
 while remain:
  m=min(remain);M=s.Matrix(2,2,m);orb={tuple(s.Matrix(2,2,a)*M*b) for a in acts for b in B};assert orb<=mats;remain-=orb;orbits.append((M,len(orb)))
 print('type',typ,'sharp' if sharp else 'interior','automorphisms',autos,'homology actions',len(acts),'markings',len(mats),'orbits',[(tuple(M),n) for M,n in orbits],flush=True)
 return E,T,C,H,basis,orbits

def smt(typ,sharp,E,C,M):
 # Scalar SMT-LIB expressions. Each named definition is a polynomial in the
 # 18 geometric variables and the modulus parameter(s), with rational constants.
 def add(*a):return '0' if not a else a[0] if len(a)==1 else '(+ '+' '.join(a)+')'
 def mul(*a):return '1' if not a else a[0] if len(a)==1 else '(* '+' '.join(a)+')'
 def neg(a):return '(- '+a+')'
 def sub(a,b):return add(a,neg(b))
 def num(n):return str(n) if n>=0 else neg(str(-n))
 def op(k,*a):return '('+k+' '+' '.join(a)+')'
 def conj(a):return 'true' if not a else a[0] if len(a)==1 else op('and',*a)
 def disj(a):return 'false' if not a else a[0] if len(a)==1 else op('or',*a)
 out=['(set-logic QF_NRA)','; Realizability at a specified reduced modulus.','; Add (assert (= w ...)) and, for interior, (assert (= x ...)) before check-sat to fix the target.']
 def decl(a):out.append(f'(declare-fun {a} () Real)');return a
 def define(a,b):out.append(f'(define-fun {a} () Real {b})');return a
 def assertion(b):out.append(f'(assert {b})')
 w=decl('w');x='(/ 1 2)' if sharp else decl('x')
 if not sharp:assertion(conj([op('>=',x,'0'),op('<',x,'(/ 1 2)')]))
 assertion(op('>=',add(mul(x,x),w),'1'))
 a=['0']+[decl(f'a{i}') for i in range(1,8)];b=['0']+[decl(f'b{i}') for i in range(1,8)];K=C*M;idx={e:i for i,e in enumerate(E)}
 def direction(i,j):
  k=K[idx[edge(i,j)],:];sg=1 if i<j else -1
  return [add(sub(a[j],a[i]),num(int(sg*k[0]))),add(sub(b[j],b[i]),num(int(sg*k[1])))]
 D={};U={}
 for i,j in it.combinations(range(8),2):
  if (i,j) in idx:
   u,v=direction(i,j);u=define(f'u{i}{j}',u);v=define(f'v{i}{j}',v);U[i,j]=(u,v)
   dx=define(f'dx{i}{j}',add(u,mul(x,v)))
   D[i,j]=define(f'd{i}{j}',add(mul(dx,dx),mul(w,v,v)))
   # Unique shortest edge, necessary for any embedded isometry. These three
   # lattice-vector inequalities suffice for our winding bound; they need not
   # be sufficient for shortestness, since exact embedding is checked below.
   for z,k in [(dx,'1'),(add(mul(x,dx),mul(w,v)),add(mul(x,x),w)),(add(mul(sub(x,'1'),dx),mul(w,v)),add(mul(sub(x,'1'),sub(x,'1')),w))]:
    assertion(conj([op('<',mul('2',z),k),op('>',mul('2',z),neg(k))]))
  else:
   D[i,j]=decl(f'd{i}{j}');assertion(op('>',D[i,j],'0'))
 def d(i,j):return '0' if i==j else D[edge(i,j)]
 # Intrinsic orientation. All faces have the same sign; determinant of marking
 # is +/-1, hence the intrinsic PL map to the target torus has degree +/-1.
 fs=F[typ];area=[]
 for k,(i,j,l) in enumerate(fs):
  u,v=direction(i,j);r,z=direction(i,l);area.append(define(f'ar{k}',sub(mul(u,z),mul(v,r))))
 assertion(disj([conj([op('>',z,'0') for z in area]),conj([op('<',z,'0') for z in area])]))
 # Extrinsic centered Gram matrix, and augmented affine Gram matrix.
 G={};B={}
 for i in range(8):
  for j in range(i,8):
   G[i,j]=G[j,i]='0' if i==0 else define(f'g{i}{j}',mul('(/ 1 2)',sub(add(d(0,i),d(0,j)),d(i,j))))
   B[i,j]=B[j,i]=define(f'B{i}{j}',add('1',G[i,j]))
 def determinant(mat,rows,cols):
  if len(rows)==0:return '1'
  if len(rows)==1:return mat[rows[0],cols[0]]
  terms=[]
  for k,j in enumerate(cols):
   z=mul(mat[rows[0],j],determinant(mat,rows[1:],cols[:k]+cols[k+1:]));terms.append(neg(z) if k%2 else z)
  return add(*terms)
 # Use one face at 0 for a 2x2 Gram pivot, extend it by one of five possible
 # third vectors. Positive definite pivot + zero Schur complement gives PSD rank 3.
 face=next(f for f in fs if 0 in f);i,j=sorted(set(face)-{0});branches=[]
 for k in range(1,8):
  if k in (i,j):continue
  p=(i,j,k);det=define(f'gp{k}',determinant(G,p,p));conditions=[op('>',G[i,i],'0'),op('>',determinant(G,p[:2],p[:2]),'0'),op('>',det,'0')]
  r=[v for v in range(1,8) if v not in p]
  for v,l in it.combinations_with_replacement(r,2):conditions.append(op('=',determinant(G,p+(v,),p+(l,)),'0'))
  branches.append(conj(conditions))
 assertion(disj(branches))
 # Minimal affine circuits. For each disjoint simplicial pair of total size
 # <=5, forbid a minimal dependence with that sign partition. Handles zeros.
 simplices={tuple(sorted(c)) for f in fs for n in range(1,4) for c in it.combinations(f,n)}
 pairs=[]
 for A,Bb in it.combinations(sorted(simplices),2):
  if set(A)&set(Bb) or len(A)+len(Bb)>5:continue
  pairs.append((A,Bb))
 subsets=sorted({tuple(sorted(A+Bb)) for A,Bb in pairs});minors={}
 for S in sorted({T for S in subsets for T in [S]+[S[:i]+S[i+1:] for i in range(len(S))]}):
  minors[S]=define('p'+''.join(map(str,S)),determinant(B,S,S))
 cof={}
 for S in subsets:
  for j in range(1,len(S)):
   # adjugate_{0j} = signed minor delete row j and col 0
   z=determinant(B,S[:j]+S[j+1:],S[1:]);cof[S,j]=define('c'+''.join(map(str,S))+'_'+str(j),neg(z) if j%2 else z)
 for A,Bb in pairs:
  S=tuple(sorted(A+Bb));first=S[0];cond=[op('=',minors[S],'0')]+[op('>',minors[S[:j]+S[j+1:]],'0') for j in range(len(S))]
  for j in range(1,len(S)):
   cond.append(op('>' if ((first in A)==(S[j] in A)) else '<',cof[S,j],'0'))
  assertion(op('not',conj(cond)))
 out.append('(check-sat)');return '\n'.join(out)+'\n',len(pairs)
if __name__=='__main__':
 out=ROOT/'systems';out.mkdir(exist_ok=True);summary=[]
 for typ in [4,5,7]:
  for sharp in [False,True]:
   if typ==7 and not sharp:continue # existing near-universality covers this after rectangular result
   E,T,C,H,basis,orbits=markings(typ,sharp)
   for k,(M,n) in enumerate(orbits):
    name=f't{typ}_'+('ray' if sharp else 'interior')+f'_{k+1}.smt2';smttext,pairs=smt(typ,sharp,E,C,M);(out/name).write_text(smttext);summary.append(dict(type=typ,sharp=sharp,basis=basis,marking=[list(map(int,r)) for r in M.tolist()],orbit_size=n,edge_shifts=[dict(edge=list(e),shift=[int(z) for z in (C*M)[j,:]]) for j,e in enumerate(E)],simplicial_pairs=pairs,file=name))
 (ROOT/'cases.json').write_text(json.dumps(summary,indent=2));print('generated',len(summary),'systems')
