#!/usr/bin/env python3
"""Radical-free, 14-real-variable Type 5 system; exact hexagonal marking."""
import sys,json
from pathlib import Path
from itertools import combinations,product
P=Path(__file__).resolve().parent
sys.path.insert(0,str(P.parent))
import focused_system as fs
from generate_base import op,add,mul,neg,sub,num,rat,all_,any_,determinant

def generate(chambers=None, full=True):
 lines=['(set-logic QF_NRA)']; A=(1,2,5); R=(3,4); L=(0,6,7); B=R+L
 def declare(s):lines.append(f'(declare-fun {s} () Real)');return s
 def define(s,x):lines.append(f'(define-fun {s} () Real {x})');return s
 def assert_(s):lines.append(op('assert',s))
 def diff(a,b):return [sub(x,y) for x,y in zip(a,b)]
 def plus(a,b):return [add(x,y) for x,y in zip(a,b)]
 def scale(s,a):return [mul(s,x) for x in a]
 def dot(a,b):return add(mul(a[0],b[0]),mul('3',a[1],b[1]))
 def norm(a):return dot(a,a)
 def cross(a,b):return sub(mul(a[0],b[1]),mul(a[1],b[0]))
 def phys(a,b):return [rat(2*a+b,2),rat(b,2)]
 p={i:['0','0'] if i==1 else [declare(f'p{i}{k}') for k in range(2)] for i in range(8)}
 K={e:phys(*k) for e,k in fs.K.items()};E=set(fs.E);F=fs.F
 def u(i,j):return plus(diff(p[j],p[i]),K[i,j])
 D=define('D',cross(p[2],p[5]));assert_(op('>',D,'0'))
 G={}
 for i in range(8):G[i,i]=define(f'g{i}{i}',norm(p[i]))
 for i,j in sorted(E):
  G[i,j]=G[j,i]=define(f'g{i}{j}',mul('(/ 1 2)',sub(add(G[i,i],G[j,j]),norm(u(i,j)))))
 T={1:['0','0']};H={};J={}
 for i in (2,5):T[i]=scale(D,p[i])
 for i in B:
  a,b=G[2,i],G[5,i]
  T[i]=[define(f't{i}0',sub(mul(a,p[5][1]),mul(b,p[2][1]))),define(f't{i}1',mul('(/ 1 3)',sub(mul(p[2][0],b),mul(p[5][0],a))))]
  H[i]=define(f'h{i}',sub(mul(D,D,G[i,i]),norm(T[i])));assert_(op('>',H[i],'0'))
 for i,j in product(R,L):J[i,j]=define(f'j{i}{j}',sub(mul(D,D,G[i,j]),dot(T[i],T[j])))
 def minor(rows,cols):return determinant([[G[i,j] for j in cols] for i in rows])
 for i,j in [(3,j) for j in L]+[(4,0)]:
  q=(2,5,i,j);assert_(op('=',minor(q,q),'0'))
 for j in (6,7):assert_(op('=',minor((2,5,3,4),(2,5,0,j)),'0'))
 # Polynomial affine coordinates: vertical scale = D*H0*sqrt(H3)>0.
 W={i:'0' for i in A};W[3]=define('w3',mul(H[3],H[0]));W[4]=define('w4',mul(J[3,0],J[4,0]))
 for j in L:W[j]=define(f'w{j}',mul(H[0],J[3,j]))
 X={i:T[i]+[W[i]] for i in range(8)}
 for i,j in sorted(E):
  for k in ((1,0),(0,1),(-1,1)):
   q=mul('2',dot(u(i,j),phys(*k)));assert_(all_([op('<',q,'1'),op('>',q,'(- 1)')]))
 areas=[define(f'a{k}',cross(u(i,j),u(i,l))) for k,(i,j,l) in enumerate(F)]
 for a in areas:assert_(op('<',a,'0'))
 assert_(op('=',add(*areas),'(- 1)'))
 # Low-degree, division-free root-chord bounds from the three gauges.
 rows=((1,2,5,3,4,0,7),(2,1,5,4,3,0,6),(5,1,2,3,4,7,6))
 qroot={v:plus(diff(p[4],p[3]),diff(K[v,4],K[v,3])) for v,*_ in rows}
 order=[]
 for v,a,b,c,d,l,m in rows:
  def gauge(i,j):return tuple(fs.K[i,j][k]+fs.K[v,i][k]-fs.K[v,j][k] for k in range(2))
  for i,j in ((a,b),(a,l),(b,m),(c,l),(d,m)):assert gauge(i,j)==(0,0)
  def s(i,j):
   k=gauge(i,j);assert k!=(0,0);t=phys(*k)
   return define(f's{v}{i}{j}',sub(mul('(/ 1 2)',norm(t)),dot(u(i,j),t)))
  ac,ad,bc,bd,M,L0,U,V=(s(i,j) for i,j in ((a,c),(a,d),(b,c),(b,d),(a,m),(b,l),(c,m),(d,l)))
  delta=define(f'delta{v}',sub(mul(ad,bc),mul(ac,bd)));assert_(op('>=',delta,'0'))
  assert_(op('=>',op('<',mul(W[c],W[d]),'0'),op('>',delta,'0')))
  for w in qroot:
   # Difference of the chart norms simplifies to an affine polynomial.
   t=mul('(/ 1 2)',sub(norm(qroot[v]),norm(qroot[w])))
   assert_(op('<=',mul(t,L0,ad),mul(delta,V)))
   assert_(op('<=',mul(t,M,bc),mul(delta,U)))
  n=next(i for i in range(8) if i not in (v,a,b,c,d,l,m));na,nb=s(a,n),s(b,n)
  assert gauge(c,n)==gauge(n,d)==(0,0)
  # At most one of the three chart deficits is zero (injectivity).
  order.append(all_([op('>=',mul(na,bc),mul(nb,ac)),op('>=',mul(nb,ad),mul(na,bd))]))
 assert_(any_([all_([x,y]) for x,y in combinations(order,2)]))
 # Missing-edge contraction, exact after multiplication by a positive factor.
 for i,j in sorted(set(combinations(range(8),2))-E):
  den=mul(H[3],H[0],H[0]); dd=add(mul(den,norm(diff(T[j],T[i]))),mul(sub(W[j],W[i]),sub(W[j],W[i])))
  for a,b in product(range(-1,2),repeat=2):
   assert_(op('<=',dd,mul(den,D,D,norm(plus(diff(p[j],p[i]),phys(a,b))))))
 minors={}
 def aff(q,axes):
  k=(q,axes)
  if k not in minors:
   v=q[0];minors[k]=define('d'+''.join(map(str,q))+'c'+''.join(map(str,axes)),determinant([[sub(X[i][j],X[v][j]) for j in axes] for i in q[1:]]))
  return minors[k]
 Q=list(combinations(range(8),4));CL=set(fs.cl)
 if chambers:
  # Sort-order determinant signs, normalized so det(1,2,5,3)>0.
  k=Q.index((1,2,3,5)); S=[[(-1 if pat[k]=='+' else 1)*(1 if c=='+' else -1) for c in pat] for pat in chambers]
  def tests(pat):return [op(('>' if s>0 else '<') if q in CL else ('>=' if s>0 else '<='),aff(q,(0,1,2)),'0') for q,s in zip(Q,pat)]
  assert_(any_([all_(tests(pat)) for pat in S]))
 if full:
  simplex={(i,) for i in range(8)}|E|{tuple(sorted(f)) for f in F}
  for n in range(2,6):
   for q in combinations(range(8),n):
    parts=[]
    for k in range(1,min(3,n-1)+1):
     for a in combinations(q,k):
      if q[0] in a and a in simplex and tuple(i for i in q if i not in a) in simplex:parts.append(a)
    if not parts:continue
    if n==2:assert_(any_([op('distinct',X[q[0]][j],X[q[1]][j]) for j in range(3)]));continue
    rank=all_([op('=',aff(q,axes),'0') for axes in combinations(range(3),n-1)]) if n<=4 else 'true'
    for a in parts:
     tests=[]
     for axes in combinations(range(3),n-2):
      coeff=[aff(q[:i]+q[i+1:],axes) for i in range(n)]
      ss=[c if ((i%2==0)==(v in a)) else neg(c) for i,(c,v) in enumerate(zip(coeff,q))]
      tests.append(any_([all_([op('>',s,'0') for s in ss]),all_([op('<',s,'0') for s in ss])]))
     assert_(op('not',all_([rank,any_(tests)])))
 lines.append('(check-sat)');return '\n'.join(lines)+'\n'

if __name__=='__main__':
 ch=None
 if '--b11' in sys.argv:
  ch=json.loads((P.parent/'branch_ledger'/'branches.json').read_text())[0]['chambers']
 print(generate(ch,full='--relax' not in sys.argv),end='')
