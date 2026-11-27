#!/usr/bin/env python3
"""Generate 19 finite-metric Type 5 systems; default necessary, --full exact."""
from itertools import combinations, permutations, product
from pathlib import Path
from fractions import Fraction as F
import json,sys
P=Path(__file__).resolve().parent
case=next(c for c in json.loads((P.parent/'cases.json').read_text()) if c['type']==5 and c['sharp'])
faces=[tuple(map(int,f)) for f in json.loads((P.parent/'lutz_faces.json').read_text())['5'].split()]
E=sorted({tuple(sorted(e)) for f in faces for e in combinations(f,2)})
V=range(8)
K={tuple(v['edge']):tuple(v['shift']) for v in case['edge_shifts']}
K.update({(j,i):tuple(-x for x in k) for (i,j),k in list(K.items())});K.update({(i,i):(0,0) for i in V})
assert set(K)=={(i,j) for i,j in E}|{(j,i) for i,j in E}|{(i,i) for i in V}
g={i:K[1,i] for i in V};K={e:tuple(k[t]+g[e[0]][t]-g[e[1]][t] for t in (0,1)) for e,k in K.items()}
assert all(K[1,i]==(0,0) for i in V)
assert all(tuple(sum(K[e][t] for e in ((a,b),(b,c),(c,a))) for t in (0,1))==(0,0) for a,b,c in faces)
def allowed(i,j):
 a,b=F(i,4),F(j,4)
 return [k for k in (-1,0,1) if any(F(h,2)<=a<=F(h+1,2) and F(h,2)<=b+k<=F(h+1,2) for h in range(-2,3))]
A={(i,j):allowed(i,j) for i,j in product(range(4),repeat=2)}
raw=set()
for a in product(range(4),repeat=8):
 if a[1]>=2 or a.count(0)<3 or a.count(2)<3:continue
 dom=[([0] if i==1 else A[a[1],a[i]]) for i in V]
 for q in product(*dom):
  if all(q[j]-q[i]+K[i,j][1] in A[a[i],a[j]] for i,j in E):raw.add((a,q))
assert len(raw)==36
perm=(6,5,2,4,3,1,0,7);M=lambda k:(k[0]+k[1],-k[1])
assert {frozenset(perm[i] for i in f) for f in faces}=={frozenset(f) for f in faces}
g={i:tuple(K[perm[1],perm[i]][t]-M(K[1,i])[t] for t in (0,1)) for i in V}
assert all(K[perm[i],perm[j]]==tuple(M(k)[t]+g[j][t]-g[i][t] for t in (0,1)) for (i,j),k in K.items())
def mirror(a,q):
 t=[F(i,4) for i in a];b=[t[i]-t[1]+q[i] for i in V];t2=[(-t[perm[i]])%1 for i in V]
 if t2[1]>=F(1,2):t2=[(x+F(1,2))%1 for x in t2]
 b2=[-b[perm[i]]-g[i][1]+b[perm[1]]+g[1][1] for i in V]
 q2=tuple(b2[i]-t2[i]+t2[1] for i in V);assert all(x.denominator==1 for x in q2)
 return tuple(int(4*x) for x in t2),tuple(int(x) for x in q2)
assert {mirror(*a) for a in raw}==raw
assert all(mirror(*mirror(*a))==a for a in raw)
rep={min(a,mirror(*a)) for a in raw};assert len(rep)==19 and len({a for a,q in rep})==19
assert {''.join(map(str,a)) for a,q in rep}==set('00020220 00020221 00020222 00022220 00023220 00120220 00120221 00200202 00200232 00220200 00220201 00220202 00220230 00220231 00220232 00230202 00230232 01200202 20022020'.split())
# All numerical bounds are checked using rational arithmetic.
W=10**12;EPS=F(1,1000);DLO=F(119,250);DHI=F(131,250)
beta=F(45,2*EPS*10**6);assert beta<=F(9,400)
assert 16*EPS+beta+F(103,2*10**6)<F(1,25)
assert DLO==1-F(13,25)-4*EPS and DHI==F(13,25)+4*EPS
assert (DLO-4*EPS)*(1-beta)-4*EPS-F(51,10**6)>F(9,20)
assert F(9,20)-2*EPS-F(1,10**6)>F(11,25)
op=lambda s,*a:'('+s+' '+' '.join(a)+')'
def num(x):
 x=F(x); n=str(abs(x.numerator)); n=op('-',n) if x<0 else n
 return n if x.denominator==1 else op('/',n,str(x.denominator))
def add(*a):return '0' if not a else a[0] if len(a)==1 else op('+',*a)
def mul(*a):return '1' if not a else a[0] if len(a)==1 else op('*',*a)
def sub(a,b):return op('-',a,b)
def neg(a):return op('-',a)
def det(A):
 return add(*(neg(mul(*(A[i][p[i]] for i in range(len(A))))) if sum(p[i]>p[j] for i,j in combinations(range(len(A)),2))%2 else mul(*(A[i][p[i]] for i in range(len(A)))) for p in permutations(range(len(A)))))
def generate(a,q,full=False):
 lines=['(set-logic QF_NRA)'];defn=lambda n,e:lines.append(f'(define-fun {n} () Real {e})') or n
 decl=lambda n:lines.append(f'(declare-fun {n} () Real)') or n
 ass=lambda e:lines.append(op('assert',e))
 p={i:['0','0'] if i==1 else [decl(f'x{i}'),decl(f'b{i}')] for i in V};d={}
 def u(i,j,k):return add(sub(p[j][0],p[i][0]),num(F(k[0])+F(k[1],2))),add(sub(p[j][1],p[i][1]),num(k[1]))
 def norm(u):return add(mul(num(F(1,W)),u[0],u[0]),mul(u[1],u[1]))
 for i,j in combinations(V,2):
  if (i,j) in E:
   x,b=u(i,j,K[i,j]);d[i,j]=defn(f'd{i}{j}',norm((x,b)))
   ass(op('<',num(F(-1,2)),x));ass(op('<',x,num(F(1,2))))
   for sg in (1,-1):
    v=add(mul(num(F(sg,2*W)),x),b);bound=num(F(1,2)+F(1,8*W));ass(op('<',neg(bound),v));ass(op('<',v,bound))
  else:
   d[i,j]=decl(f'd{i}{j}');ass(op('>',d[i,j],'0'))
   for k in product(range(-1,2),repeat=2):ass(op('<=',d[i,j],norm(u(i,j,k))))
  d[j,i]=d[i,j]
 for i in V:d[i,i]='0'
 areas=[]
 for i,j,k in faces:
  x,b=u(i,j,K[i,j]);X,B=u(i,k,K[i,k]);area=defn(f'a{i}{j}{k}',sub(mul(x,B),mul(X,b)));areas.append(area);ass(op('<',area,'0'))
 ass(op('=',add(*areas),num(-2)))
 h=[sub(p[i][1],num(q[i])) for i in V];low=[[],[]];high=[[],[]]
 for i,z in enumerate(a):
  if z%2==0:
   k=z//2;low[k].append((sub(h[i],num(EPS)),False));high[k].append((add(h[i],num(EPS)),False))
  elif z==1:
   high[0].append((sub(h[i],num(EPS)),True));low[1].append((add(h[i],num(EPS)),True))
  else:
   high[1].append((sub(h[i],num(EPS)),True));low[0].append((add(h[i],num(EPS-1)),True))
 for k in (0,1):
  for (l,ls),(r,rs) in product(low[k],high[k]):ass(op('<' if ls or rs else '<=',l,r))
 for (l,_),(r,_) in product(low[0],high[1]):ass(op('<',add(l,num(DLO)),r))
 for (l,_),(r,_) in product(low[1],high[0]):ass(op('<',l,add(r,num(DHI))))
 for i,j in combinations(V,2):
  if {a[i],a[j]}=={0,2}:ass(op('>',d[i,j],num(F(121,625))))
  if a[i]==a[j] and a[i]%2==0:ass(op('<=',d[i,j],num(4*EPS*EPS+F(1,4*W))))
 G={(i,j):defn(f'g{i}{j}',mul(num(F(1,2)),sub(add(d[1,i],d[1,j]),d[i,j]))) for i in V if i!=1 for j in V if j!=1 and i<=j};G.update({(j,i):v for (i,j),v in list(G.items())})
 A=[2,5,3];B=[i for i in V if i!=1 and i not in A];minor=lambda rows,cols:det([[G[i,j] for j in cols] for i in rows])
 for n in (1,2,3):ass(op('>',minor(A[:n],A[:n]),'0'))
 for i in B:
  for j in B:
   if i<=j:ass(op('=',minor(A+[i],A+[j]),'0'))
 cliques=[S for S in combinations(V,4) if all(e in E for e in combinations(S,2))];assert len(cliques)==23
 for S in cliques:
  v,*T=S;H=[[mul(num(F(1,2)),sub(add(d[v,i],d[v,j]),d[i,j])) for j in T] for i in T];ass(op('>',det(H),'0'))
 if full:
  simplex={(i,) for i in V}|set(E)|{tuple(sorted(f)) for f in faces}
  H={(i,j):defn(f'h{i}{j}',add('1',G[i,j] if i!=1 and j!=1 else '0')) for i in V for j in V if i<=j};H.update({(j,i):v for (i,j),v in list(H.items())})
  for n in range(2,6):
   for S in combinations(V,n):
    parts=[]
    for k in range(1,min(3,n-1)+1):
     for A0 in combinations(S,k):
      if S[0] in A0 and A0 in simplex and tuple(i for i in S if i not in A0) in simplex:parts.append(A0)
    if not parts:continue
    name=''.join(map(str,S));base=defn('b'+name,det([[H[i,j] for j in S] for i in S]))
    cof=[]
    for k in range(n):
     c=det([[H[i,j] for j in S[1:]] for i in S[:k]+S[k+1:]])
     cof.append(defn('c'+name+'x'+str(k),neg(c) if k%2 else c))
    for A0 in parts:
     ass(op('not',op('and',op('=',base,'0'),*(op('>' if i in A0 else '<',c,'0') for i,c in zip(S,cof)))))
 lines.append('(check-sat)');return '\n'.join(lines)+'\n'
if __name__=='__main__':
 full='--full' in sys.argv;args=[x for x in sys.argv[1:] if x!='--full'];out=Path(args[0]) if args else P/'systems';out.mkdir(parents=True,exist_ok=True)
 for a,q in sorted(rep):
  s=generate(a,q,full);label=''.join(map(str,a));(out/(label+'.smt2')).write_text(s);assert s.count('(declare-fun')==18
  print(label,q,'assertions',s.count('(assert '),flush=True)
 print('PASS: 36 raw branches, 19 symmetry representatives, 18 variables each; full=',full)
