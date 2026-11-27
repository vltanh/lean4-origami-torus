#!/usr/bin/env python3
"""Exact first-scale enumeration, intrinsic and second-scale witnesses."""
from fractions import Fraction as F
from itertools import combinations, permutations, product
from pathlib import Path
import json,sys
P=Path(__file__).resolve().parent
cases=Path(sys.argv[1]) if len(sys.argv)>1 else P.parent/'cases.json'
faces=Path(sys.argv[2]) if len(sys.argv)>2 else P.parent/'lutz_faces.json'
case=next(c for c in json.loads(cases.read_text()) if c['type']==5 and c['sharp'])
T=[tuple(map(int,f)) for f in json.loads(faces.read_text())['5'].split()]
E=sorted({tuple(sorted(e)) for f in T for e in combinations(f,2)})
K={tuple(v['edge']):tuple(v['shift']) for v in case['edge_shifts']}
K.update({(j,i):tuple(-x for x in k) for (i,j),k in list(K.items())});K.update({(i,i):(0,0) for i in range(8)})
assert set(K)=={(i,j) for i,j in E}|{(j,i) for i,j in E}|{(i,i) for i in range(8)}
g={i:K[1,i] for i in range(8)}
K={e:tuple(k[t]+g[e[0]][t]-g[e[1]][t] for t in (0,1)) for e,k in K.items()}
assert all(K[1,i]==(0,0) for i in range(8))
assert all(tuple(sum(K[e][i] for e in ((a,b),(b,c),(c,a))) for i in (0,1))==(0,0) for a,b,c in T)
V=range(8)
def allowed(i,j):
 a,b=F(i,4),F(j,4)
 return [k for k in (-1,0,1) if any(F(h,2)<=a<=F(h+1,2) and F(h,2)<=b+k<=F(h+1,2) for h in range(-2,3))]
A={(i,j):allowed(i,j) for i,j in product(range(4),repeat=2)}
def cycles(S):
 for n in range(3,len(S)+1):
  for C in combinations(S,n):
   for o in permutations(C[1:]):
    c=C[:1]+o; ed=list(zip(c,c[1:]+c[:1]))
    if all(e in K for e in ed) and tuple(sum(K[e][t] for e in ed) for t in (0,1)) in ((1,0),(-1,0)):yield c
raw=set()
for a in product(range(4),repeat=8):
 if a[1]>=2 or a.count(0)<3 or a.count(2)<3:continue
 dom=[([0] if i==1 else A[a[1],a[i]]) for i in V]
 for q in product(*dom):
  if all(q[j]-q[i]+K[i,j][1] in A[a[i],a[j]] for i,j in E):
   assert all(list(cycles([i for i in V if a[i]==k])) for k in (0,2))
   raw.add((a,q))
assert len(raw)==36 and len({a for a,q in raw})==36
def endpoints(a,q):
 for b in product(*[([x] if x%2==0 else [x,0,2]) for x in a]):
  if b[1]>=2:continue
  r=tuple(q[i]+int(a[i]==3 and b[i]==0) for i in V)
  r=tuple(x-r[1] for x in r)
  assert (b,r) in raw
  yield b,r
covered={b for a,q in raw for b in endpoints(a,q) if b!=(a,q)}
maximal=raw-covered
assert len(maximal)==7
assert set().union(*(set(endpoints(*x)) for x in maximal))==raw
perm=(6,5,2,4,3,1,0,7);M=lambda k:(k[0]+k[1],-k[1])
assert {frozenset(perm[i] for i in f) for f in T}=={frozenset(f) for f in T}
g={i:tuple(K[perm[1],perm[i]][t]-M(K[1,i])[t] for t in (0,1)) for i in V}
assert all(K[perm[i],perm[j]]==tuple(M(k)[t]+g[j][t]-g[i][t] for t in (0,1)) for (i,j),k in K.items())
def mirror(a,q):
 t=[F(i,4) for i in a];b=[t[i]-t[1]+q[i] for i in V]
 t2=[(-t[perm[i]])%1 for i in V]
 if t2[1]>=F(1,2):t2=[(x+F(1,2))%1 for x in t2]
 b2=[-b[perm[i]]-g[i][1]+b[perm[1]]+g[1][1] for i in V]
 q2=tuple(b2[i]-t2[i]+t2[1] for i in V);assert all(x.denominator==1 for x in q2)
 return tuple(int(4*x) for x in t2),tuple(int(x) for x in q2)
assert {mirror(*x) for x in raw}==raw
assert {mirror(*x) for x in maximal}==maximal
reps={min(x,mirror(*x)) for x in maximal};assert len(reps)==4
assert {''.join(map(str,a)) for a,q in reps}=={'00120221','00220231','00230232','01200202'}
XDATA={
 '00120221':'1/3 5/12 1/3 -1/3 1/6 0 -1/6',
 '00220231':'5/12 5/12 1/4 -5/12 1/12 -1/24 -1/3',
 '00230232':'5/12 1/4 1/6 -1/3 -1/12 -1/6 -5/12',
 '01200202':'3/7 3/7 1/7 -3/7 1/14 -1/7 -5/14',
 '20022120':'2/7 5/14 0 -3/7 -1/14 -1/7 -3/7',
 '30020221':'5/12 1/3 1/4 -1/3 1/6 1/12 -1/4',
 '30023220':'1/4 1/3 1/6 -5/12 1/12 0 -1/3'}
for a,q in sorted(maximal):
 label=''.join(map(str,a));t=[F(i,4) for i in a];b=[t[i]-t[1]+q[i] for i in V]
 d=lambda i,j:b[j]-b[i]+K[i,j][1]
 C=[next(cycles([i for i in V if a[i]==k])) for k in (0,2)]
 for c,k in zip(C,(0,2)):
  assert set(c)=={i for i in V if a[i]==k}
  assert {tuple(sorted(e)) for e in zip(c,c[1:]+c[:1])}=={(i,j) for i,j in E if a[i]==a[j]==k}
  for i,j in zip(c,c[1:]+c[:1]):
   w=[next(v for v in f if v not in (i,j)) for f in T if {i,j}<=set(f)]
   assert len(w)==2 and d(i,w[0])*d(i,w[1])<0
 assert all(len({a[i] for i in f})>=2 for f in T)
 cross=[];sg=set()
 for i,j in E:
  if {a[i],a[j]}=={0,2}:
   assert abs(d(i,j))==F(1,2)
   sg.add(d(i,j) if a[i]==0 else -d(i,j))
   cross.append((i,j) if d(i,j)>0 else (j,i))
 assert sg=={F(1,2),-F(1,2)}
 left=set(V);order=[]
 while left:
  options=[i for i in left if not any(j in left and k==i for j,k in cross)];assert options
  i=min(options);order.append(i);left.remove(i)
 eta=[-order.index(i)+order.index(1) for i in V]
 x={1:F(0),**dict(zip((0,2,3,4,5,6,7),map(F,XDATA[label].split())))}
 X=lambda i,j:x[j]-x[i]+K[i,j][0]+F(K[i,j][1],2)
 for i,j in E:
  assert abs(X(i,j))<F(1,2) and abs(d(i,j))<=F(1,2)
  h=eta[j]-eta[i]
  for s in (-1,1):
   assert F(1,2)-s*d(i,j)>=0
   assert 256*(F(1,2)-s*d(i,j))+F(1,8)-s*h-abs(X(i,j))/2>0
 for i,j,k in T:
  base=X(i,k)*d(i,j)-X(i,j)*d(i,k)
  corr=X(i,k)*(eta[j]-eta[i])-X(i,j)*(eta[k]-eta[i])
  assert base>0 and base+corr/256>0
 print(label,'cap cycles',C,'strict intrinsic placements for y^2>=256')
print('PASS: 36 relative cells, 7 maximal closed families, 4 up to marking symmetry; cap checks and rational intrinsic placements')
LIMIT={
'00120221':([0,0,2,2,-2,0,0,-2],[0,0,-1,2,2,2,0,-1],[0,0,6,-2,12,-2,2,6],[0,0,0,2,-12,2,-2,0]),
'00220231':([0,0,2,0,-2,0,-2,-1],[0,0,0,0,2,2,2,0],[0,0,2,2,4,-2,0,2],[0,0,-2,-2,-4,2,0,0]),
'00230232':([2,0,2,2,0,0,0,-2],[0,-2,0,1,-2,2,-1,0],[0,4,2,-2,4,-10,6,2],[0,4,2,0,4,6,0,2]),
'01200202':([2,0,2,0,0,0,0,-2],[0,-2,0,-2,-2,2,-2,0],[0,0,2,4,4,-18,4,2],[0,0,2,4,4,14,4,2])}
for a,q in sorted(reps):
 label=''.join(map(str,a));x,p,rho,eta=LIMIT[label]
 x,p,rho,eta=[[F(v,den) for v in z] for z,den in ((x,4),(p,4),(rho,16),(eta,16))]
 t=[F(i,4) for i in a];h=[z if i<=2 else 1-z for z,i in zip(t,a)]
 v=lambda i,j:t[j]-t[i]+q[j]-q[i]+K[i,j][1]
 X=lambda i,j:x[j]-x[i]+K[i,j][0]+F(K[i,j][1],2)
 assert all(eta[i]==0 for i in V if a[i]%2)
 cap={i for i in V if a[i]%2==0};counts=[]
 for sign,lab in ((1,1),(-1,3)):
  S=cap|{i for i in V if a[i]==lab};G=set()
  for i,j in E:
   if {i,j}<=S and h[j]!=h[i] and v(i,j)==sign*(h[j]-h[i]) and not (a[i]%2 and a[j]%2):G.add((i,j))
  reached={min(cap)}
  while True:
   nex=reached|{j for i,j in G if i in reached}|{i for i,j in G if j in reached}
   if nex==reached:break
   reached=nex
  assert reached==S;counts.append(len(S)-1)
 assert sum(counts)==len(cap)+6
 for i,j in E:
  d=h[j]-h[i];vv=v(i,j);assert d*d==vv*vv
  assert (p[j]-p[i])**2+2*d*(rho[j]-rho[i])==X(i,j)**2+2*vv*(eta[j]-eta[i])
  assert abs(X(i,j))<=F(1,2)
  if abs(vv)==F(1,2):assert (1 if vv>0 else -1)*(eta[j]-eta[i])+abs(X(i,j))/2<=F(1,8)
 for i,j,k in T:assert X(i,k)*v(i,j)-X(i,j)*v(i,k)>=0
 print(label,'rank',sum(counts),'exact collinear t=0 witness PASS')
