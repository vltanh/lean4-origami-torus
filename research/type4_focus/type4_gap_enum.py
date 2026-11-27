#!/usr/bin/env python3
"""Exact maximal gap-cell cover of both Type 4 sharp-ray markings."""
from itertools import combinations,product,permutations
from collections import Counter
F=[tuple(map(int,s)) for s in '012 031 024 053 045 152 134 146 165 264 257 276 374 356 367 475'.split()]
E=sorted({e for f in F for e in combinations(sorted(f),2)})
SH=[{'01':(-1,0),'03':(-1,0),'12':(1,0),'15':(0,1),'25':(-1,1),'27':(-1,1),'35':(1,0),'36':(1,-1),'56':(0,-1),'67':(-1,1)}, {'01':(-1,1),'03':(-1,1),'12':(1,-1),'15':(1,0),'25':(0,1),'27':(0,1),'35':(1,-1),'36':(0,-1),'56':(-1,0),'67':(0,1)}]

def enumerate_cells(sh):
 K={e:sh.get(''.join(map(str,e)),(0,0)) for e in E};K.update({(j,i):(-a,-b) for (i,j),(a,b) in list(K.items())})
 assert all(K[4,j]==(0,0) for j in range(8) if j!=4)
 assert all(tuple(sum(K[i,j][k] for i,j in zip(f,f[1:]+f[:1])) for k in (0,1))==(0,0) for f in F)
 def ok(i,a,j,b):
  if (i,j) not in K:return True
  l,q=a;m,r=b;h=m+4*(r-q+K[i,j][1]);return any(min(l,h)>=2*k and max(l,h)<=2*k+2 for k in [-1,0,1])
 def period(c):return tuple(sum(K[i,j][k] for i,j in zip(c,c[1:]+c[:1])) for k in (0,1))
 # All chordless cycles; the face graph implies none longer than four.
 C=[]
 for n in range(3,9):
  for c in combinations(range(8),n):
   for tail in permutations(c[1:]):
    c1=(c[0],)+tail
    if c1[1]>=c1[-1]:continue
    if not all((i,j) in K for i,j in zip(c1,c1[1:]+c1[:1])):continue
    if not all((i,j) not in K for i,j in combinations(c1,2) if (c1.index(j)-c1.index(i))%n not in (1,n-1)):continue
    assert n<=4
    if period(c1) in ((1,0),(-1,0)):C.append(set(c1))
 print('horizontal chordless cycles',C)
 out=[];order=[4,5,1,6,2,3,0,7]
 # Naming the two gap centers puts vertex 4 in cap 0 or open strip 1.
 for a4 in (0,1):
  v={4:(a4,0)};ds={i:[a for a in product(range(4),range(-1,2)) if ok(4,v[4],i,a)] for i in range(8) if i!=4}
  def rec(k):
   if k==8:
    if all(any(c<= {i for i in v if v[i][0]==r} for c in C) for r in [0,2]):out.append(tuple(v[i] for i in range(8)))
    return
   i=order[k]
   for a in ds[i]:
    if all(ok(j,b,i,a) for j,b in v.items()):v[i]=a;rec(k+1);del v[i]
  rec(1)
 print('raw cells',len(out),Counter(v[4][0] for v in out))
 return K,sorted(out)

def orbits(K,out):
 FF={tuple(sorted(f)) for f in F};autos=[p for p in permutations(range(8)) if {tuple(sorted(p[i] for i in f)) for f in F}==FF];assert len(autos)==4
 ms=[((1,0),(0,1)),((-1,0),(0,-1)),((1,0),(1,-1)),((-1,0),(-1,1))]
 mul=lambda a,M:tuple(sum(a[k]*M[k][l] for k in range(2)) for l in range(2))
 sub=lambda a,b:tuple(x-y for x,y in zip(a,b));zero=(0,0)
 maps=[]
 for p in autos:
  for M in ms:
   D={(i,j):sub(mul(K[p[i],p[j]],M),K[i,j]) for i,j in K};h={4:zero};h.update({i:D[4,i] for i in range(8) if i!=4})
   if all(D[i,j]==sub(h[j],h[i]) for i,j in K):maps.append((p,M[1][1],h))
 print('maps',[(p,s,[h[i][1] for i in range(8)]) for p,s,h in maps]);assert len(maps) in (2,4)
 def act(v,p,s,h):
  u=[s*(v[p[i]][0]+4*v[p[i]][1])+4*h[i][1] for i in range(8)]
  if u[4]%4>=2:u=[a+2 for a in u]
  q4=u[4]//4;return tuple((a%4,a//4-q4) for a in u)
 pool=set(out);O=[]
 while pool:
  v=min(pool);o={act(v,*m) for m in maps};assert o<=pool,(v,o-pool);pool-=o;O.append(sorted(o))
 print('orbits',len(O),Counter(map(len,O)))
 return [o[0] for o in O]

def contained(a,b):
 av=[l+4*q for l,q in a];bv=[l+4*q for l,q in b]
 return any(all(abs(x+delta-y)<=(y%2) for x,y in zip(av,bv)) for delta in (-4,-2,0,2,4))
def maximal(out):
 mx=[a for a in out if not any(a!=b and contained(a,b) for b in out)]
 assert all(any(contained(a,b) for b in mx) for a in out)
 return mx

if __name__=='__main__':
 for i,sh in enumerate(SH):
  K,raw=enumerate_cells(sh);mx=maximal(raw);rs=orbits(K,mx)
  assert (len(raw),len(mx),len(rs))==[(56,10,6),(9,4,2)][i]
  print('maximal',len(mx),'representatives',[( ''.join(str(a) for a,b in r),[b for a,b in r]) for r in rs])
 print('PASS finite gap-cell cover of eight maximal families')
