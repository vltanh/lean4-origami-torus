#!/usr/bin/env python3
"""Exact intrinsic flip families and lateration incidence checks; no solver."""
from fractions import Fraction as Q
from itertools import combinations, product
from collections import Counter

F = [tuple(map(int,s)) for s in
     '015 052 031 024 043 136 145 174 167 264 257 276 347 356 375 465'.split()]
E = sorted({e for f in F for e in combinations(sorted(f),2)})
K = {'04':(0,-1),'24':(0,-1),'26':(-1,0),'27':(-1,0),'34':(0,-1),
     '35':(1,-1),'37':(0,-1),'46':(-1,1),'56':(-1,1),'57':(-1,0)}
K = {(i,j):K.get(f'{i}{j}',(0,0)) for i,j in E}
K.update({(j,i):(-m,-n) for (i,j),(m,n) in list(K.items())})
K.update({(i,i):(0,0) for i in range(8)})
# Last three vectors: X times ten, endpoint and limiting b times thirty.
ROWS = [
    ((5,7,2,3),('532','723'),[0,2,-3,2,3,-1,5,5],
     [0,4,2,-12,18,14,-2,14],[0,4,4,-11,19,13,-5,10]),
    ((3,4,0,7),('307','470'),[0,2,-2,1,2,-1,4,5],
     [0,4,4,-10,20,14,0,14],[0,0,0,-10,15,15,0,15])]
def add(a,b):
    return tuple(x+y for x,y in zip(a,b))

for i in range(8):
    N={i}|{b if a==i else a for a,b in E if i in (a,b)}
    assert any(all(e in E for e in combinations(c,2))
               for c in combinations(sorted(N),5))
for quad,replacements,XX,B0,BI in ROWS:
    a,b,c,d=quad
    L=K.copy()
    L[c,d]=add(L[c,a],L[a,d])
    assert L[c,d]==add(L[c,b],L[b,d])
    L[d,c]=tuple(-v for v in L[c,d])
    new=[f for f in F if not {a,b}<=set(f)]+[tuple(map(int,s)) for s in replacements]
    EN=sorted({e for f in new for e in combinations(sorted(f),2)})
    X=[Q(v,10) for v in XX]
    b0=[Q(v,30) for v in B0]
    bi=[Q(v,30) for v in BI]
    def x(i,j):
        m,n=L[i,j]
        return X[j]-X[i]+m+Q(n,2)
    def v(i,j,B):
        return B[j]-B[i]+L[i,j][1]
    def area(f,B):
        i,j,k=f
        return x(i,j)*v(i,k,B)-x(i,k)*v(i,j,B)
    for faces in (F,new):
        assert all(add(add(L[i,j],L[j,k]),L[k,i])==(0,0) for i,j,k in faces)
        assert all(area(f,b0)>0 and area(f,bi)>0 for f in faces)
        assert sum(area(f,b0) for f in faces)==sum(area(f,bi) for f in faces)==2
        directed=Counter((i,j) for a,b,c in faces for i,j in ((a,b),(b,c),(c,a)))
        assert all(directed[j,i]==n==1 for (i,j),n in directed.items())
    gaps=[]
    for i,j in sorted(set(E)|set(EN)):
        assert abs(x(i,j))<Q(1,2) and abs(v(i,j,b0))<Q(2,3)
        assert abs(v(i,j,bi))<=Q(1,2)
        for h,k in product(range(-1,2),repeat=2):
            if not(h or k): continue
            dx=Q(h)+Q(k,2)
            gap=2*x(i,j)*dx+dx*dx+Q(3,4)*(2*k*v(i,j,b0)+k*k)
            slope=2*k*v(i,j,bi)+k*k
            assert gap>0 and slope>=0
            gaps.append(gap)
    out=sorted(set(range(8))-set(quad))
    N={i:[j for j in quad if (i,j) in K] for i in out}
    assert sorted(map(len,N.values()))==[3,3,4,4]
    for i,ns in N.items():
        assert any(all(e in E for e in combinations(sorted([i,*tr]),2))
                   or all(e in EN for e in combinations(sorted([i,*tr]),2))
                   for tr in combinations(ns,3))
    outer=[e for e in E if set(e)<=set(out)]
    triangles=[t for t in combinations(out,3) if all(e in outer for e in combinations(t,2))]
    assert len(outer)==5 and len(triangles)==2
    g={i:L[a,i] for i in quad}
    offsets={}
    for i,ns in N.items():
        if len(ns)!=4: continue
        shifts=[add(g[j],K[j,i]) for j in ns]
        offsets[i]=[tuple(v-w for v,w in zip(t,shifts[0])) for t in shifts]
    expected=({4:[(0,0),(-1,0),(0,-1),(-1,0)],6:[(0,0),(0,-1),(0,-1),(0,0)]}
              if a==5 else
              {1:[(0,0),(0,-1),(0,0),(0,-1)],5:[(0,0),(-1,0),(-1,1),(0,0)]})
    assert offsets==expected
    print(quad,'PASS all sharp W>=3/4; min hex gap',min(gaps),
          'minimum face area normalized',min(area(f,B) for f in F+new for B in (b0,bi)),
          'outside',N,'cycles',triangles)
