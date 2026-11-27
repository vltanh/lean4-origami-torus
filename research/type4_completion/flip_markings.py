#!/usr/bin/env python3
"""Complete marked inverse-flip orbit and short-link cycle checks."""
from itertools import combinations, permutations, product
from fractions import Fraction as Q

F4 = '012 031 024 053 045 152 134 146 165 264 257 276 374 356 367 475'.split()
F6 = '015 052 031 024 043 136 145 174 167 264 257 276 347 356 375 465'.split()
SH = [
    {'01':(-1,0),'03':(-1,0),'12':(1,0),'15':(0,1),'25':(-1,1),'27':(-1,1),'35':(1,0),'36':(1,-1),'56':(0,-1),'67':(-1,1)},
    {'01':(-1,1),'03':(-1,1),'12':(1,-1),'15':(1,0),'25':(0,1),'27':(0,1),'35':(1,-1),'36':(0,-1),'56':(-1,0),'67':(0,1)}]
PUB = {'04':(0,-1),'24':(0,-1),'26':(-1,0),'27':(-1,0),'34':(0,-1),'35':(1,-1),'37':(0,-1),'46':(-1,1),'56':(-1,1),'57':(-1,0)}
V = tuple(range(8))

def key(f):return ''.join(sorted(f))
def canon(F):return tuple(sorted(map(key,F)))
def graph(F):return {''.join(e) for f in F for e in combinations(key(f),2)}
def transport(F,p):return canon(''.join(str(p[int(i)]) for i in f) for f in F)
def add(a,b):return tuple(x+y for x,y in zip(a,b))
def sub(a,b):return tuple(x-y for x,y in zip(a,b))
def neg(a):return tuple(-x for x in a)
def mul(a,M):return tuple(sum(a[k]*M[k][j] for k in (0,1)) for j in (0,1))
def ext(sh,F):
    k={tuple(map(int,e)):sh.get(e,(0,0)) for e in graph(F)}
    k.update({(j,i):neg(v) for (i,j),v in list(k.items())})
    return k

def gaugeeq(K,L):
    assert K.keys()==L.keys()
    g={4:(0,0)}
    while len(g)<8:
        old=len(g)
        for i,j in K:
            if i in g and j not in g:g[j]=add(g[i],sub(K[i,j],L[i,j]))
        assert len(g)>old
    return all(sub(K[i,j],L[i,j])==sub(g[j],g[i]) for i,j in K)

def flip(F,e,K=None):
    adj=[f for f in F if set(e)<=set(f)]
    assert len(adj)==2
    n=key(set(''.join(adj))-set(e));assert len(n)==2
    if n in graph(F):return None
    new=[f for f in F if f not in adj]+[a+n for a in e]
    if K is None:return n,new
    a,b=map(int,e);c,d=map(int,n);L=K.copy()
    L[c,d]=add(K[c,a],K[a,d]);assert L[c,d]==add(K[c,b],K[b,d])
    L[d,c]=neg(L[c,d]);del L[a,b];del L[b,a]
    assert set(L)==set(ext({},new))
    return n,new,L

def period(c,K):
    return tuple(sum(K[i,j][k] for i,j in zip(c,c[1:]+c[:1])) for k in (0,1))

P=list(permutations(V))
AUT=[p for p in P if transport(F4,p)==canon(F4)]
assert len(AUT)==4
TARGET={transport(F6,p) for p in P}
FLIPS={}
for e in sorted(graph(F4)):
    row=flip(F4,e)
    if row and canon(row[1]) in TARGET:FLIPS[e]=row[0]
assert FLIPS=={'24':'06','25':'17','34':'17','35':'06'}
K=[ext(sh,F4) for sh in SH]
RAY=[((1,0),(0,1)),((-1,0),(0,-1)),((1,0),(1,-1)),((-1,0),(-1,1))]
shorts=[(1,0),(-1,0),(0,1),(0,-1),(1,-1),(-1,1)]
HEX=[(a,b) for a,b in product(shorts,repeat=2)
     if abs(a[0]*b[1]-a[1]*b[0])==1 and
     2*a[0]*b[0]+2*a[1]*b[1]+a[0]*b[1]+a[1]*b[0]==1]
assert len(HEX)==12

def orbit(rep,mats):
    k,e=rep;out=set()
    for p,M,l in product(AUT,mats,range(2)):
        L={(i,j):mul(K[l][p[i],p[j]],M) for i,j in K[k]}
        if gaugeeq(K[k],L):out.add((l,key(str(p[int(i)]) for i in e)))
    return out

pairs=set(product(range(2),FLIPS));classes=[]
while pairs:
    o=orbit(min(pairs),RAY);assert o<=pairs
    classes.append(o);pairs-=o
assert classes==[{(0,'24'),(0,'25')},{(0,'34'),(0,'35')},
                 {(1,'24'),(1,'25'),(1,'34'),(1,'35')}]
assert orbit((1,'25'),HEX)==set(product(range(2),FLIPS))

# The same published old/new graph pair in every class; change only
# the lattice basis and vertex lifts. In each row the relabeling sends
# the Type 4 edge being removed to 23, and the new Type 6 edge to 57.
kp=ext(PUB,F6)
rows=[(1,'25',(0,5,2,1,4,3,6,7),((-1,0),(-1,1))),
      (0,'25',(0,5,2,1,4,3,6,7),((0,-1),(-1,0))),
      (0,'34',(0,5,1,2,3,4,6,7),((0,1),(-1,1)))]
for k,e,p,M in rows:
    n,F,L=flip(F4,e,K[k]);assert transport(F,p)==canon(F6)
    assert key(str(p[int(i)]) for i in e)=='23'
    assert key(str(p[int(i)]) for i in n)=='57'
    assert gaugeeq(L,{(i,j):mul(kp[p[i],p[j]],M) for i,j in L})
    print('inverse class',k+1,e,n,'basis',M)

# Use central inversion and the sharp-ray point group for simpler
# representatives of the same classes in published labels.
MATS=[((1,0),(0,1)),((0,1),(1,0)),((0,1),(-1,1))]
short=[(1,0),(0,1),(1,-1)]
n,Fnew,kn=flip(F6,'57',kp);assert n=='23'
# Each cycle is taken in a genuine old or new triangulation, not in
# their crossing-edge union.
for M,h,witness,bound in zip(MATS,short,[(1,3,2,4),(1,5,3,4,6),(0,1,7,5,4)], [Q(4),Q(25,4),Q(25,4)]):
    assert mul(h,M)==(1,0)
    best=None
    for C in (kp,kn):
        for k in range(3,9):
            for S in combinations(V,k):
                for tail in permutations(S[1:]):
                    if tail[0]>tail[-1]:continue
                    cyc=S[:1]+tail
                    if not all(e in C for e in zip(cyc,cyc[1:]+cyc[:1])):continue
                    m,n=mul(period(cyc,C),M)
                    if n:
                        b=(Q(k*k)-(m+Q(n,2))**2)/(n*n)
                        best=b if best is None else min(best,b)
    assert best==bound
    C=next(C for C in (kp,kn) if all(e in C for e in zip(witness,witness[1:]+witness[:1])))
    m,n=mul(period(witness,C),M)
    assert (Q(len(witness)**2)-(m+Q(n,2))**2)/(n*n)==bound
    print('short slope',h,'best cycle threshold W',best,'witness',witness,(m,n))

# Check the structural input to the finite reconstruction.
quad=(5,7,2,3)
G=kp.copy()
G[2,3]=add(kp[2,5],kp[5,3]);G[3,2]=neg(G[2,3])
G.update({(i,i):(0,0) for i in V})
for i, expected in [(4,((0,0),(-1,0),(0,-1),(-1,0))),
                    (6,((0,0),(0,-1),(0,-1),(0,0)))]:
    T=[add(G[5,j],G[j,i]) for j in quad]
    assert tuple(sub(v,T[0]) for v in T)==expected
assert {j for j in V if (1,j) in kp}=={0,3,4,5,6,7}
assert {j for j in V if (0,j) in kp}=={1,2,3,4,5}
for i,j,k in [(5,4,7),(4,7,6),(7,6,3)]:
    assert all((a,b) in kp for a,b in combinations(sorted((1,i,j,k)),2))
assert all(key(str(j) for j in (1,i,k)) in canon(F6)
           for i,k in [(5,4),(4,7),(7,6),(6,3)])
print('PASS three ray classes, one hexagonal class, cycle thresholds and reconstruction incidences')
