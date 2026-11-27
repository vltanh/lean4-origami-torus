#!/usr/bin/env python3
"""Check the cycle representatives used in the topology theorem (integer combinatorics)."""
from verify_linking import *
from collections import defaultdict

def canon(h):return max(h,tuple(-v for v in h))
for t in (4,5,7):
    c=next(c for c in cases if c['type']==t and c['sharp']);K,T,pairs=data(c)
    a,b=(1,0),(1,-1)
    assert abs(a[0]*b[1]-a[1]*b[0])==1
    H=defaultdict(list)
    for A,B,h,g in pairs:H[canon(h)].append((A,B))
    assert H[a] and H[b]
    short={}
    for n in range(3,6):
        for A in it.combinations(V,n):
            for r in it.permutations(A[1:]):
                if r[0]>r[-1]:continue
                cyc=A[:1]+r;ed=list(zip(cyc,cyc[1:]+cyc[:1]))
                if not all(e in K for e in ed):continue
                h=canon(tuple(sum(K[e][k] for e in ed) for k in range(2)))
                short.setdefault(h,cyc)
    targets=(a,b,canon(tuple(x+y for x,y in zip(a,b))),canon(tuple(x-y for x,y in zip(a,b))))
    assert all(h in short for h in targets)
    print('Type',t,'triangle pair counts',{h:len(H[h]) for h in targets[:2]},'four slope representatives',{h:short[h] for h in targets})
    if t==5:
        assert set(H)=={(1,0),(0,1),(1,-1)} and all(len(v)==5 for v in H.values())
        print('Type 5: exactly five pairs on each of three slopes')
# Enumerate possible integral diagonal coefficients q(a), q(b) in {-1,0,1}
# for a unimodular hyperbolic form q with discriminant 1.
allowed=[]
for a,b in it.product(range(-1,2),repeat=2):
    for c in range(-3,4):
        if c*c-4*a*b!=1:continue
        assert a*b==0 and abs(c)==1
        allowed.append((a,b,c))
        if a+b-c in (-1,0,1):assert sum(x!=0 for x in (a,b,a+b-c))==1
print('Allowed quadratic coefficients:',allowed)
print('PASS topology cycle and quadratic-form checks')
