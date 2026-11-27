#!/usr/bin/env python3
"""Exact generic H13 sign witness: embedded but no flat-metric claim.
All determinant calculations are integer arithmetic. Uses no solver.
"""
from itertools import combinations
F={tuple(sorted(map(int,s))) for s in '012 031 024 053 045 152 134 146 165 264 257 276 374 356 367 475'.split()}
E={e for f in F for e in combinations(f,2)}
R=[(1000,0,0),(0,1000,0),(3176,2372,-5000),(608,3405,-2561),
   (0,0,0),(0,0,1000),(452,5000,-3294),(1155,720,-1328)]
Q=list(combinations(range(8),4))
S=dict(zip(Q,'-++-++--++--+-+--+-++++--++-+-+++++-++--+--+--+--++--+-+-++--+--++----'))
assert len(S)==70
def sub(a,b):return tuple(x-y for x,y in zip(a,b))
def det(a,b,c):
    return a[0]*(b[1]*c[2]-b[2]*c[1])-a[1]*(b[0]*c[2]-b[2]*c[0])+a[2]*(b[0]*c[1]-b[1]*c[0])
def D(q):
    i,j,k,l=q
    return det(sub(R[j],R[i]),sub(R[k],R[i]),sub(R[l],R[i]))
def sig(q):
    v=D(q)
    assert v
    return 1 if v>0 else -1
assert all(sig(q)==(1 if S[q]=='+' else -1) for q in Q)
N={i:{j for j in range(8) if tuple(sorted((i,j))) in E} for i in range(8)}
pairs=support=0
containment=[]
for C in combinations(range(8),5):
    s=[(-1)**i*sig(C[:i]+C[i+1:]) for i in range(5)]
    pos=tuple(v for v,a in zip(C,s) if a>0)
    neg=tuple(v for v,a in zip(C,s) if a<0)
    assert pos and neg
    assert not ((pos in E and neg in F) or (neg in E and pos in F))
    pairs+=sum(e in E and tuple(v for v in C if v not in e) in F for e in combinations(C,2))
    if len(pos)==1:containment.append((pos[0],neg))
    if len(neg)==1:containment.append((neg[0],pos))
    for v in C:
        if set(C)-{v}<=N[v]:
            assert not (pos==(v,) or neg==(v,));support+=1
for v in range(8):
    assert any(len({sig((*f,w)) for w in N[v]-set(f)})==2 for f in F if v in f)
assert pairs==140 and support==140
assert min(abs(D(q)) for q in Q)==449984000
assert containment==[(7,(0,1,2,4)),(3,(0,2,4,6)),(7,(0,2,3,4)),(7,(0,2,4,5)),(7,(0,2,4,6)),(3,(1,2,4,6)),(3,(2,4,5,6)),(3,(2,4,6,7))]
print('PASS 70 strict signs, minimum absolute determinant 449984000')
print('PASS 140 disjoint edge/face tests, 140 neighbor-support tetrahedra, all mixed-side vertex conditions')
print('Singleton circuits (vertex, containing tetrahedron):',containment)
print('This is a sign-only embedded torus, not an isometric realization of the hexagonal metric.')
