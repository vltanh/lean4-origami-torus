#!/usr/bin/env python3
"""Exact Type 4 hexagonal-marking and clique-pattern symmetry quotient."""
import json
from itertools import permutations, combinations
from collections import Counter
from pathlib import Path

base=Path(__file__).resolve().parent.parent/'orientation_checkpoint'
faces=json.loads((base/'lutz_faces.json').read_text())
F={tuple(sorted(map(int,f))) for f in faces['4'].split()}
E=sorted({e for f in F for e in combinations(f,2)})
N=lambda j:{i for i in range(8) if tuple(sorted((i,j))) in E}
assert len(E)==24
assert all(e in E for e in combinations((1,4,5,6),2))
assert all({1,4,5,6}<=N(j) for j in (2,3))
assert N(0)=={1,2,3,4,5} and N(7)=={2,3,4,5,6}
assert all(tuple(sorted(pair)) not in E for pair in [(2,3),(0,7)])
for j in (0,7):
    link=[tuple(i for i in f if i!=j) for f in F if j in f]
    assert len(link)==5
    assert all(sum(i in e for e in link)==2 for i in N(j))
    seen={min(N(j))}
    for _ in range(5):
        seen|={i for e in link if seen.intersection(e) for i in e}
    assert seen==N(j)
autos=[p for p in permutations(range(8))
       if {tuple(sorted(p[i] for i in f)) for f in F}==F]
assert len(autos)==4
cases=[c for c in json.loads((base/'cases.json').read_text()) if c['type']==4 and c['sharp']]
assert len(cases)==2
def cocycle(c):
    K={}
    for row in c['edge_shifts']:
        i,j=row['edge']; a,b=row['shift']
        K[i,j]=(a,b);K[j,i]=(-a,-b)
    assert set(K)=={(i,j) for i,j in E}|{(j,i) for i,j in E}
    return K
K,K2=map(cocycle,cases)
for c in (K,K2):
    for i,j,k in F:
        assert tuple(sum(c[e][d] for e in [(i,j),(j,k),(k,i)]) for d in (0,1))==(0,0)
# Rows act on row-vector lattice coordinates. The normalized Gram form
# is (1/2)*[[2,1],[1,2]]. Its six shortest vectors determine all isometries.
V=((1,0),(-1,0),(0,1),(0,-1),(1,-1),(-1,1))
def dot(a,b):return 2*a[0]*b[0]+a[0]*b[1]+a[1]*b[0]+2*a[1]*b[1]
M=[(a,b) for a in V for b in V if dot(a,b)==1]
assert len(M)==12
def mul(a,m):return tuple(a[0]*m[0][i]+a[1]*m[1][i] for i in (0,1))
def sub(a,b):return tuple(x-y for x,y in zip(a,b))
def equiv(p,m,source,target):
    h={(i,j):sub(mul(source[p[i],p[j]],m),target[i,j]) for i,j in E}
    h.update({(j,i):tuple(-x for x in v) for (i,j),v in list(h.items())})
    g={i:h[4,i] for i in range(8) if i!=4};g[4]=(0,0)
    return all(h[i,j]==sub(g[j],g[i]) for i,j in E)
for p in autos:
    hits=[m for m in M if equiv(p,m,K,K)]
    assert len(hits)==1
    print('automorphism',p,'compensating lattice isometry',hits[0])
hits=[m for m in M if equiv(tuple(range(8)),m,K2,K)]
assert hits==[((0,1),(-1,1))]
print('ray 2 equivalent to ray 1 at hexagon',hits[0])

data=json.loads((base/'clique_signs4.json').read_text())
cliques=[tuple(q) for q in data['cliques']]
assert cliques==[q for q in combinations(range(8),4) if all(e in E for e in combinations(q,2))]
patterns=set(data['patterns'])
assert len(patterns)==120 and all(s[0]=='+' and len(s)==len(cliques) for s in patterns)
def act(s,p):
    out=[]
    for c in cliques:
        t=tuple(p[i] for i in c)
        parity=sum(a>b for i,a in enumerate(t) for b in t[i+1:])%2
        sign=s[cliques.index(tuple(sorted(t)))]
        out.append(('-' if sign=='+' else '+') if parity else sign)
    return ''.join(out) if out[0]=='+' else ''.join('-' if x=='+' else '+' for x in out)
unseen=patterns.copy();orbits=[]
while unseen:
    s=min(unseen)
    orb=sorted({act(s,p) for p in autos})
    assert set(orb)<=unseen
    unseen.difference_update(orb);orbits.append(orb)
assert len(orbits)==31 and Counter(map(len,orbits))=={4:29,2:2}
print('clique patterns',len(patterns),'joint hexagonal orbits',len(orbits),'sizes',dict(Counter(map(len,orbits))))
for i,orb in enumerate(orbits,1):
    print('H%02d'%i,orb[0],len(orb))
