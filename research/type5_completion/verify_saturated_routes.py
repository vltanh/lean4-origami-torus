#!/usr/bin/env python3
"""Exact shortest-route certificates for 14 Type 5 hexagonal planar masks.
Standard library only; see saturated_routes.md. Optional --ledger replays the old screen.
"""
from collections import defaultdict
from itertools import combinations, permutations
from pathlib import Path
from fractions import Fraction
import json,sys

# mask, orbit size, (a,b,known lift x,y,missing lift x,y),
# then shortest inequalities (a,b,lift x,y,comparison lattice vector x,y).
CERTS=[
(3500,6,(0,1,0,0,1,-1),[(2,3,0,0,1,-1),(0,2,1,-1,1,-1),(1,3,-1,1,-1,1)]),
(3731,6,(0,1,1,0,1,-1),[(1,4,-1,1,0,1),(4,7,1,0,0,1),(0,7,1,-1,0,-1)]),
(3737,6,(0,1,1,0,1,-1),[(1,6,0,1,0,1),(0,6,0,0,0,-1)]),
(4014,6,(5,6,1,0,0,0),[(1,5,0,0,1,-1),(6,7,1,-1,1,-1),(5,6,1,-1,0,-1),(1,7,0,0,-1,1)]),
(5849,6,(1,2,0,-1,-1,0),[(2,4,0,0,1,-1),(1,4,-1,1,-1,1)]),
(6873,3,(1,3,0,1,-1,1),[(1,4,-1,1,0,1),(3,4,0,-1,1,-1),(1,3,0,0,0,-1),(1,4,-1,0,-1,0)]),
(10838,6,(0,5,-1,1,-1,0),[(5,7,1,0,0,1),(0,7,1,-1,0,-1)]),
(10905,3,(0,1,1,0,1,-1),[(1,2,0,0,1,0),(0,2,0,-1,0,-1),(1,2,-1,0,-1,1)]),
(10957,6,(3,5,0,0,-1,0),[(1,4,0,0,1,0),(3,4,-1,0,-1,0),(2,5,-1,1,-1,0),(1,2,-1,0,-1,0)]),
(10961,3,(1,2,-1,0,0,-1),[(1,5,0,0,1,-1),(2,5,-1,1,-1,1)]),
(10965,6,(1,2,-1,0,0,-1),[(1,5,0,0,1,-1),(2,5,-1,1,-1,1)]),
(11084,6,(1,2,0,0,0,-1),[(2,3,0,1,0,1),(3,5,0,0,1,0),(3,5,-1,1,-1,1),(1,5,-1,0,0,-1)]),
(12121,6,(3,4,0,0,-1,0),[(4,5,0,1,1,0),(3,5,-1,0,-1,0)]),
(12185,3,(3,4,0,0,-1,0),[(4,5,0,1,1,0),(3,5,-1,0,-1,0)])]
OLD={3021,3052,4017,10919,18289,18353}
OPEN=[(2550,6),(2553,6),(2806,6),(2809,6),(3449,6),(3501,6),(3502,6),(3513,3),(3514,6),(3763,6),(3766,6),(3769,6),(3948,6),(3953,6),(3981,6),(3993,6),(4012,6),(5779,6),(5785,6),(5806,6),(5810,6),(5817,6),(5818,6),(5881,6),(6905,3),(7854,6),(7857,6),(7858,6),(7865,6),(7866,6),(10886,3),(10887,3),(10893,6),(10918,3),(10925,6),(10950,6),(10963,6),(10966,6),(10969,6),(10982,6),(10998,6),(11001,6),(11116,6),(11124,6),(11149,6),(11161,6),(11212,6),(11213,6),(11225,6),(15065,1),(15097,1),(17777,6),(17785,6),(17841,6),(17849,6),(17905,6),(19635,6),(19889,6),(21682,2),(21683,6),(21881,6),(21945,6)]
add=lambda a,b:tuple(x+y for x,y in zip(a,b))
sub=lambda a,b:tuple(x-y for x,y in zip(a,b))
neg=lambda a:tuple(-x for x in a)

def main(folder):
    F=[tuple(map(int,f)) for f in json.loads((folder/'lutz_faces.json').read_text())['5'].split()]
    assert F==[tuple(map(int,f)) for f in '012 031 024 053 045 152 136 164 147 175 263 237 274 256 357 465'.split()]
    case=next(c for c in json.loads((folder/'cases.json').read_text()) if c['type']==5 and c['sharp'])
    assert case['marking']==[[-1,0],[-1,1]]
    E=sorted({e for f in F for e in combinations(sorted(f),2)})
    K={tuple(row['edge']):tuple(row['shift']) for row in case['edge_shifts']}
    assert set(K)==set(E);K.update({(j,i):neg(k) for (i,j),k in list(K.items())});K.update({(i,i):(0,0) for i in range(8)})
    cyc=lambda a,b,c:add(add(K[a,b],K[b,c]),K[c,a])
    assert all(cyc(*f)==(0,0) for f in F)
    EF={e:tuple(i for i,f in enumerate(F) if set(e)<=set(f)) for e in E};assert all(len(a)==2 for a in EF.values())
    FS={frozenset(f):i for i,f in enumerate(F)};autos=[]
    # The marked basis rows and their symmetry images specify a metric-preserving lattice change.
    U,V=cyc(0,1,4),cyc(0,1,5);det=U[0]*V[1]-U[1]*V[0];assert abs(det)==1
    dot=lambda a,b:2*a[0]*b[0]+a[0]*b[1]+a[1]*b[0]+2*a[1]*b[1]
    for p in permutations(range(8)):
        if {frozenset(p[v] for v in f) for f in F}!=set(FS):continue
        A,B=cyc(p[0],p[1],p[4]),cyc(p[0],p[1],p[5]);M=tuple(tuple((u*A[j]+v*B[j])//det for j in (0,1)) for u,v in ((V[1],-U[1]),(-V[0],U[0])))
        assert all(dot(M[i],M[j])==(2 if i==j else 1) for i in (0,1) for j in (0,1));assert abs(M[0][0]*M[1][1]-M[0][1]*M[1][0])==1
        mv=lambda k:tuple(k[0]*M[0][j]+k[1]*M[1][j] for j in (0,1))
        gauge={v:sub(K[p[1],p[v]],mv(K[1,v])) for v in range(8)}
        assert all(K[p[i],p[j]]==add(mv(K[i,j]),sub(gauge[j],gauge[i])) for i,j in E)
        autos.append([FS[frozenset(p[v] for v in f)] for f in F])
    assert len(autos)==6
    def orbit(m):
        out=set()
        for perm in autos:
            n=sum(((m>>i)&1)<<j for i,j in enumerate(perm));out.add(n^65535 if n>>15 else n)
        return out
    def routes(m):
        signs=[(m>>i)&1 for i in range(16)];assert all(len({signs[i] for i,f in enumerate(F) if v in f})==2 for v in range(8))
        result=defaultdict(set);remaining=set(range(16))
        # Raw edge-connected same-sign components only: no isometry merging.
        while remaining:
            i=remaining.pop();group={i};todo=[i]
            while todo:
                t=todo.pop()
                for e in combinations(sorted(F[t]),2):
                    for w in EF[e]:
                        if w in remaining and signs[w]==signs[t]:remaining.remove(w);group.add(w);todo.append(w)
            adj=defaultdict(set)
            for t in group:
                for a,b in combinations(F[t],2):adj[a].add(b);adj[b].add(a)
            a=min(adj);co={a:(0,0)};todo=[a]
            while todo:
                a=todo.pop()
                for b in adj[a]:
                    q=add(co[a],K[a,b])
                    if b in co:assert co[b]==q
                    else:co[b]=q;todo.append(b)
            for a,b in combinations(sorted(co),2):result[a,b].add(sub(co[b],co[a]))
        adj=defaultdict(set)
        for (a,b),(i,j) in EF.items():
            if signs[i]!=signs[j]:adj[a].add(b);adj[b].add(a)
        # Include all directed subpaths of straight degree-two crease chains.
        for a in range(8):
            for b in adj[a]:
                path=[a,b];q=K[a,b]
                while True:
                    b=path[-1]
                    if a<b:result[a,b].add(q)
                    elif a>b:result[b,a].add(neg(q))
                    if len(adj[b])!=2:break
                    c=next(iter(adj[b]-{path[-2]}));assert c not in path
                    q=add(q,K[b,c]);path.append(c)
        return result
    def row(a,b,k,l):
        v=(2*l[0]+l[1],l[0]+2*l[1]);r=[0]*14
        for j in range(2):
            if a:r[2*(a-1)+j]-=v[j]
            if b:r[2*(b-1)+j]+=v[j]
        rhs=l[0]**2+l[0]*l[1]+l[1]**2-v[0]*k[0]-v[1]*k[1]
        return tuple(r)+(rhs,)
    excluded=set()
    for m,n,witness,terms in CERTS:
        a,b,x,y,z,t=witness;k=(x,y);missing=(z,t);R=routes(m)
        assert k in R[a,b] and missing not in R[a,b]
        target=row(a,b,k,sub(k,missing));sums=[0]*15
        for i,j,x,y,u,v in terms:
            assert (x,y) in R[i,j] and (u,v)!=(0,0)
            sums=[a+b for a,b in zip(sums,row(i,j,(x,y),(u,v)))]
        assert tuple(sums)==neg(target),(m,terms)
        o=orbit(m);assert min(o)==m and len(o)==n and not excluded&o;excluded|=o
        print('PASS',m,n,'masks:',f'{a}{b}',k,'forced missing lift',missing,'from',len(terms),'shortest inequalities')
    assert len(CERTS)==14 and len(excluded)==72
    remaining=set()
    for m,n in OPEN:
        o=orbit(m);assert min(o)==m and len(o)==n and not (remaining|excluded)&o;remaining|=o
    assert len(OPEN)==62 and len(remaining)==343
    assert not (remaining|excluded)&set.union(*(orbit(m) for m in OLD))
    if '--ledger' in sys.argv:
        from verify_planar_patterns import audit_archive,screen
        audit_archive(folder);old={m:n for m,n,d in screen()}
        assert len(old)==82 and sum(old.values())==448
        assert set(old)==OLD|{m for m,*_ in CERTS}|{m for m,n in OPEN}
        assert all(old[m]==n for m,n,*_ in CERTS) and all(old[m]==n for m,n in OPEN)
    print('PASS: 14 new classes / 72 masks excluded; 62 classes / 343 masks remain in prior regular-planar ledger.')

if __name__=='__main__':
    args=[a for a in sys.argv[1:] if a!='--ledger'];main(Path(args[0]) if args else Path(__file__).resolve().parent.parent/'type5_focus')
