#!/usr/bin/env python3
"""Exact narrow-level reduction and compactification for Type 7 marking ray_4.
Uses rational arithmetic and SymPy only for the linear rank check.
"""
from verify_linking import *
from fractions import Fraction as Fq
import sympy as sp
c=next(c for c in cases if c['file']=='t7_ray_4.smt2');K,_,_=data(c)
assert short_pairs(K)==[((0,2,4,6),(1,3,5,7))]
A,B=short_pairs(K)[0];q=[-1,-1,-1,-1,0,-2,-1,-2]
G={e:(v[0],v[1]+q[e[1]]-q[e[0]]) for e,v in K.items()}
assert all((i,j) in G and G[i,j][1] in (0,-1) for i in A for j in B)
assert all(G[e][1]==0 for R in (A,B) for e in zip(R,R[1:]+R[:1]))
D=[(i,j) if G[i,j][1]==0 else (j,i) for i in A for j in B]
N={i:{j for j in V if (i,j) in D} for i in V}
maxd=0
for i in V:
    found={i};d=0
    while len(found)<8:
        new=found|set.union(*(N[j] for j in found));assert new!=found;found=new;d+=1
    maxd=max(maxd,d)
assert maxd==3
print('Cross-edge directed graph: 16 edges, strongly connected, directed diameter 3')
Z=json.loads((P/'clique_signs7.json').read_text());cl=[tuple(v) for v in Z['cliques']]
pat=json.loads((P/'elongated_linking_projections.json').read_text())['t7_ray_4.smt2']['patterns'];assert len(pat)==4
for s in pat:
    rows=[]
    for i,j in zip(A,A[1:]+A[:1]):
        row=[]
        for k,l in zip(B,B[1:]+B[:1]):
            v=lit((i,j,k,l));t=1 if s[cl.index(tuple(sorted((i,j,k,l))))]=='+' else -1;row.append(t*(1 if v>0 else -1))
        rows.append(row)
    rare=1 if sum(sum(r) for r in rows)<0 else -1
    assert all(r.count(rare)==1 for r in rows) and all(r.count(rare)==1 for r in zip(*rows))
    print('Sign matrix:',' '.join(''.join('+' if x>0 else '-' for x in r) for r in rows))
# First-order limiting equations: cross squared distances after removing w/4.
E=[(i,j) for i in A for j in B];M=sp.zeros(16,14);rr={v:i+1 for i,v in enumerate(range(2,8))};gg={v:i+7 for i,v in enumerate(range(1,8))}
for k,(i,j) in enumerate(E):
    s=1+2*G[i,j][1];M[k,0]=1
    for v,z in [(i,-1),(j,1)]:
        if v in rr:M[k,rr[v]]=z
        if v in gg:M[k,gg[v]]=-s*z
assert M.rank()==14
print('First-order correction matrix rank 14; two independent residual cross-edge identities')
# Exact degenerate feasible point of the compactified system at t=0.
x=[Fq(i,4) for i in (0,-1,1,0,-2,1,-1,2)];P1=[Fq(i,4) for i in (0,0,-1,1,0,0,-1,1)];P2=[Fq(0)]*8;gamma=[Fq(0)]*8;rho=[Fq(i,8) for i in (0,0,1,-1,0,0,1,-1)];c0=Fq(1,16)
def X(i,j):return x[j]-x[i]+G[i,j][0]+Fq(G[i,j][1],2)
def dp(i,j):return (P1[j]-P1[i])**2+(P2[j]-P2[i])**2
for R in (A,B):
    for i,j in zip(R,R[1:]+R[:1]):
        assert abs(X(i,j))<=Fq(1,2) and dp(i,j)==X(i,j)**2
for i,j in E:
    s=1+2*G[i,j][1];assert abs(X(i,j))<=Fq(1,2)
    assert s*(gamma[j]-gamma[i])+abs(X(i,j))/2<=Fq(1,8)
    assert c0+rho[j]-rho[i]+dp(i,j)==X(i,j)**2+s*(gamma[j]-gamma[i])
assert c0==X(0,1)**2
assert all(abs(v)<=Fq(3,8) for v in gamma) and all(abs(v)<=6 for v in rho)
# All planar K4 cross products vanish here, so it meets every weak limiting clique-sign constraint.
assert P2==[0]*8
print('PASS exact degenerate t=0 witness: naive compact closure is feasible; not an embedding.')
# Consistent intrinsic face orientations and degree at the weak t=0 witness.
levels={i:Fq(i%2,2) for i in V};tri=[tuple(map(int,f)) for f in F['7'].split()]
areas=[]
for a,b,c in tri:
    Y=lambda i,j: levels[j]-levels[i]+G[i,j][1]
    areas.append(X(a,b)*Y(a,c)-X(a,c)*Y(a,b))
assert all(z>0 for z in areas) or all(z<0 for z in areas)
assert abs(sum(areas))==2
print('PASS consistent intrinsic faces and absolute degree one at the weak limit')
# Horizontal lifts are bounded by path inequalities; verify a safe bound 3.
from fractions import Fraction
lengths={i:None for i in V};lengths[0]=Fq(0)
for _ in V:
    for (i,j),(m,n) in G.items():
        if lengths[i] is not None:
            b=lengths[i]+Fq(1,2)+abs(m+Fq(n,2))
            if lengths[j] is None or b<lengths[j]:lengths[j]=b
assert all(z<=3 for z in lengths.values())
print('PASS intrinsic horizontal lift bound 3')
