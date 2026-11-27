#!/usr/bin/env python3
"""Exact necessary screen for all Type 4 planar bases at the hexagon.

Integer arithmetic (NumPy arrays of bounded integers), no real solver.
See planar_seed_screen.md for geometric hypotheses and scope.
"""
from itertools import combinations, permutations, product
from collections import Counter
import json
import argparse
import numpy as np

F=[tuple(map(int,s)) for s in '012 031 024 053 045 152 134 146 165 264 257 276 374 356 367 475'.split()]
E=sorted({e for f in F for e in combinations(sorted(f),2)})
SH={'01':(-1,1),'03':(-1,1),'12':(1,-1),'15':(1,0),'25':(0,1),'27':(0,1),'35':(1,-1),'36':(0,-1),'56':(-1,0),'67':(0,1)}
K={(i,j):SH.get(f'{i}{j}',(0,0)) for i,j in E}
K.update({(j,i):tuple(-x for x in v) for (i,j),v in list(K.items())})
V=range(8)
dual=[tuple(i for i,f in enumerate(F) if set(e)<=set(f)) for e in E]
T=np.array([[2,1],[1,2],[-1,1]],int)
assert len(E)==24 and all(len(d)==2 for d in dual)
assert all(K[4,j]==(0,0) for j in V if j!=4)
assert all(tuple(sum(K[a,b][k] for a,b in zip(f,f[1:]+f[:1]))
                 for k in (0,1))==(0,0) for f in F)

def sub(a,b):return tuple(x-y for x,y in zip(a,b))
def add(a,b):return tuple(x+y for x,y in zip(a,b))
def det(a,b):return a[0]*b[1]-a[1]*b[0]

def islands(mask):
    s=[(mask>>j)&1 for j in range(16)];adj=[set() for _ in F]
    for i,j in dual:
        if s[i]==s[j]:adj[i].add(j);adj[j].add(i)
    remaining=set(range(16));out=[]
    while remaining:
        q=[min(remaining)];remaining.remove(q[0]);c=[]
        while q:
            i=q.pop();c.append(i)
            for j in adj[i]&remaining:remaining.remove(j);q.append(j)
        EC={e for i in c for e in combinations(sorted(F[i]),2)}
        VC=set().union(*(set(F[i]) for i in c))
        p={min(VC):(0,0)};q=list(p)
        while q:
            i=q.pop()
            for j in VC:
                if tuple(sorted((i,j))) not in EC:continue
                v=add(p[i],K[i,j])
                if j in p:
                    if p[j]!=v:return None
                else:p[j]=v;q.append(j)
        out.append((s[c[0]],p))
    return out

def pair_data(cs):
    pairs={(i,j,*K[i,j]) for i,j in E}
    for _,p in cs:
        for i,j in combinations(sorted(p),2):
            pairs.add((i,j,*sub(p[j],p[i])))
    return tuple(sorted(pairs))

def init(pairs):
    # Radial nearest-lift inequalities with p4=0 bound every coordinate
    # in [-1,1], hence every difference in [-2,2].
    U=np.full((3,8,8),2,dtype=np.int64)
    for i in V:U[:,i,i]=0
    for i,j,m,n in pairs:
        sh=T@np.array([m,n])
        U[:,i,j]=np.minimum(U[:,i,j],1-sh)
        U[:,j,i]=np.minimum(U[:,j,i],1+sh)
    return U

def close(U):
    while True:
        old=U.copy()
        for k in V:
            U=np.minimum(U,U[:,:,k,None]+U[:,None,k,:])
        if np.any(np.diagonal(U,axis1=1,axis2=2)<0):return None
        U[0]=np.minimum(U[0],U[1]+U[2].T)
        U[1]=np.minimum(U[1],U[0]+U[2])
        U[2]=np.minimum(U[2],U[1]+U[0].T)
        if np.any(U+U.transpose(0,2,1)<0):return None
        if np.array_equal(U,old):return U

def degenerate(U):
    for i,j,k in F:
        e=[(i,j),(i,k),(j,k)]
        sh=np.array([T@np.array(K[a,b]) for a,b in e]).T
        hi=np.array([U[:,a,b] for a,b in e]).T+sh
        lo=-np.array([U[:,b,a] for a,b in e]).T+sh
        if np.any(np.all((hi==0)&(lo==0),axis=1)):return True
        if np.any(np.sum((hi==0)&(lo==0),axis=0)>=2):return True
        if np.all(hi[:2,:2]==lo[:2,:2]) and hi[0,0]*hi[1,1]==hi[0,1]*hi[1,0]:
            return True
    return False

def overlap(cs):
    cs=cs.copy()
    while True:
        done=False
        for i,j in combinations(range(len(cs)),2):
            si,p=cs[i];sj,q=cs[j]
            if si!=sj:continue
            S=sorted(p.keys()&q.keys())
            pairs=[(a,b) for a,b in combinations(S,2) if (a,b) in K
                   and sub(p[b],p[a])==sub(q[b],q[a])]
            if not pairs:continue
            a,b=pairs[0];delta=sub(p[a],q[a])
            if any(sub(p[k],q[k])!=delta for k in S):
                return 'same-sign inconsistency',None
            cs[i]=(si,p|{k:add(v,delta) for k,v in q.items()})
            del cs[j];done=True;break
        if not done:break
    U=init(pair_data(cs))
    for (s,p),(t,q) in combinations(cs,2):
        S=sorted(p.keys()&q.keys())
        if len(S)<2:continue
        a=S[0]
        d={i:sub(sub(q[i],q[a]),sub(p[i],p[a])) for i in S}
        nz=[v for v in d.values() if v!=(0,0)]
        rank=0 if not nz else 2 if any(det(nz[0],v)!=0 for v in nz) else 1
        if s==t and rank and any(d[i]==d[j] for i,j in combinations(S,2) if (i,j) in K):
            return 'same-sign coincidence',None
        if (s==t and rank==1 or s!=t and rank==0) and any(set(f)<=set(S) for f in F):
            return 'shared face collinear',None
        if s!=t and rank==2:return 'reflection shift rank two',None
        if s!=t and rank==1:
            direction=next((k for k,w in enumerate([(1,0),(0,1),(-1,1)])
                            if det(nz[0],w)==0),None)
            if direction is None:return 'long shift',None
            for i,j in combinations(S,2):
                sh=T[direction]@np.array(sub(p[j],p[i]))
                rhs=-int(T[direction]@np.array(sub(d[j],d[i])))
                assert rhs%2==0
                r=rhs//2-sh
                U[direction,i,j]=min(U[direction,i,j],r)
                U[direction,j,i]=min(U[direction,j,i],-r)
    U=close(U)
    return ('overlap difference infeasible',None) if U is None else ('overlap degenerate',None) if degenerate(U) else ('survives',U)

def rank_bound(U):
    rows=[]
    for k in range(3):
        for i,j in combinations(V,2):
            if U[k,i,j]+U[k,j,i]!=0:continue
            row=np.zeros(16,int)
            coeff=np.array([[1,0],[0,1],[-1,1]][k])
            row[2*j:2*j+2]=coeff;row[2*i:2*i+2]=-coeff
            rows.append(row)
    A=np.array(rows,int).reshape(-1,16);r=0;p=101
    for j in range(16):
        if r==len(A):break
        ii=next((i for i in range(r,len(A)) if A[i,j]%p),None)
        if ii is None:continue
        A[[r,ii]]=A[[ii,r]];A[r]=(A[r]*pow(int(A[r,j]%p),-1,p))%p
        for i in range(r+1,len(A)):A[i]=(A[i]-A[i,j]*A[r])%p
        r+=1
    return r # rigorous lower bound on rational rank

def orbits(masks):
    FF={tuple(sorted(f)) for f in F}
    AUT=[p for p in permutations(V) if {tuple(sorted(p[i] for i in f)) for f in F}==FF]
    assert len(AUT)==4
    shorts=[(1,0),(-1,0),(0,1),(0,-1),(1,-1),(-1,1)]
    HEX=[(a,b) for a,b in product(shorts,repeat=2) if abs(det(a,b))==1
         and 2*a[0]*b[0]+2*a[1]*b[1]+a[0]*b[1]+a[1]*b[0]==1]
    assert len(HEX)==12
    def preserves(p,M):
        delta={(i,j):tuple(sum(K[p[i],p[j]][k]*M[k][l] for k in (0,1))
                           -K[i,j][l] for l in (0,1)) for i,j in K}
        g={4:(0,0)};g.update({j:delta[4,j] for j in V if j!=4})
        return all(delta[i,j]==sub(g[j],g[i]) for i,j in K)
    assert all(any(preserves(p,M) for M in HEX) for p in AUT)
    idx={tuple(sorted(f)):i for i,f in enumerate(F)}
    perms=[[idx[tuple(sorted(p[i] for i in f))] for f in F] for p in AUT]
    pool=set(masks);out=[]
    while pool:
        m=min(pool);o=set()
        for perm in perms:
            q=sum(((m>>i)&1)<<j for i,j in enumerate(perm))
            o.add(q^65535 if q&32768 else q)
        assert o<=pool;pool-=o;out.append(sorted(o))
    return out

def main(output=None):
    counts=Counter();extra=Counter();cache={};survive=[];regular=[]
    for mask in range(1<<15):
        cs=islands(mask)
        if cs is None:counts['inconsistent lifts']+=1;continue
        p=pair_data(cs)
        if p not in cache:
            U=close(init(p))
            cache[p]='difference infeasible' if U is None else 'forced degenerate face' if degenerate(U) else 'survives'
        reason=cache[p];counts[reason]+=1
        if reason!='survives':continue
        reason,U=overlap(cs);extra[reason]+=1
        if U is None:continue
        survive.append(mask)
        if 14-rank_bound(U)>=3 and all(len({(mask>>j)&1 for j,f in enumerate(F) if i in f})>1 for i in V):
            regular.append(mask)
    all_orbits=orbits(survive);regular_orbits=orbits(regular)
    print('initial screen',counts,'distinct consistent-lift systems',len(cache))
    print('overlap screen',extra)
    print('all planar seeds',len(survive),'orbits',len(all_orbits))
    print('regular planar seeds',len(regular),'orbits',len(regular_orbits))
    assert counts==Counter({'inconsistent lifts':30045,'forced degenerate face':1868,'survives':491,'difference infeasible':364})
    assert extra==Counter({'survives':443,'shared face collinear':36,'same-sign inconsistency':12})
    assert len(survive)==443 and len(all_orbits)==121
    assert len(regular)==405 and len(regular_orbits)==109
    if output:
        with open(output,'w') as out:
            json.dump({'face_order':F,'all_planar_orbits':all_orbits,
                       'regular_planar_orbits':regular_orbits},out,indent=2)

if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--output',help='write the complete surviving mask orbits as JSON')
    main(p.parse_args().output)
