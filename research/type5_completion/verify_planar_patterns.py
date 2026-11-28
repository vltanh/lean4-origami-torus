"""Exact finite filter for regular planar inflation bases of Type 5 at the hexagon.
SciPy proposes dual certificates; every exclusion uses rational arithmetic.
Run with Python 3, NumPy, SciPy, SymPy. See planar_patterns.md for the proof.
"""
from itertools import combinations,product
from collections import defaultdict,Counter
import numpy as np
from scipy.optimize import linprog
F=[tuple(map(int,f)) for f in '012 031 024 053 045 152 136 164 147 175 263 237 274 256 357 465'.split()]
E=sorted({e for f in F for e in combinations(sorted(f),2)})
sh=[(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(-1,0),(-1,1),(0,0),(0,0),(0,1),(0,0),(-1,1),(0,1),(1,0),(0,0),(0,0),(1,-1),(0,0),(1,0),(1,0),(1,0),(1,-1)]
K=dict(zip(E,sh));K.update({(b,a):(-x,-y) for (a,b),(x,y) in list(K.items())});K.update({(v,v):(0,0) for v in range(8)})
add=lambda a,b:(a[0]+b[0],a[1]+b[1]); sub=lambda a,b:(a[0]-b[0],a[1]-b[1]);
EF={e:tuple(i for i,f in enumerate(F) if set(e)<=set(f)) for e in E}; assert all(len(v)==2 for v in EF.values())
for f in F:assert add(add(K[f[0],f[1]],K[f[1],f[2]]),K[f[2],f[0]])==(0,0)
# q intrinsic coordinates in basis (1,tau), metric 2*inner-product [[2,1],[1,2]].
# A shortest displacement p_j-p_i+k obeys 2dot(d,l)<= norm(l)^2. scale by two.
short=[(1,0),(-1,0),(0,1),(0,-1),(1,-1),(-1,1)]
def nearest(i,j,k):
    for a,b in short:
        v=(2*a+b,a+2*b); coeff=[0]*14
        for s in range(2):
            if i:coeff[2*(i-1)+s]-=v[s]
            if j:coeff[2*(j-1)+s]+=v[s]
        yield tuple(coeff), a*a+a*b+b*b-v[0]*k[0]-v[1]*k[1]
base=set(row for i,j in E for row in nearest(i,j,K[i,j]))

def audit_archive(folder):
    import json
    from pathlib import Path
    folder=Path(folder)
    assert F==[tuple(map(int,f)) for f in json.loads((folder/'lutz_faces.json').read_text())['5'].split()]
    case=next(c for c in json.loads((folder/'cases.json').read_text()) if c['type']==5 and c['sharp'])
    assert case['marking']==[[-1,0],[-1,1]]
    assert {tuple(row['edge']):tuple(row['shift']) for row in case['edge_shifts']}=={e:K[e] for e in E}


def components(s):
    remaining=set(range(16)); cs=[]
    while remaining:
        f=remaining.pop(); group={f}; todo=[f]
        while todo:
            t=todo.pop()
            for e in combinations(sorted(F[t]),2):
                for w in EF[e]:
                    if w in remaining and s[w]==s[t]: remaining.remove(w);group.add(w);todo.append(w)
        g={}
        for t in group:
            for a,b in combinations(sorted(F[t]),2):g.setdefault(a,[]).append(b);g.setdefault(b,[]).append(a)
        root=min(g); coord={root:(0,0)}; todo=[root]
        while todo:
            a=todo.pop()
            for b in g[a]:
                q=add(coord[a],K[a,b])
                if b in coord:
                    if coord[b]!=q:return None
                else:coord[b]=q;todo.append(b)
        cs.append((group,coord))
    return cs

def merge_components(cs,s):
    # Same oriented planar isometries that agree on two distinct coherent lifts agree everywhere.
    cs=[(set(g),dict(co)) for g,co in cs]
    while True:
        joined=False
        for i,j in combinations(range(len(cs)),2):
            fi,ci=cs[i];fj,cj=cs[j]
            if s[min(fi)]!=s[min(fj)]:continue
            common=set(ci)&set(cj)
            offsets=Counter(sub(ci[v],cj[v]) for v in common)
            match=[q for q,n in offsets.items() if n>=2]
            if not match:continue
            if len(offsets)>1:return None
            q=match[0];ci.update({v:add(p,q) for v,p in cj.items()});fi.update(fj);del cs[j]
            joined=True;break
        if not joined:return cs

def paths(s):
    creases={e for e,(f,g) in EF.items() if s[f]!=s[g]}; adj={v:[] for v in range(8)}
    for a,b in creases:adj[a].append(b);adj[b].append(a)
    # at degree 2, crease neighbors can't share triangle (angle pi impossible)
    for v in adj:
        if len(adj[v])==2 and any({v,*adj[v]}==set(f) for f in F):return None,'consecutive'
    rem=set(creases); ps=[]
    for a in adj:
        if len(adj[a])==2:continue
        for b in adj[a]:
            if tuple(sorted((a,b))) not in rem:continue
            path=[a,b]; rem.remove(tuple(sorted((a,b))))
            while len(adj[path[-1]])==2:
                c=next(x for x in adj[path[-1]] if x!=path[-2]);edge=tuple(sorted((path[-1],c)))
                if edge not in rem or c in path:return None,'loop'
                rem.remove(edge);path.append(c)
            if len(path)>=3:ps.append(path)
    if rem:return None,'loop'
    return ps,None

def restrictions(s,skip_mono=True, with_paths=True):
    if skip_mono and any(len({s[i] for i,f in enumerate(F) if v in f})==1 for v in range(8)):return None,'mono'
    cs=components(s)
    if cs is None:return None,'inconsistent component'
    cs=merge_components(cs,s)
    if cs is None:return None,'inconsistent merged component'
    rows=set(base)
    for group,co in cs:
        for a,b in combinations(sorted(co),2):rows.update(nearest(a,b,sub(co[b],co[a])))
    if not with_paths:return rows,None
    ps,reason=paths(s)
    if ps is None:return None,reason
    for path in ps:
        co={path[0]:(0,0)}
        for a,b in zip(path,path[1:]):co[b]=add(co[a],K[a,b])
        for i,j in combinations(range(len(path)),2):
            if j-i==1:continue
            a,b=path[i],path[j];k=sub(co[b],co[a]);rows.update(nearest(a,b,k))
            if (a,b) in K and k==K[a,b]:return None,'chord same lift'
    return rows,None

def relint(A,B):
    res=linprog(np.zeros(14),A_ub=A,b_ub=B,bounds=[(None,None)]*14,method='highs')
    if not res.success:return None,None
    active=np.where(abs(B-A@res.x)<1e-7)[0]; pts=[res.x]
    while len(active):
        obj=A[active].sum(axis=0)
        rr=linprog(obj,A_ub=A,b_ub=B,bounds=[(None,None)]*14,method='highs')
        assert rr.success
        new=active[abs(B[active]-A[active]@rr.x)<1e-7]
        if len(new)==len(active):break
        active=new;pts.append(rr.x)
    return np.mean(pts,axis=0),active
from fractions import Fraction
from math import lcm
import sympy as sp
from itertools import permutations
import time,json

def check_dual(A,B,y,target,tval):
    # produce integer combination and compare exactly
    ids=[i for i,v in enumerate(y) if abs(v)>1e-9];co=[Fraction(float(y[i])).limit_denominator(1000000) for i in ids]
    assert all(v>0 for v in co)
    D=lcm(*[v.denominator for v in co]);n=[int(v*D) for v in co]
    assert all(sum(n0*int(A[i,j]) for i,n0 in zip(ids,n))==D*int(target[j]) for j in range(A.shape[1]))
    value=sum(n0*int(B[i]) for i,n0 in zip(ids,n))
    if tval is None:assert value<0
    else:assert value==D*int(tval)
    return (ids,n,D)

def exact_hull(rows):
    A,B=map(np.array,zip(*sorted(rows)));x,active=relint(A,B)
    if x is None:
        rr=linprog(B,A_eq=np.vstack([A.T,np.ones(len(B))]),b_eq=[0]*14+[1],bounds=(0,None),method='highs');assert rr.success and rr.fun<0
        check_dual(A,B,rr.x,[0]*14,None);return None,None
    if len(active):
        obj=A[active].sum(axis=0)
        rr=linprog(obj,A_ub=A,b_ub=B,bounds=[(None,None)]*14,method='highs');assert rr.success
        check_dual(A,B,-rr.ineqlin.marginals,-obj,-B[active].sum())
        mat=sp.Matrix(np.column_stack([A[active],B[active]]).tolist());rref,piv=mat.rref();assert 14 not in piv
    else:rref=sp.zeros(0,15);piv=()
    variables=sp.symbols('x0:14');free=tuple(variables[i] for i in range(14) if i not in piv);vals=list(variables)
    for j,i in enumerate(piv):vals[i]=rref[j,14]-sum(rref[j,k]*variables[k] for k in range(14) if k not in piv)
    return tuple(vals),free

def delta(p,i,j):
    return (p[j][0]-p[i][0]+K[i,j][0],p[j][1]-p[i][1]+K[i,j][1])
def determinant(a,b):return sp.expand(a[0]*b[1]-a[1]*b[0])
def inner(a,b):return sp.expand(2*a[0]*b[0]+a[0]*b[1]+a[1]*b[0]+2*a[1]*b[1])
def mul(a,b):return sp.expand(a[0]*b[0]-a[1]*b[1]),sp.expand(a[0]*b[1]+a[1]*b[0]+a[1]*b[1])
def conj(a):return a[0]+a[1],-a[1]
def points(vals):return [(0,0)]+[tuple(vals[i:i+2]) for i in range(0,14,2)]
def link_order(v):
    # oriented link: edge a->b if face cyclically rotates to (v,a,b)
    d={f[(f.index(v)+1)%3]:f[(f.index(v)+2)%3] for f in F if v in f};first=min(d);L=[first]
    while d[L[-1]]!=first:L.append(d[L[-1]])
    assert len(L)==len(d);return L
LINK=[link_order(v) for v in range(8)]

def reduce_eq(vals,free,s):
    # Compute products in the polynomial ring to avoid expression expansion blowup.
    while True:
        pp=points(vals);generators=free or (sp.Symbol('dummy'),)
        P=lambda a:sp.Poly(a,*generators,domain=sp.QQ)
        p=[tuple(P(a) for a in q) for q in pp]
        def dd(i,j):return (p[j][0]-p[i][0]+K[i,j][0],p[j][1]-p[i][1]+K[i,j][1])
        for i,j,k in F:
            a,b=dd(i,j),dd(i,k);det=a[0]*b[1]-a[1]*b[0]
            if det.is_zero:return None,None,'zero face'
            if det.total_degree()==0 and det.LC()>0:return None,None,'negative face'
        lin=[]
        for v,L in enumerate(LINK):
            C=[a for a in L if (lambda fg:s[fg[0]]!=s[fg[1]])(EF[tuple(sorted((v,a)))])]
            if not C:continue
            assert len(C)%2==0
            A,B=P(1),P(0)
            for i,a in enumerate(C):
                x,y=dd(v,a)
                if i%2==0:x,y=x+y,-y
                A,B=A*x-B*y,A*y+B*x+B*y
            if not B.is_zero and B.total_degree()==0:return None,None,'Kawasaki constant'
            if A.total_degree()==0 and A.LC()>=0:return None,None,'Kawasaki sign'
            if B.total_degree()==1:lin.append(B.as_expr())
        if not lin:return vals,free,None
        M,b=sp.linear_eq_to_matrix(lin,free);R,piv=M.row_join(b).rref()
        if len(free) in piv:return None,None,'Kawasaki inconsistent'
        new=tuple(free[i] for i in range(len(free)) if i not in piv);sub={free[i]:R[j,len(free)]-sum(R[j,k]*free[k] for k in range(len(free)) if k not in piv) for j,i in enumerate(piv)}
        vals=tuple(sp.expand(v.subs(sub,simultaneous=True)) if hasattr(v,'subs') else v for v in vals);free=new

def metric_reduce(vals,free,s):
    # Clique Cayley-Menger / Gram determinants. Saturate each polynomial by
    # nonzero intrinsic face areas, then use all linear consequences. No
    # division by a vanishing factor, and no numerical algebraic test.
    while True:
        pp=points(vals);generators=free or (sp.Symbol('dummy'),)
        P=lambda a:sp.Poly(a,*generators,domain=sp.QQ)
        p=[tuple(P(a) for a in q) for q in pp]
        def dd(i,j):return (p[j][0]-p[i][0]+K[i,j][0],p[j][1]-p[i][1]+K[i,j][1])
        areas=[(lambda a,b:a[0]*b[1]-a[1]*b[0])(dd(i,j),dd(i,k)) for i,j,k in F]
        if any(a.is_zero for a in areas):return None,None,'zero face'
        if any(a.total_degree()==0 and a.LC()>0 for a in areas):return None,None,'negative face'
        d={e:(lambda a,b:a*a+a*b+b*b)(*dd(*e)) for e in E}
        def dist(i,j):return P(0) if i==j else d[tuple(sorted((i,j)))]
        equations=[]
        for quad in combinations(range(8),4):
            if not all(e in E for e in combinations(quad,2)):continue
            a,*b=quad
            G=[[dist(a,i)+dist(a,j)-dist(i,j) for j in b] for i in b]
            f=G[0][0]*(G[1][1]*G[2][2]-G[1][2]*G[2][1])-G[0][1]*(G[1][0]*G[2][2]-G[1][2]*G[2][0])+G[0][2]*(G[1][0]*G[2][1]-G[1][1]*G[2][0])
            if not f.is_zero:equations.append(f)
        # Area of folded oriented closed surface is zero. Signed intrinsic
        # face areas agree with the projected ones up to common reversal.
        signed=sum((a if s[i] else -a for i,a in enumerate(areas)),P(0))
        if not signed.is_zero:equations.append(signed)
        lin=[]
        # Factor only the quadratic face areas. A factor of a strict
        # face determinant is nonzero everywhere on the admissible set.
        safe=set(q for a in areas for q,power in a.factor_list()[1])
        for f in equations:
            if f.total_degree()==0:return None,None,'constant metric'
            # Use factorization and exact divisibility rather than expensive multivariate gcds.
            ff=f
            for q in safe:
                while ff.total_degree()>=q.total_degree() and ff.rem(q).is_zero:ff=ff.exquo(q)
            if ff.total_degree()==0:return None,None,'metric product nonzero'
            if ff.total_degree()==1:lin.append(ff.as_expr())
        if not lin:return vals,free,None
        M,b=sp.linear_eq_to_matrix(lin,free);R,piv=M.row_join(b).rref()
        if len(free) in piv:return None,None,'inconsistent metric linear'
        new=tuple(free[i] for i in range(len(free)) if i not in piv);sub={free[i]:R[j,len(free)]-sum(R[j,k]*free[k] for k in range(len(free)) if k not in piv) for j,i in enumerate(piv)}
        vals=tuple(sp.expand(v.subs(sub,simultaneous=True)) if hasattr(v,'subs') else v for v in vals);free=new
        vals,free,reason=reduce_eq(vals,free,s)
        if reason:return None,None,reason

# symmetry exact
Fset={frozenset(f):i for i,f in enumerate(F)}; autos=[];Q=sp.Matrix([[2,1],[1,2]])
cy=lambda a,b,c:add(add(K[a,b],K[b,c]),K[c,a]);basis=sp.Matrix([cy(0,1,4),cy(0,1,5)])
for p in permutations(range(8)):
    if {frozenset(p[v] for v in f) for f in F}!=set(Fset):continue
    M=basis.inv()*sp.Matrix([cy(p[0],p[1],p[4]),cy(p[0],p[1],p[5])]);assert M*Q*M.T==Q and abs(M.det())==1
    gauge={v:sp.Matrix([K[p[1],p[v]]])-sp.Matrix([K[1,v]])*M for v in range(8)}
    assert all(sp.Matrix([K[p[i],p[j]]])==sp.Matrix([K[i,j]])*M+gauge[j]-gauge[i] for i,j in E)
    autos.append([Fset[frozenset(p[v] for v in f)] for f in F])
assert len(autos)==6

def orbit(m):
    o=set()
    for perm in autos:
        mm=sum(((m>>i)&1)<<j for i,j in enumerate(perm))
        if mm>>15: mm^=65535
        o.add(mm)
    return o

def screen():
    t=time.time();seen=set();counts=Counter();orbits=Counter();sur=[]
    for mask in range(32768):
        if mask in seen:continue
        o=orbit(mask);n=len(o);seen|=o
        signs=[(mask>>i)&1 for i in range(16)];rows,reason=restrictions(signs)
        if rows is not None:
            v,free=exact_hull(rows)
            if v is None:reason='linear infeasible'
            else:
                v,free,reason=reduce_eq(v,free,signs)
                if not reason and len(free)<=5:v,free,reason=metric_reduce(v,free,signs)
        if reason:counts[reason]+=n;orbits[reason]+=1
        else:
            counts['open']+=n;orbits['open']+=1;sur.append((mask,n,len(free)))
    assert len(seen)==32768
    assert counts=={'mono':8088,'inconsistent component':21849,'inconsistent merged component':624,'consecutive':627,'zero face':991,'linear infeasible':45,'Kawasaki sign':45,'metric product nonzero':51,'open':448},counts
    assert orbits['open']==82
    print('PASS exact screen:',dict(counts));print('PASS symmetry classes:',dict(orbits));return sur

if __name__=='__main__':
    from pathlib import Path
    import sys
    audit_archive(Path(sys.argv[1]) if len(sys.argv)>1 else Path(__file__).resolve().parent.parent/'type5_focus')
    p=points(sp.symbols('x0:14'));assert sp.expand(sum(determinant(delta(p,i,j),delta(p,i,k)) for i,j,k in F))==-2
    print('PASS archive inputs and global intrinsic orientation -2')
    print(json.dumps(screen()))
