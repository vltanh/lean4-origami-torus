#!/usr/bin/env python3
"""Type 6 -> Type 4 flip locus: exact two-side classification.

All proofs of forbidden side patterns and mixed-pattern linkage use the
independent, standard-library DPLL routine below. Optional --enumerate
uses libz3 for full projected Boolean model counts, NOT real feasibility.
The geometric hypotheses/perturbation argument are in flip_ready_type6.md.
"""
from collections import Counter
from itertools import combinations, product
import argparse

V = tuple(range(8))
F = [tuple(sorted(map(int, s))) for s in
     '015 052 031 024 043 136 145 174 167 264 257 276 347 356 375 465'.split()]
Q = (5, 7, 2, 3)
ALT = (3, 4, 0, 7)
B = list(combinations(V, 4))
IDS = {b: i+1 for i,b in enumerate(B)}
ZERO = tuple(sorted(Q))

def graph(faces):
    return {e for f in faces for e in combinations(f,2)}

E = graph(F)
def flip(faces, q):
    a,b,c,d = q
    return [f for f in faces if not {a,b} <= set(f)] + [
        tuple(sorted((a,c,d))), tuple(sorted((b,c,d)))]

FN = flip(F,Q)
EN = graph(FN)
K0 = {'04':(0,-1),'24':(0,-1),'26':(-1,0),'27':(-1,0),
      '34':(0,-1),'35':(1,-1),'37':(0,-1),'46':(-1,1),
      '56':(-1,1),'57':(-1,0)}
K = {e: K0.get(''.join(map(str,e)),(0,0)) for e in E}
K.update({(j,i):tuple(-x for x in t) for (i,j),t in list(K.items())})
OUT = tuple(i for i in V if i not in Q)

def addv(a,b):
    return tuple(x+y for x,y in zip(a,b))

def parity(v):
    return (-1)**sum(i>j for i,j in combinations(v,2))

def br(v):
    key = tuple(sorted(v))
    return 0 if key == ZERO else parity(v)*IDS[key]

def side_lits():
    return [br(Q[:3]+(i,)) for i in OUT]

def check_geometry_inputs():
    # Flatness => strict K4, no antipodal links, strict support.
    # The geometric proof in global_attack_support.md is valid for these
    # finite hypotheses, which we check in both triangulations.
    for FS in (F,FN):
        ES=graph(FS)
        antipodal=0
        for i in V:
            N={j for j in V if tuple(sorted((i,j))) in ES}
            assert any(all(e in ES for e in combinations(c,2))
                       for c in combinations(sorted(N|{i}),5))
            L={j:[] for j in N}
            for f in FS:
                if i in f:
                    u,v=sorted(set(f)-{i});L[u].append(v);L[v].append(u)
            assert all(len(neighbors)==2 for neighbors in L.values())
            cy=[min(N)];prev=None
            while True:
                nxt=next(j for j in L[cy[-1]] if j!=prev)
                if nxt==cy[0]:break
                assert nxt not in cy
                prev=cy[-1];cy.append(nxt)
            assert set(cy)==N
            for j,k in combinations(range(len(cy)),2):
                a,b=cy[j],cy[k]
                if tuple(sorted((a,b))) in ES:continue
                antipodal+=1
                arcs=(cy[j:k+1],cy[k:]+cy[:j+1])
                assert any(all(e in ES for e in combinations(sorted((i,*c)),2))
                           for arc in arcs for c in combinations(arc,3))
        assert antipodal==20
        assert all(addv(addv(K[i,j],K[j,k]),K[k,i])==(0,0)
                   for i,j,k in FS) if FS==F else True
    # Relabeling plus central lattice inversion, valid at every modulus.
    p=(2,6,0,7,5,4,1,3)
    g=((0,0),(1,0),(0,0),(1,0),(0,1),(0,1),(1,0),(1,0))
    assert {tuple(sorted(p[i] for i in f)) for f in F}==set(F)
    assert {p[Q[0]],p[Q[1]]}==set(ALT[:2])
    assert {p[Q[2]],p[Q[3]]}==set(ALT[2:])
    assert all(tuple(-a-b for a,b in zip(K[p[i],p[j]],K[i,j]))==
               tuple(b-a for a,b in zip(g[i],g[j])) for i,j in K)
    P=(0,3,2,5,4,1,6,7)
    F4={tuple(sorted(map(int,s))) for s in
        '012 031 024 053 045 152 134 146 165 264 257 276 374 356 367 475'.split()}
    assert {tuple(sorted(P[i] for i in f)) for f in FN}==F4

def make():
    clauses=set()
    def add(vals):
        vals=set(vals);assert 0 not in vals
        if not any(-x in vals for x in vals):
            clauses.add(tuple(sorted(vals,key=lambda n:(abs(n),n))))
    def forbid(vals):
        add([-v for v in vals])
    # A convex planar quadrilateral in diagonal order (a,b,c,d) has
    # unique affine dependence with sign partition {a,b}|{c,d}.
    for i in OUT:
        l=[(-1)**j*br(tuple(Q[k] for k in range(4) if k!=j)+(i,))
           for j in range(4)]
        l=[v*s for v,s in zip(l,(1,1,-1,-1))]
        for v in l[1:]:
            add([-l[0],v]);add([l[0],-v])
    add([side_lits()[0]])  # global reflection gauge
    # Three-term Grassmann--Pluecker relation, including its two-term
    # specialization whenever the one fixed zero bracket occurs.
    for S in combinations(V,2):
        for j,k,l,m in combinations([i for i in V if i not in S],4):
            terms=[(br(S+(j,k)),br(S+(l,m))),
                   (-br(S+(j,l)),br(S+(k,m))),
                   (br(S+(j,m)),br(S+(k,l)))]
            terms=[(u,v) for u,v in terms if u and v]
            assert len(terms)>=2
            for target in (-1,1):
                for signs in product((-1,1),repeat=len(terms)):
                    forbid([v for (u,w),s in zip(terms,signs)
                            for v in (s*u,s*target*w)])
    for f5 in combinations(V,5):
        L=[(-1)**i*br(f5[:i]+f5[i+1:]) for i in range(5)]
        support=[i for i,v in enumerate(L) if v]
        for signs in product((-1,1),repeat=len(support)-1):
            p=(1,)+signs
            A=tuple(f5[i] for i,s in zip(support,p) if s==1)
            C=tuple(f5[i] for i,s in zip(support,p) if s==-1)
            bad=not C
            for FS,ES in ((F,E),(FN,EN)):
                simplices=set(FS)|ES|{(i,) for i in V}
                bad|=A in simplices and C in simplices
                bad|=(len(A)==1 and all(tuple(sorted((A[0],j))) in ES for j in C))
                bad|=(len(C)==1 and all(tuple(sorted((C[0],j))) in ES for j in A))
            if bad:
                lits=[s*L[i] for i,s in zip(support,p)]
                forbid(lits);forbid([-v for v in lits])
    # In a strictly supported flat star at least one incident face has
    # other neighbors on both strict sides. The zero bracket is ignored,
    # never assigned an artificial side for this condition.
    idx=len(B)+1
    for FS,ES in ((F,E),(FN,EN)):
        for i in V:
            choices=[]
            for f in FS:
                if i not in f:continue
                signs=[br(f+(j,)) for j in V if j not in f and
                       tuple(sorted((i,j))) in ES]
                signs=[s for s in signs if s]
                if len(signs)<2:continue
                choices.append(idx);add([-idx]+signs)
                add([-idx]+[-s for s in signs]);idx+=1
            add(choices)
    assert idx-1==166 and len(clauses)==7421
    return idx-1, sorted(clauses)

def simplify(clauses,v):
    return [tuple(x for x in c if x!=-v) for c in clauses if v not in c]

def solve(clauses):
    """Independent finite proof by exhaustive Boolean branching."""
    nodes=0
    def rec(cs):
        nonlocal nodes
        nodes+=1
        while True:
            units={c[0] for c in cs if len(c)==1}
            if any(not c for c in cs) or any(-v in units for v in units):
                return False
            if not units:break
            cs=[tuple(x for x in c if -x not in units) for c in cs
                if all(x not in units for x in c)]
        if not cs:return True
        score=Counter();pos=set()
        for c in cs:
            pos.update(c)
            for x in c:score[abs(x)]+=2**(8-min(len(c),8))
        pure={x for x in pos if -x not in pos}
        if pure:return rec([c for c in cs if not any(x in pure for x in c)])
        v=max(score,key=score.get)
        return rec(simplify(cs,v)) or rec(simplify(cs,-v))
    return rec(clauses),nodes

SAME=(1,1,1,1)
MIXED=(1,-1,1,-1)
TRI=(1,7,5)
RING=(3,6,4)
def edges(c):
    return tuple(zip(c,c[1:]+c[:1]))

def pierce_lits(tri,u,v):
    S=tuple(sorted(tri+(u,v)))
    L=[(-1)**i*br(S[:i]+S[i+1:]) for i in range(5)]
    assert all(L)
    return tuple(x if j in tri else -x for j,x in zip(S,L))

def wind(c,cochain):
    return tuple(sum(cochain[e][i] for e in edges(c)) for i in range(2))

def check_link_data():
    assert set(TRI).isdisjoint(RING)
    assert all(tuple(sorted(e)) in E for c in (TRI,RING) for e in edges(c))
    assert wind(TRI,K)==wind(RING,K)==(1,0)
    a,b,c,d=Q
    k=K.copy()
    k[c,d]=addv(k[c,a],k[a,d])
    assert k[c,d]==addv(k[c,b],k[b,d])==(-1,1)
    k[d,c]=tuple(-v for v in k[c,d])
    assert all(addv(addv(k[i,j],k[j,l]),k[l,i])==(0,0) for i,j,l in FN)
    long=(1,3,2,4)
    assert all(tuple(sorted(e)) in EN for e in edges(long))
    assert wind(long,k)==(1,-2)
    return [pierce_lits(TRI,u,v) for u,v in edges(RING)]

def check():
    check_geometry_inputs()
    n,clauses=make()
    for h in product((1,-1),repeat=3):
        pattern=(1,)+h
        extra=[(s*v,) for s,v in zip(pattern,side_lits())]
        answer,nodes=solve(clauses+extra)
        assert answer==(pattern in (SAME,MIXED))
        print('side',pattern,'SAT' if answer else 'UNSAT','DPLL nodes',nodes)
    terms=check_link_data()
    base=clauses+[(s*v,) for s,v in zip(MIXED,side_lits())]
    # The edge 64 crosses the triangular disk 175, while 36 and 43
    # do not. All five-point supports here avoid the coplanar quadruple.
    for j,L in enumerate(terms):
        if j==1:
            ans,nodes=solve(base+[tuple(-v for v in L),L])
            assert not ans
            print('mixed, no 64 piercing: UNSAT',nodes)
        else:
            for s in (1,-1):
                ans,nodes=solve(base+[(s*v,) for v in L])
                assert not ans
                print('mixed, other piercing',j,s,': UNSAT',nodes)
    print('PASS symmetry, both flat-star hypotheses, two height patterns,')
    print('mixed case links horizontal triangles, and period (1,-2) on four edges.')

def enumerate_z3():
    """Optional full bracket projection counts, solver-dependent."""
    import ctypes as C
    import ctypes.util
    lib=C.CDLL(ctypes.util.find_library('z3'))
    p=C.c_void_p;u=C.c_uint;s=C.c_char_p;I=C.c_int
    z={}
    for key,res,args in [('mk_config',p,[]),('mk_context',p,[p]),
        ('del_config',None,[p]),('mk_solver',p,[p]),
        ('solver_inc_ref',None,[p,p]),('mk_bool_sort',p,[p]),
        ('mk_string_symbol',p,[p,s]),('mk_const',p,[p,p,p]),
        ('mk_not',p,[p,p]),('mk_or',p,[p,u,C.POINTER(p)]),
        ('solver_assert',None,[p,p,p]),('solver_check',I,[p,p]),
        ('solver_get_model',p,[p,p]),
        ('model_eval',C.c_bool,[p,p,p,C.c_bool,C.POINTER(p)]),
        ('get_bool_value',I,[p,p])]:
        f=getattr(lib,'Z3_'+key);f.restype=res;f.argtypes=args;z[key]=f
    cfg=z['mk_config']();ctx=z['mk_context'](cfg);z['del_config'](cfg)
    sol=z['mk_solver'](ctx);z['solver_inc_ref'](ctx,sol)
    sort=z['mk_bool_sort'](ctx)
    n,clauses=make()
    var={i:z['mk_const'](ctx,z['mk_string_symbol'](ctx,('b%d'%i).encode()),sort)
         for i in range(1,n+1)}
    lit=var|{-i:z['mk_not'](ctx,v) for i,v in var.items()}
    def add(cl):
        z['solver_assert'](ctx,sol,z['mk_or'](ctx,len(cl),(p*len(cl))(*[lit[v] for v in cl])))
    for cl in clauses:add(cl)
    ids=[i for q,i in IDS.items() if q!=ZERO]
    terms=check_link_data()
    counts=Counter();unlinked=Counter()
    while True:
        status=z['solver_check'](ctx,sol)
        if status!=1:
            assert status==-1;break
        model=z['solver_get_model'](ctx,sol);S=set()
        for i in ids:
            v=p();assert z['model_eval'](ctx,model,var[i],True,C.byref(v))
            value=z['get_bool_value'](ctx,v);assert value in (-1,1);S.add(i*value)
        pattern=tuple(1 if v in S else -1 for v in side_lits())
        counts[pattern]+=1
        L=0
        for (u,v),lits in zip(edges(RING),terms):
            if all(x in S for x in lits) or all(-x in S for x in lits):
                L+=1 if br(TRI+(v,)) in S else -1
        if L==0:unlinked[pattern]+=1
        add([-v for v in S])
    assert counts==Counter({SAME:305,MIXED:20})
    assert unlinked==Counter({SAME:149})
    print('Boolean bracket models:',counts)
    print('Horizontal unlinking retained:',unlinked)

if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--enumerate',action='store_true')
    args=parser.parse_args()
    check()
    if args.enumerate:enumerate_z3()
