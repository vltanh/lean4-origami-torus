#!/usr/bin/env python3
"""Recheck cached clique projections with Z3 and the smaller independent branch certificate.
Run with assertions enabled. The cached lists are supersets of signs of all genuine realizations.
"""
from satgeom import *
import subprocess
P=Path(__file__).resolve().parent
for t in (4,5,7):
    z=json.loads((P/f'clique_signs{t}.json').read_text())
    n,C,T,E,N=formula(t)
    cl=[tuple(q) for q in z['cliques']]
    assert cl==[q for q in Q if set(it.combinations(q,2))<=E]
    S=[ids[q] for q in cl]
    # Test each projected sign pattern for Boolean satisfiability, up to reflection.
    solver=SAT(n,C)
    for p in z['patterns']:
        a=[i*(1 if c=='+' else -1) for i,c in zip(S,p)]
        assert len(a)==len(S) and p[0]=='+'
        solver.push()
        for l in a:solver.add([l])
        b=solver.check();solver.pop()
        if b==-1:
            solver.push()
            for l in a:solver.add([-l])
            b=solver.check();solver.pop()
        assert b==1
    assert len(set(z['patterns']))==len(z['patterns'])=={4:120,5:138,7:316}[t]
    B=list(C)
    for p in z['patterns']:
        a=[i*(1 if c=='+' else -1) for i,c in zip(S,p)]
        B.extend([a,[-i for i in a]])
    assert SAT(n,B).check()==-1
    tree=[(v,tuple(A)) for v,A in z['true_tree']]
    A=tree[0][1];V0=set(A);E0=set(it.combinations(A,2));used=[]
    for v,A in tree:
        assert v not in V0 and set(A)<=V0 and set(it.combinations(A,2))<=E0
        q=tuple(sorted(A+(v,)));assert q in cl;used.append(q)
        E0.update(tuple(sorted((a,v))) for a in A);V0.add(v)
    assert V0==set(V) and E0<=E and len(E0)==18
    used=sorted(used);assert used==[tuple(q) for q in z['true_tree_cliques']]
    ix=[cl.index(q) for q in used];s={''.join(p[i] for i in ix) for p in z['patterns']}
    s={p if p[-1]=='-' else ''.join('+' if c=='-' else '-' for c in p) for p in s}
    assert s==set(z['true_tree_signs']) and len(s)=={4:10,5:7,7:12}[t]
    # For an independent exclusion proof block exactly the allowed tree signs.
    # Clause order agrees with verify_tree.py; use the checked unsat-core subset for Type 7.
    S=[ids[q] for q in used];D=list(C)
    for a in sorted(s):
        v=[1 if b=='+' else -1 for b in a]
        D.extend([[-k*p for k,p in zip(S,v)],[k*p for k,p in zip(S,v)]])
    assert SAT(n,D).check()==-1
    if t==7:
        ix=[int(x) for x in (P/'blocked_tree_7.cnf.coreids').read_text().split()]
        assert len(ix)==len(set(ix))==137 and min(ix)>=0 and max(ix)<len(D)
        D=[D[i] for i in ix]
    cnf=f'p cnf {n} {len(D)}\n'+''.join(' '.join(map(str,c))+' 0\n' for c in D)
    result=subprocess.run([str(P/'check_unsat')],input=cnf,text=True,capture_output=True,check=True).stdout.strip()
    assert result.startswith('UNSAT nodes ')
    print(f'Type {t}: {len(cl)} strict K4 signs, {len(z["patterns"])} projected patterns, {len(s)} tree branches; independent {len(D)}-clause {result}',flush=True)
# Additional height-sign restriction for the Type 5 eight-variable core reconstruction.
z=json.loads((P/'clique_signs5.json').read_text());ci={tuple(q):i for i,q in enumerate(z['cliques'])};A=(1,2,5);B=(0,3,4,6,7);sg=set()
for p in z['patterns']:
    s=tuple((1 if p[ci[tuple(sorted(A+(j,)))]]=='+' else -1)*(-1)**sum(a>b for i,a in enumerate(A+(j,)) for b in (A+(j,))[i+1:]) for j in B)
    sg.add(''.join('+' if a*s[0]>0 else '-' for a in s))
assert len(sg)==7
print('Type 5 anchor height signs, ordered (0,3,4,6,7), modulo reflection:',sorted(sg))
print('PASS: exact necessary orientation branch certificates.')
