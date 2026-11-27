#!/usr/bin/env python3
"""Force nonzero determinants in the closure of H13, with exact circuit signs.
Only Python's standard library is needed. See README for geometry.
"""
from itertools import combinations
F={tuple(sorted(map(int,s))) for s in '012 031 024 053 045 152 134 146 165 264 257 276 374 356 367 475'.split()}
E={e for f in F for e in combinations(f,2)}
V=tuple(range(8));Q=list(combinations(V,4))
signs='-++-++--++--+-+--+-++++--++-+-+++++-++--+--+--+--++--+-+-++--+--++----'
assert len(signs)==len(Q)==70
S=dict(zip(Q,signs))
simplices={(v,) for v in V}|E|F
strict={q for q in Q if all(e in E for e in combinations(q,2))}
assert len(strict)==23
proof=[];rounds=[]
while True:
    new=[]
    for q in Q:
        if q in strict:continue
        for w in V:
            if w in q:continue
            C=tuple(sorted(q+(w,)))
            repl={v:tuple(x for x in C if x!=v) for v in C}
            cof={v:(1 if S[repl[v]]=='+' else -1)*(-1)**i for i,v in enumerate(C)}
            # D_q=0. Some replacement determinant is known nonzero,
            # so the five augmented point columns have rank four.
            pivot=next((repl[v] for v in q if repl[v] in strict),None)
            if pivot is None:continue
            a=tuple(v for v in q if cof[v]>0)
            b=tuple(v for v in q if cof[v]<0)
            reason=None
            if not a or not b:reason='same sign'
            elif a in simplices and b in simplices:reason='disjoint simplices'
            elif (len(a)==1 and all(tuple(sorted((a[0],i))) in E for i in b)
                  or len(b)==1 and all(tuple(sorted((b[0],i))) in E for i in a)):
                reason='strict neighbor support'
            if reason:
                new.append((q,w,pivot,a,b,reason))
                break
    if not new:break
    strict.update(row[0] for row in new)
    rounds.append(len(new));proof.extend(new)
assert rounds==[35,5]
assert len(strict)==63
assert sorted(set(Q)-strict)==[(0,1,4,7),(0,2,3,7),(0,2,5,6),(0,2,5,7),(0,4,6,7),(1,2,4,7),(1,3,5,7)]
for q,w,pivot,a,b,reason in proof:
    print('strict',q,'auxiliary',w,'nonzero pivot',pivot,'partition',a,b,reason)
creases=[]
for e in sorted(E):
    T=[f for f in F if set(e)<=set(f)]
    assert len(T)==2
    q=tuple(sorted(set(T[0])|set(T[1])))
    assert q in strict
    creases.append(q)
assert len(creases)==24
print('PASS strict propagation rounds',rounds,'strict determinants',len(strict),'genuine crease edges',len(creases))
