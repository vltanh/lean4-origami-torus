#!/usr/bin/env python3
"""Four exact cap-sidedness UNSAT certificates, with independent DPLL replay.

Run python3 verify_cap_degeneracy.py (assertions enabled). Standard library
only; the formula generator is imported but no Z3 solver is called.
The compressed data decode to four lists of zero-based clause indices.
Use --dump to inspect the plain JSON certificate.
"""
from pathlib import Path
import sys,json,zlib,base64,hashlib
from collections import Counter
sys.path.insert(0,str(Path(__file__).resolve().parent.parent/'orientation_checkpoint'))
from satgeom import formula,lit,V
RAW=zlib.decompress(base64.b64decode("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"))
assert hashlib.sha256(RAW).hexdigest()=="c8b449ce1f1474ccd430ea33b6e27193f669ba8715e3fc6b8eae6abd0c9ae1a1"
CORES=json.loads(RAW)
def sided(tri,other):
    L=[lit(tri+(i,)) for i in other]
    return [[-L[0],x] for x in L[1:]]+[[L[0],-x] for x in L[1:]]
def dpll(C):
    C=[frozenset(c) for c in C];count=0
    def go(C):
        nonlocal count
        count+=1
        while True:
            if not C:return True
            if any(not c for c in C):return False
            x=next((next(iter(c)) for c in C if len(c)==1),None)
            if x is None:break
            C=[c-{-x} for c in C if x not in c]
        h=Counter(abs(x) for c in C for x in c)
        v=max(h,key=h.get)
        return go(C+[frozenset({v})]) or go(C+[frozenset({-v})])
    return go(C),count
def systems():
    n,C,T,E,N=formula(4)
    assert (n,len(C))==(118,7497)
    A=(1,4,5);B=(0,2,3,7)
    for label in 'AB':
        aa=A+((6,) if label=='A' else ())
        bb=B+((6,) if label=='B' else ())
        for j,tris in enumerate((((0,2,3),(2,3,7)),((0,2,7),(0,3,7))) if label=='A' else (((2,3,7),),((0,2,7),(0,3,7))),1):
            C2=C+sided(A,[i for i in V if i not in aa])
            for t in tris:C2+=sided(t,[i for i in V if i not in bb])
            yield label+str(j),n,C2
if __name__=='__main__':
    if '--dump' in sys.argv:
        print(RAW.decode(),end='')
        sys.exit()
    for name,n,C in systems():
        core=CORES[name]
        assert len(core)==len(set(core)) and all(0<=j<len(C) for j in core)
        a,k=dpll([C[j] for j in core])
        assert not a,name
        print(name,'UNSAT','total clauses',len(C),'core',len(core),'DPLL nodes',k,flush=True)
    print('PASS all four necessary sign systems excluded')
