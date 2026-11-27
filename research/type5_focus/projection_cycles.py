#!/usr/bin/env python3
"""Necessary projected-edge crossing constraints for any Type 5 embedding.
No assumptions about the intrinsic metric. Enumerate signed inconsistency
cycles with <=4 active crossing comparisons. Shared triangle vertices
are harmless, as they are extreme in the projected overlap (generic view).
"""
from itertools import combinations,product
from collections import defaultdict,Counter

def forbidden_cycles(F,E):
    E0=lambda f:[tuple(sorted(e)) for e in combinations(f,2)]
    C=[(e,f) for e,f in combinations(E,2) if not set(e)&set(f)]
    I={c:i for i,c in enumerate(C)};adj=defaultdict(dict)
    for f,g in combinations(F,2):
        if len(set(f)&set(g))>1:continue
        l=[]
        for a in E0(f):
            for b in E0(g):
                if not set(a)&set(b):l.append((I[tuple(sorted((a,b)))],1 if a<b else -1))
        for (i,s),(j,t) in combinations(l,2):
            if i==j:continue
            adj[i].setdefault(j,set()).add(s*t);adj[j].setdefault(i,set()).add(s*t)
    cycles=set()
    def walk(path,sign):
        i=path[-1];start=path[0]
        if len(path)>=2 and -sign in adj[i].get(start,()):cycles.add(tuple(sorted(path)))
        if len(path)==4:return
        for j,ss in adj[i].items():
            if j>start and j not in path:
                for s in ss:walk(path+[j],s*sign)
    for i in adj:walk([i],1)
    minimal=sorted(c for c in cycles if not any(s in cycles for n in range(2,len(c)) for s in combinations(c,n)))
    return C,minimal

if __name__=='__main__':
    from focused_system import F,E
    C,cycles=forbidden_cycles(F,E)
    assert len(C)==153 and Counter(map(len,cycles))=={3:9,4:438}
    print('PASS:',len(C),'disjoint-edge comparisons;',dict(Counter(map(len,cycles))),'minimal forbidden crossing sets among cycles of length at most 4')
