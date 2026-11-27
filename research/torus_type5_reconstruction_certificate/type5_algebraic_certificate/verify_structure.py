from itertools import combinations
F={4:'012 031 024 053 045 152 134 146 165 264 257 276 374 356 367 475',5:'012 031 024 053 045 152 136 164 147 175 263 237 274 256 357 465',7:'356 325 364 302 341 310 506 524 547 570 674 601 617 214 207 271'}
F={k:[tuple(map(int,f)) for f in v.split()] for k,v in F.items()}
E={k:{frozenset(e) for f in fs for e in combinations(f,2)} for k,fs in F.items()}
V=set(range(8));A={1,2,5};R={3,4};L={0,6,7};C=A|R
assert frozenset(A) in map(frozenset,F[5])
assert E[5]=={frozenset((a,b)) for a in A for b in V-{a}}|{frozenset((a,b)) for a in R for b in L}
for j in L:
    link={frozenset(set(f)-{j}) for f in F[5] if j in f}
    assert len(link)==5
    for i in C:
        ns={k for k in C-{i} if frozenset((i,k)) in link}
        assert len(ns)==2
        if frozenset(ns) not in E[5]:assert ns==R and i in A
    # degree 2 simple graph on 5 vertices must be a 5-cycle
print('PASS Type 5 join graph, anchor face and five-cycle links')
anchors={4:[(0,2,4,5),(0,3,4,5),(1,2,4,5),(1,2,4,6),(2,4,5,7)],7:[(0,1,2,3),(0,1,2,7),(0,1,3,6),(0,2,3,5),(1,2,3,4)]}
for k,aa in anchors.items():
    aa=list(map(frozenset,aa))
    assert set.union(*(set(a) for a in aa))==V
    for a in aa:
        assert all(frozenset(e) in E[k] for e in combinations(a,2))
        assert all(sum(frozenset((i,j)) in E[k] for j in a)>=3 for i in V-a)
    seen={aa[0]}
    while True:
        more={a for a in aa if any(len(a&b)>=3 for b in seen)}-seen
        if not more:break
        seen|=more
    assert len(seen)==len(aa)
    print(f'PASS Type {k} five tetrahedral anchors')
