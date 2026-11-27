#!/usr/bin/env python3
"""Exact linking-number filters for the fixed marking orientation relaxations.
Requires Python 3 and shared libz3. No floating point operations.
"""
from satgeom import *
from collections import Counter, defaultdict
from functools import lru_cache
P=Path(__file__).resolve().parent
cases=json.loads((P/'cases.json').read_text())
def data(case):
    K={tuple(z['edge']):tuple(z['shift']) for z in case['edge_shifts']}
    K.update({(b,a):tuple(-x for x in z) for (a,b),z in list(K.items())})
    T=[]
    for s in it.combinations(V,3):
        ed=list(zip(s,s[1:]+s[:1]))
        if all(e in K for e in ed):
            h=tuple(sum(K[e][i] for e in ed) for i in range(2))
            if h!=(0,0):T.append((s,h))
    pairs=[(a,b,h,g) for (a,h),(b,g) in it.combinations(T,2) if not set(a)&set(b)]
    assert all(h==g or h==tuple(-v for v in g) for a,b,h,g in pairs)
    return K,T,pairs

def sign_lit(q,s):
    a=lit(q);return s[abs(a)-1]*(1 if a>0 else -1)

def pierce(a,u,v,s):
    S=tuple(sorted(a+(u,v)))
    p=[(-1)**i*sign_lit(S[:i]+S[i+1:],s) for i in range(5)]
    pos={j for j,z in zip(S,p) if z==1}
    return pos==set(a) or set(S)-pos==set(a)

def lk(a,b,s):
    return sum(sign_lit(a+(v,),s) for u,v in zip(b,b[1:]+b[:1]) if pierce(a,u,v,s))

def short_pairs(K):
    cycles=[]
    for k in range(3,6):
        for a in it.combinations(V,k):
            for b in it.permutations(a[1:]):
                if b[0]>b[-1]:continue
                c=a[:1]+b;ed=list(zip(c,c[1:]+c[:1]))
                if not all(e in K for e in ed):continue
                h=tuple(sum(K[e][i] for e in ed) for i in range(2))
                if abs(h[0])==1 and h[1]==0:cycles.append(c)
    pairs=[(a,b) for a,b in it.combinations(cycles,2) if not set(a)&set(b)]
    assert pairs
    k=min(len(a)+len(b) for a,b in pairs)
    return [(a,b) for a,b in pairs if len(a)+len(b)==k]

class CNF:
    def __init__(self,n):self.n=n;self.C=[]
    def var(self):self.n+=1;return self.n
    def conjunction(self,L):
        p=self.var();self.C.extend([[-p,l] for l in L]+[[p]+[-l for l in L]]);return p
    def unlink(self,a,b):
        events=[]
        for i in range(1,len(a)-1):
            tri=(a[0],a[i],a[i+1])
            for u,v in zip(b,b[1:]+b[:1]):
                S=tuple(sorted(tri+(u,v)))
                L=[(1 if w in tri else -1)*(-1)**j*lit(S[:j]+S[j+1:]) for j,w in enumerate(S)]
                test=lit(tri+(v,))
                assert (test in L) != (-test in L)
                if test not in L:L=[-l for l in L]
                p=self.conjunction(L);n=self.conjunction([-l for l in L]);events.append((p,n))
        # Deterministic path of signed partial intersection counts.
        old={0:self.var()};self.C.append([old[0]])
        for i,(p,n) in enumerate(events):
            new={k:self.var() for k in range(-i-1,i+2)}
            for k,v in old.items():
                self.C.extend([[-v,-p,new[k+1]],[-v,-n,new[k-1]],[-v,p,n,new[k]]])
            old=new
        self.C.extend([[-v] for k,v in old.items() if k!=0])

def project(t,extra):
    n,C,T,E,N=formula(t)
    Z=json.loads((P/f'clique_signs{t}.json').read_text());cl=[tuple(q) for q in Z['cliques']]
    assert cl==[q for q in Q if set(it.combinations(q,2))<=E]
    S=[ids[q] for q in cl];sol=SAT(extra.n,C+extra.C);patterns=set()
    while sol.check()==1:
        m=sol.model();v=[m[i-1] for i in S];s=''.join('+' if x*v[0]>0 else '-' for x in v);patterns.add(s)
        sol.add([-i*x for i,x in zip(S,v)]);sol.add([i*x for i,x in zip(S,v)])
    assert sol.check()==-1
    assert patterns<=set(Z['patterns'])
    ix=[cl.index(tuple(q)) for q in Z['true_tree_cliques']]
    ss={''.join(p[i] for i in ix) for p in patterns};ss={p if p[-1]=='-' else ''.join('+' if c=='-' else '-' for c in p) for p in ss}
    assert ss<=set(Z['true_tree_signs'])
    print('clique patterns',len(patterns),'of',len(Z['patterns']),'tree branches',len(ss),'of',len(Z['true_tree_signs']),flush=True)
    return sorted(patterns),sorted(ss)

def main():
    out={}
    for c in cases:
        if not c['sharp'] and c['type']!=5:continue
        t=c['type'];K,T,pairs=data(c);short=short_pairs(K)
        assert short and any(h[1]!=0 for a,h in T)
        print(c['file'],'short disjoint cycle pairs',len(short),'lengths',tuple(map(len,short[0])),flush=True)
        extra=CNF(formula(t)[0])
        for a,b in short:extra.unlink(a,b)
        out[c['file']]=dict(zip(('patterns','tree_signs'),project(t,extra)))
    (P/'elongated_linking_projections.json').write_text(json.dumps(out,indent=2)+'\n')

if __name__=='__main__':main()
