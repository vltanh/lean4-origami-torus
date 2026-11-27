"""Compute two marked lattice periods by developing along a dual spanning tree."""
from itertools import combinations
from certify_positive import dot,sub,cross,vertices
from math import sqrt

def combinatorics(faces):
    E={}
    for i,f in enumerate(faces):
        for a,b in combinations(sorted(f),2):E.setdefault((a,b),[]).append(i)
    assert all(len(v)==2 for v in E.values())
    # Primal tree: use deterministic lexicographic Kruskal.
    def tree(edges,n):
        parent=list(range(n));out=[]
        def root(i):
            while parent[i]!=i:i=parent[i]
            return i
        for e,i,j in edges:
            a,b=root(i),root(j)
            if a!=b: parent[b]=a;out.append(e)
        assert len(out)==n-1
        return set(out)
    T=tree([(e,*e) for e in sorted(E)],8)
    D=tree([(e,*E[e]) for e in sorted(E) if e not in T],len(faces))
    R=sorted(set(E)-T-D);assert len(R)==2
    # Build breadth-first dual development order, using original oriented faces.
    steps=[];seen={0};queue=[0]
    for i in queue:
        for e in sorted(D):
            if i not in E[e]:continue
            j=next(x for x in E[e] if x!=i)
            if j in seen:continue
            a,b=e;f=faces[j]
            if f[(f.index(a)+1)%3]!=b:a,b=b,a
            assert faces[i][(faces[i].index(b)+1)%3]==a
            c=next(v for v in f if v not in e)
            steps.append((i,j,a,b,c));queue.append(j);seen.add(j)
    assert len(seen)==len(faces)
    return steps,[(E[e][0],E[e][1],e[0]) for e in R]

def root(x):return x.sqrt() if hasattr(x,'sqrt') else sqrt(x)
def develop(p,faces,comb=None):
    steps,ends=combinatorics(faces) if comb is None else comb
    P=vertices(p);a,b,c=faces[0];d=sub(P[b],P[a]);l=root(dot(d,d));z=l*0
    charts={0:{a:[z,z],b:[l,z]}}
    def third(a,b,c,pa,pb):
        u,w=sub(P[b],P[a]),sub(P[c],P[a]);s=dot(u,u);d=dot(u,w)/s;C=cross(u,w);k=root(dot(C,C))/s
        x,y=sub(pb,pa)
        return [pa[0]+d*x-k*y,pa[1]+d*y+k*x]
    charts[0][c]=third(a,b,c,charts[0][a],charts[0][b])
    for i,j,a,b,c in steps:
        pa,pb=charts[i][a],charts[i][b]
        charts[j]={a:pa,b:pb,c:third(a,b,c,pa,pb)}
    return [sub(charts[j][a],charts[i][a]) for i,j,a in ends]

def modulus(p,faces,U,comb=None):
    a,b=develop(p,faces,comb);u=[U[0][0]*a[i]+U[0][1]*b[i] for i in range(2)];v=[U[1][0]*a[i]+U[1][1]*b[i] for i in range(2)]
    s=dot(u,u);return [dot(u,v)/s,(u[0]*v[1]-u[1]*v[0])/s]
