#!/usr/bin/env python3
'''Check exact harmonic placements at the hexagonal modulus for every sharp marking.
This tests only intrinsic constraints, not any embedding in R^3.'''
from fractions import Fraction as Q
from pathlib import Path
import json
P=Path(__file__).resolve().parent
cases=json.loads((P/'cases.json').read_text()); faces=json.loads((P/'lutz_faces.json').read_text())

def solve(A,b):
    A=[[Q(x) for x in row]+[Q(y)] for row,y in zip(A,b)];n=len(A)
    for k in range(n):
        l=next(i for i in range(k,n) if A[i][k]);A[k],A[l]=A[l],A[k];v=A[k][k];A[k]=[x/v for x in A[k]]
        for i in range(n):
            if i!=k:
                v=A[i][k];A[i]=[x-v*y for x,y in zip(A[i],A[k])]
    return [row[-1] for row in A]
def dot(a,b):return a[0]*b[0]+Q(a[0]*b[1]+a[1]*b[0],2)+a[1]*b[1]
def cross(a,b):return a[0]*b[1]-a[1]*b[0]
count=0
for c in cases:
    if not c['sharp']:continue
    f=[tuple(map(int,t)) for t in faces[str(c['type'])].split()];K={}
    for v in c['edge_shifts']:
        i,j=v['edge'];k=tuple(v['shift']);K[i,j]=k;K[j,i]=tuple(-a for a in k)
    for i,j,k in f:assert all(sum(K[e][l] for e in [(i,j),(j,k),(k,i)])==0 for l in range(2))
    N={i:[j for j in range(8) if (i,j) in K] for i in range(8)}
    A=[[len(N[i]) if i==j else -int(j in N[i]) for j in range(1,8)] for i in range(1,8)]
    ps=[solve(A,[sum(K[i,j][l] for j in N[i]) for i in range(1,8)]) for l in range(2)]
    p=[(Q(0),Q(0))]+list(zip(*ps));u=lambda i,j:tuple(p[j][l]-p[i][l]+K[i,j][l] for l in range(2))
    ds=[cross(u(i,j),u(i,k)) for i,j,k in f];assert all(d>0 for d in ds) or all(d<0 for d in ds);assert abs(sum(ds))==2
    # At the hexagonal lattice the Voronoi hexagon is determined by these three directions and negatives.
    a=min(dot(v,v)-2*abs(dot(u(i,j),v)) for i,j in K if i<j for v in [(1,0),(0,1),(-1,1)])
    assert a>0
    print('type',c['type'],'marking',c['marking'],'minimum shortest-edge slack',a,'minimum absolute face double area in lattice coordinates',min(map(abs,ds)))
    count+=1
assert count==7
print('PASS: all seven sharp-ray marking representatives have exact intrinsic hexagonal triangulations with strict shortest edges.')
