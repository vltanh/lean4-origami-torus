#!/usr/bin/env python3
"""Exact combinatorial and complex-arithmetic checks for the Type 5 planar obstruction.
Run: python3 verify.py ../linking_checkpoint/cases.json ../linking_checkpoint/lutz_faces.json
Only the Python standard library is used. See README for the geometric argument.
"""
import itertools as it
import json,sys
from pathlib import Path
from fractions import Fraction as F
C=json.loads(Path(sys.argv[1]).read_text());D=json.loads(Path(sys.argv[2]).read_text())
V=range(8)

def faces(t):return [tuple(map(int,f)) for f in D[str(t)].split()]
def graph(t):
    T=faces(t);E=sorted({e for f in T for e in it.combinations(sorted(f),2)})
    forced=[]
    for a,b in E:
        i,j=[i for i,f in enumerate(T) if a in f and b in f]
        u,v=[next(x for x in T[k] if x not in (a,b)) for k in (i,j)]
        if tuple(sorted((u,v))) in E:forced.append((i,j,a,b,u,v))
    return T,E,forced

def patterns(t):
    T,E,A=graph(t);out=[]
    for m in range(1<<15):
        s=[(m>>i)&1 for i in range(15)]+[0]
        if all(s[i]!=s[j] for i,j,*_ in A):out.append(s)
    return A,out

expected={3:(17,4),4:(17,0),5:(15,1),6:(16,2),7:(16,2)}
for t,(n,k) in expected.items():
    A,S=patterns(t);assert (len(A),len(S))==(n,k)
    print('Type',t,'forced dual edges',n,'all-flip patterns modulo reflection',k)
T,E,A=graph(5);_,S=patterns(5);s=S[0]
if s[0]:s=[1-x for x in s]
assert ''.join('+' if x else '-' for x in s)=='-++--+--+-+---++'
noncrease=[]
for a,b in E:
    i,j=[i for i,f in enumerate(T) if a in f and b in f]
    if s[i]==s[j]:noncrease.append((a,b))
assert noncrease==[(0,5),(1,6),(2,7)]
assert all(s[i]==0 for i,f in enumerate(T) if any(set(e)<=set(f) for e in noncrease))
case=next(c for c in C if c['file']=='t5_ray_1.smt2')
K={tuple(v['edge']):tuple(v['shift']) for v in case['edge_shifts']}
K.update({(b,a):tuple(-u for u in k) for (a,b),k in list(K.items())})
assert set(K)=={e for a,b in E for e in ((a,b),(b,a))}
add=lambda a,b:tuple(x+y for x,y in zip(a,b))
neg=lambda a:tuple(-x for x in a)
sub=lambda a,b:add(a,neg(b))
zero=(0,0)
for i,j,a,b,u,v in A:
    d=sub(add(K[u,a],K[a,v]),K[u,v]);assert d!=zero
print('PASS all 15 clique-edge alternate lifts are distinct')
for case4 in (c for c in C if c['type']==4 and c['sharp']):
    K4={tuple(z['edge']):tuple(z['shift']) for z in case4['edge_shifts']}
    K4.update({(b,a):neg(z) for (a,b),z in list(K4.items())})
    assert all(sub(add(K4[u,a],K4[a,v]),K4[u,v])!=zero for i,j,a,b,u,v in graph(4)[2])
    print('PASS distinct alternate lifts',case4['file'])
B=(5,1,2);L=(0,6,7);g={v:i for i in range(3) for v in (B[i],L[i])}
rootshifts=[(0,0),(-1,0),(0,-1)]
for i in range(3):
    for v in (B[i],L[i]):assert add(K[3,v],K[v,4])==rootshifts[i]
# Complex numbers x + sqrt(3)*i*y, with rational coordinates.
def times(a,b):return (a[0]*b[0]-3*a[1]*b[1],a[0]*b[1]+a[1]*b[0])
def scale(t,a):return tuple(t*x for x in a)
def dot(a,b):return a[0]*b[0]+3*a[1]*b[1]
one=(F(1),F(0));omega=(F(-1,2),F(1,2));omega2=times(omega,omega);R=[one,omega,omega2]
assert times(omega,omega2)==one and all(dot(r,r)==1 for r in R)
h=sub(one,omega);k=sub(one,omega2);c=(F(1,2),F(-1,2));u=neg(c);v=sub(one,c)
physical=lambda a:add(scale(a[0],h),scale(a[1],k))
assert all(add(one,physical(rootshifts[i]))==R[i] for i in range(3))
assert dot(h,h)==dot(k,k)==dot(sub(h,k),sub(h,k))==3
# Root-3 chart p_i + K_3i, edge displacement shift correction.
def correction(i,j):return add(K[i,j],sub(K[3,i],K[3,j]))
# All three anchor-edge corrections give rotations about the common center c.
for i,j in it.permutations(range(3),2):
    assert physical(correction(B[i],B[j]))==times(sub(R[i],R[j]),c)
# Leaf-to-anchor comparisons take place about roots 3 and 4 respectively.
for i in range(3):
    j=(i+1)%3; k0=(i-1)%3
    assert correction(L[i],B[j])==zero
    assert physical(correction(L[i],B[k0]))==sub(R[i],R[k0])
print('PASS anchor rotation center and cyclic leaf constraints')
# Bilinear coefficient matrix for adjacent anchor groups in the rhombus wedge.
mat=[[dot(a,times(sub(omega,one),b)) for b in (u,v)] for a in (u,v)]
assert mat==[[F(-3,2),F(0)],[F(-3,2),F(-3,2)]]
# If B_k=c, then B_(k+2)=(1-t)*1+t*c, 0<=t<1. Leaf L_(k+1)
# is real by its root-4 relation, and its root-3 relation forces L=0.
assert times(sub(omega2,one),sub(c,one))==(F(0),F(1))
assert times(sub(omega,one),one)[0]==F(-3,2)
assert times(sub(omega,one),c)[0]==0
print('PASS wedge matrix and forced leaf/root coincidence')
print('PASS exact checks; the unique all-clique-flip Type 5 planar pattern is impossible at hexagonal metric.')
