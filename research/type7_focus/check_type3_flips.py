#!/usr/bin/env python3
"""Exhaust all sign-preserving combinatorial diagonal flips from the
published Type 3 flattened folding pattern, ignoring convexity (an upper
bound on the genuine planar metric-preserving flips). Standard library only.
"""
from itertools import combinations
from collections import deque
from fractions import Fraction as Q
F3=[tuple(map(int,f)) for f in '012 031 024 043 152 136 145 174 167 264 257 276 347 356 375 465'.split()]
V=range(8)
# Published family 2 at a sharp modulus, in coordinates scaled by y.
x=Q(1,2);w=Q(16);u=x/2-Q(1,2048);k=Q(1,16);l=Q(1,2);b=1-x-2*k
P=[(0,0),(u,u*(b+2*k/l)),(u-Q(1,2),(1-2*u)*x/2),
 (-k-b*l,(l*(w-b*b)-2*b*k)/2),(x+k-Q(1,2),(w+b*x)/2),
 (u-Q(1,2),(w+b*(b+2*u-1))/2),(u-k,b*(u-k)),
 (u,(w+b*b+2*b*u)/2-(2*u-2*x-2*k+1)/(2*(1-l)))]
def area(a,b,c):
 A,B,C=[P[v] for v in (a,b,c)]
 return (B[0]-A[0])*(C[1]-A[1])-(B[1]-A[1])*(C[0]-A[0])
def sign(z):return 1 if z>0 else -1 if z<0 else 0
sg=[sign(area(*f)) for f in F3]
assert sg==[1,-1,-1,1,1,1,1,1,-1,1,-1,-1,-1,-1,1,-1]
def cyc(q):
 i=q.index(min(q));return q[i:]+q[:i]
def canon(f):return tuple(sorted((cyc(q),s) for q,s in f))
def edges(f):return {tuple(sorted(e)) for q,s in f for e in combinations(q,2)}
start=canon(zip(F3,sg));seen={start};todo=deque([start]);degrees=[]
while todo:
 cur=todo.popleft();E=edges(cur)
 assert len(cur)==16 and len(E)==24
 deg=sorted(sum(i in e for e in E) for i in V);degrees.append(deg)
 assert deg!=[6]*8
 for a,b in E:
  f,g=[(q,s) for q,s in cur if a in q and b in q]
  c=next(i for i in f[0] if i not in (a,b));d=next(i for i in g[0] if i not in (a,b))
  if f[1]!=g[1] or tuple(sorted((c,d))) in E:continue
  if f[0][(f[0].index(a)+1)%3]!=b:a,b=b,a
  assert g[0][(g[0].index(b)+1)%3]==a
  nxt=canon([z for z in cur if z not in (f,g)]+[((a,d,c),f[1]),((b,c,d),f[1])])
  if nxt not in seen:seen.add(nxt);todo.append(nxt)
assert len(seen)==3
print('PASS: three sign-preserving flip states; no uniform degree-six triangulation',degrees)
