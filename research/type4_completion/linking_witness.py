#!/usr/bin/env python3
"""Exact obstruction to closing ray2_2 by topology and cap separation alone.
The archived H13 integer coordinates are an embedded, NONFLAT Type 4 torus
with the active cap partition. No metric feasibility is asserted.
"""
from pathlib import Path
from itertools import combinations,permutations
import runpy,io,contextlib,sys
ROOT=Path(__file__).resolve().parents[1]
with contextlib.redirect_stdout(io.StringIO()):
 d=runpy.run_path(str(ROOT/'type4_focus/verify_h13_sign_witness.py'))
R,F,E,sig=d['R'],d['F'],d['E'],d['sig'];V=tuple(range(8))
sys.path.insert(0,str(ROOT/'type4_focus'))
from type4_gap_enum import SH
K={(i,j):SH[1].get(str(i)+str(j),(0,0)) for i,j in E}
K.update({(j,i):tuple(-v for v in q) for(i,j),q in list(K.items())})
def edges(c):return list(zip(c,c[1:]+c[:1]))
def wind(c):return tuple(sum(K[e][k] for e in edges(c)) for k in (0,1))
def normalize(c):
 h=wind(c)
 if h<(0,0):return c[:1]+c[:0:-1],tuple(-x for x in h)
 return c,h
def pierces(tri,u,v):
 S=tuple(sorted(tri+(u,v)))
 pos={j for i,j in enumerate(S) if (-1)**i*sig(S[:i]+S[i+1:])>0}
 return pos==set(tri) or set(S)-pos==set(tri)
def link(a,b):
 return sum(sig((a[0],a[k],a[k+1],v))
            for k in range(1,len(a)-1) for u,v in edges(b)
            if pierces((a[0],a[k],a[k+1]),u,v))
cycles=[]
for n in range(3,6):
 for S in combinations(V,n):
  for tail in permutations(S[1:]):
   if tail[0]>tail[-1]:continue
   c=S[:1]+tail
   if all(e in K for e in edges(c)):cycles.append(c)
def verify_links():
 slopes={};pairs=0
 for a,b in combinations(cycles,2):
  if set(a)&set(b):continue
  a,h=normalize(a);b,k=normalize(b);L=link(a,b);pairs+=1
  if h==(0,0) or k==(0,0):assert L==0;continue
  assert h==k,(a,b,h,k)
  assert h not in slopes or slopes[h]==L
  slopes[h]=L
 forms=[(B,C) for B in (-1,1) for C in range(-2,3)
        if all(B*m*n+C*n*n==L for(m,n),L in slopes.items())]
 assert len(forms)==1 and pairs==608
 return forms[0]
A=(1,4,5);B=(0,2,7,3)
assert wind(A)==(-1,0) and wind(B)==(1,0)
assert link(A,B)==0
assert all(R[i][0]==0 for i in A)
assert min(R[i][0] for i in B)==608
assert R[6][0]==452
first=verify_links();assert first==(-1,0)
p=(0,1,3,2,5,4,6,7)
assert {tuple(sorted(p[i] for i in f)) for f in F}==F
assert {p[i] for i in A}==set(A) and {p[i] for i in B}==set(B) and p[6]==6
# This cap-preserving automorphism respects the sharp marking after
# horizontal reflection (m,n)->(-m-n,n) and an integer vertex gauge.
M=((-1,0),(-1,1))
def transform(v):return tuple(sum(v[k]*M[k][j] for k in (0,1)) for j in (0,1))
Delta={(i,j):tuple(a-b for a,b in zip(transform(K[p[i],p[j]]),K[i,j])) for i,j in K}
gauge={4:(0,0)};gauge.update({i:Delta[4,i] for i in V if i!=4})
assert all(Delta[i,j]==tuple(gauge[j][k]-gauge[i][k] for k in (0,1)) for i,j in K)
old_sig=sig
sig=lambda q:old_sig(tuple(p[i] for i in q))
second=verify_links();assert second==(1,1)
print('PASS archived integer Type4 embedding, all70 strict affine signs')
print('PASS active caps145/0273 strictly separated by x; vertex6 between them')
print('PASS cap-preserving automorphism and exact sharp-marking gauge')
print('PASS all608 disjoint cycle pairs for each witness; linking forms:',first,second)
print('These realize both possible q(m,n)=B*m*n+C*n^2 choices up to reflection.')
print('NONFLAT witnesses only: no edge-metric or quantitative phase claim.')
