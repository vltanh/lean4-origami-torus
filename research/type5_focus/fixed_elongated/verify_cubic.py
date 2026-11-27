#!/usr/bin/env python3
"""Symbolic identities and exact rational feasible witnesses for the quadratic relaxation only."""
from cubic import F,V,E,K,faces,rep,links,MISSING,combinations,product,phase
import sympy as s
a,b,c,d,e,f=s.symbols('a b c d e f')
S=s.Matrix([[0,0,a,b,c],[0,0,0,d,e],[a,0,0,0,f],[b,d,0,0,0],[c,e,f,0,0]])
assert s.expand(S.det()-2*a*d*f*(b*e-c*d))==0
A,B,C=s.symbols('A B C');M=s.Matrix([[0,0,A,B],[0,0,0,C],[A,0,0,0],[B,C,0,0]])
N=s.Matrix([[0,0,C,0],[0,0,-B,A],[C,-B,0,0],[0,A,0,0]])
assert M*N==A*C*s.eye(4);assert s.expand(M.det()-A*A*C*C)==0
print('PASS symbolic five-ray determinant and sparse pivot inverse')
WITNESSES={
'hex':'1/4 5/16 0 -3/8 -1/16 -1/4 -1/4 0 7/16 -1/4 1/8 19/32 0 3/8 0 1/8 1/16 1/64',
'00120221':'1/4 3/8 1/8 -3/8 -1/16 -3/16 -1/4 0 0 0 0 0 0 0 1/8 5/64 5/32 31999999999993/128',
'00220231':'1/4 3/8 1/8 -3/8 -1/16 -1/4 -1/4 0 -1999 0 0 0 -8191999999/32768 0 0 5/64 3/16 999999999939/4',
'00230232':'1/4 3/8 0 -3/8 -1/16 -1/4 -1/4 0 -1999 -16383999997/65536 0 0 -4095999999/16384 -2000 0 1/8 1/8 63743999992203/128',
'01200202':'1/4 7/16 1/8 -3/8 1/16 0 -1/4 0 0 0 0 1 0 0 0 9/64 1/32 0'}
names=[f'{c}{i}' for c in 'xz' for i in V if i!=1]+[f's1_{i}{j}' for i,j in sorted(MISSING)]
for label,row in WITNESSES.items():
 a,q=(None,None) if label=='hex' else next((a,q) for a,q in rep if ''.join(map(str,a))==label)
 w=F(3,4) if a is None else 10**12;scale=F(1) if a is None else F(1,10**6)
 dct=dict(zip(names,map(F,row.split())));assert len(dct)==18
 off=[F(k,4)-F(a[1],4)+qq for k,qq in zip(a,q)] if a is not None else [F(0)]*8
 x={i:dct[f'x{i}'] if i!=1 else F(0) for i in V};zz={i:dct[f'z{i}'] if i!=1 else F(0) for i in V};b={i:off[i]+zz[i]*scale for i in V}
 if a is not None:
  for (i,j),c in phase(a,q)[0].items():assert abs(zz[j]-zz[i])<=c
  low=[[],[]];high=[[],[]];h=[b[i]-q[i] for i in V];eps=F(1,1000)
  for i,k in enumerate(a):
   if k%2==0:l=k//2;low[l].append((h[i]-eps,False));high[l].append((h[i]+eps,False))
   elif k==1:high[0].append((h[i]-eps,True));low[1].append((h[i]+eps,True))
   else:high[1].append((h[i]-eps,True));low[0].append((h[i]+eps-1,True))
  for k in (0,1):
   for (l,ls),(r,rs) in product(low[k],high[k]):assert l<r if ls or rs else l<=r
  for (l,_),(r,_) in product(low[0],high[1]):assert l+F(119,250)<r
  for (l,_),(r,_) in product(low[1],high[0]):assert l<r+F(131,250)
 def u(i,j,k):return (x[j]-x[i]+k[0]+F(k[1],2),b[j]-b[i]+k[1])
 def dnorm(i,j,k):
  X,B=u(i,j,k);return X*X+w*B*B
 d={}
 for i,j in combinations(V,2):
  if (i,j) in E:
   X,B=u(i,j,K[i,j]);assert abs(X)<F(1,2) and all(abs(B+sg*X/(2*w))<F(1,2)+F(1,8*w) for sg in (1,-1));d[i,j]=dnorm(i,j,K[i,j])
  else:
   d[i,j]=dnorm(i,j,(0,0))-2*dct[f's1_{i}{j}'];assert d[i,j]>0 and all(d[i,j]<=dnorm(i,j,k) for k in product(range(-1,2),repeat=2))
  d[j,i]=d[i,j]
 ar=[]
 for i,j,k in faces:
  X,B=u(i,j,K[i,j]);XX,BB=u(i,k,K[i,k]);ar.append(X*BB-XX*B)
 assert all(v<0 for v in ar) and sum(ar)==-2
 for v,c in links.items():
  S=lambda i,j:(dnorm(i,j,tuple(K[v,j][t]-K[v,i][t] for t in (0,1)))-d[i,j])/2
  aa=[S(c[i],c[(i+2)%7]) for i in range(7)];bb=[S(c[i],c[(i+3)%7]) for i in range(7)]
  assert min(aa)>=0 and min(bb)>0
  for i,j in combinations(c,2):
   gap=(c.index(j)-c.index(i))%7
   if gap in (1,6):assert S(i,j)==0
   elif tuple(sorted((i,j))) in E:assert S(i,j)>0
  for i in range(7):assert bb[i]*bb[(i+1)%7]>=bb[(i+4)%7]*aa[(i+1)%7] and aa[i]+aa[(i+1)%7]>0
 if a is not None:
  A=[i for i in V if a[i]==0];B=[i for i in V if a[i]==2]
  for i,j in combinations(A,2):
   for k,l in combinations(B,2):assert ((d[i,l]+d[j,k]-d[i,k]-d[j,l])/2)**2<=d[i,j]*d[k,l]
 print(label,'PASS exact quadratic relaxation (not a metric realization)')
