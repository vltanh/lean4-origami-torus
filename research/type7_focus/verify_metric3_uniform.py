#!/usr/bin/env python3
"""Uniform exact contraction certificate for a NONEMBEDDED ray_3 metric
realization, every y>=10^6. Run with Python, SymPy, NumPy, assertions on.
NumPy supplies only an approximate preconditioner; every proof inequality
is checked with outward-rounded integer intervals."""
import os
os.environ['OPENBLAS_NUM_THREADS']='1'
import numpy as np
from fractions import Fraction as F
import sympy as s
import json
from pathlib import Path
from itertools import combinations,product
D=Path(__file__).resolve().parent.parent/'linking_checkpoint'
case=next(c for c in json.loads((D/'cases.json').read_text()) if c['file']=='t7_ray_3.smt2')
K={tuple(e['edge']):tuple(e['shift']) for e in case['edge_shifts']}
K.update({(j,i):(-m,-n) for (i,j),(m,n) in list(K.items())})
V=tuple(range(8)); Q=list(combinations(V,4))
faces=[tuple(map(int,f)) for f in json.loads((D/'lutz_faces.json').read_text())['7'].split()]
T={tuple(sorted(f)) for f in faces}
edges=sorted({e for f in T for e in combinations(f,2)})
assert set(K)=={e for i,j in edges for e in ((i,j),(j,i))}
assert all(sum(K[e][k] for e in ((a,b),(b,c),(c,a)))==0 for a,b,c in faces for k in (0,1))
def sign_lit(q,sg):
 return sg[Q.index(tuple(sorted(q)))]*(-1)**sum(a>b for a,b in combinations(q,2))
A=(0,1,4,5); B=(2,3,6,7); other=[i for i in V if i not in (0,2)]
tmax=F(1,10**12);t=s.Symbol('t')
xbase=[F(0)]*8;ybase=xbase.copy()
for R in ((0,2,4,6),(1,3,5,7)):
 for i,j in zip(R,R[1:]):
  m,n=K[i,j];xbase[j]=xbase[i]-m-F(n,2);ybase[j]=ybase[i]-F(1,2)-n
KX={(i,j):xbase[j]-xbase[i]+m+F(n,2) for (i,j),(m,n) in K.items()}
KY={(i,j):ybase[j]-ybase[i]+n for (i,j),(m,n) in K.items()}
assert all(KY[i,j]==0 if (i in B)==(j in B) else abs(KY[i,j])==F(1,2) for i,j in edges)
z=s.symbols('z0:32');xx=[0]+list(z[:7]);gg=[0]+list(z[7:14]);P={0:[0,0],2:[0,0]};rho={0:0,2:0}
for i,j in enumerate(other):P[j]=z[14+2*i:16+2*i];rho[j]=z[26+i]
c0=(xx[2]+KX[0,2])**2+2*KY[0,2]*gg[2]+t*gg[2]**2;den=1+4*t*c0
polys=[]
for i,j in edges:
 if (i,j)==(0,2):continue
 X=xx[j]-xx[i]+KX[i,j];dg=gg[j]-gg[i];dr=rho[j]-rho[i];L=int(j in B)-int(i in B)
 f=den*(sum((P[j][k]-P[i][k])**2 for k in (0,1))+L*dr+L*L*c0-X*X-2*KY[i,j]*dg-t*dg*dg)+t*dr*dr
 polys.append(s.Poly(f,*z,t))
assert len(polys)==23
X=lambda i,j:xx[j]-xx[i]+KX[i,j];Y=lambda i,j:KY[i,j]+t*(gg[j]-gg[i])
assert s.expand(sum(X(a,b)*Y(a,c)-X(a,c)*Y(a,b) for a,b,c in faces))==-2
center_int=[-26089016762695,219867705183,-24981133205763,189158914796,-26089016762695,203979102139,-24718377714140,6302448398414,-25719925554,5606783590039,75712663161,6244957924166,39733478840,5757028130088,-8246882319364,-24751277293403,-23368484000004,9434214458889,-646743305793,-2279899138903,5374350117742,23299173379904,478641589817,2571762107432,-24018608439872,7155277162726,7548050072468,-5743321240364,183788671920,5092658367647,-54484371136,-5672542646291]
center=[F(v,10**14) for v in center_int]
ix=[0,1,2,3,4,5,7,8,9,10,11,12,13,15,19,21,22,26,27,28,29,30,31]
J0=np.array([[float(p.diff(z[i]).eval(dict(zip(z,center))|{t:tmax})) for i in ix] for p in polys])
# Integer intervals; endpoints are multiples of 10^-45, rounded outwards.
S=10**45
class I:
 def __init__(self,x,y=None,raw=False):
  if isinstance(x,I):self.lo,self.hi=x.lo,x.hi;return
  if raw:self.lo,self.hi=x,y;return
  x=F(x);y=x if y is None else F(y);self.lo=x.numerator*S//x.denominator;self.hi=-((-y.numerator*S)//y.denominator)
 def __add__(a,b):
  b=I(b);return I(a.lo+b.lo,a.hi+b.hi,raw=True)
 __radd__=__add__
 def __neg__(a):return I(-a.hi,-a.lo,raw=True)
 def __sub__(a,b):return a+-I(b)
 def __rsub__(a,b):return I(b)+-a
 def __mul__(a,b):
  b=I(b);p=[a.lo*b.lo,a.lo*b.hi,a.hi*b.lo,a.hi*b.hi];return I(min(p)//S,-((-max(p))//S),raw=True)
 __rmul__=__mul__
 def __truediv__(a,b):
  b=I(b);assert b.lo*b.hi>0;return a*I(F(S,b.hi),F(S,b.lo))
 def __pow__(a,n):
  if n==0:return I(1)
  if n==2 and a.lo<=0<=a.hi:return I(0,-((-max(a.lo*a.lo,a.hi*a.hi))//S),raw=True)
  if n%2:return a*(a**(n-1))
  return (a**(n//2))**2 if n!=2 else a*a
 def mag(a):return F(max(abs(a.lo),abs(a.hi)),S)
 def __repr__(a):return str((a.lo/S,a.hi/S))
 def sign(a):return 1 if a.lo>0 else -1 if a.hi<0 else 0
def evaluate(poly,coords):
 out=I(0)
 for powers,c in poly.terms():
  u=I(F(c))
  for i,n in enumerate(powers):
   if n:u*=coords[i]**n
  out+=u
 return out
C=[[F(round(v*10**12),10**12) for v in row] for row in np.linalg.inv(J0)]
radius=F(1,10**8)
box=[I(v-radius,v+radius) if i in ix else I(v) for i,v in enumerate(center)]+[I(0,tmax)]
cp=list(map(I,center))+[I(0,tmax)]
f=[evaluate(p,cp) for p in polys]
err=max(sum(C[i][j]*f[j] for j in range(23)).mag() for i in range(23))
JI=[[evaluate(p.diff(z[i]),box) for i in ix] for p in polys]
contract=max(sum((int(i==k)-sum(C[i][j]*JI[j][k] for j in range(23))).mag() for k in range(23)) for i in range(23))
print('err',float(err),'contract',float(contract))
assert err<F(6,10**13) and contract<F(2,10**6) and err+contract*radius<radius
# For every fixed t in the interval, x->x-C*f(x,t) is a contraction
# of the box into itself. The norm bound also implies C is invertible.
print('PASS uniform contraction for 0<=t<=10^-12')
t=box[-1]
xx=[I(0)]+box[:7];gg=[I(0)]+box[7:14];P={0:[I(0),I(0)],2:[I(0),I(0)]};rho={0:I(0),2:I(0)}
for i,j in enumerate(other):P[j]=box[14+2*i:16+2*i];rho[j]=box[26+i]
c0=(xx[2]+KX[0,2])**2+2*KY[0,2]*gg[2]+t*gg[2]**2;den=1+4*t*c0;lam=t/den;assert den.lo>0
X=lambda i,j:xx[j]-xx[i]+KX[i,j];Y=lambda i,j:KY[i,j]+t*(gg[j]-gg[i]);sl=[]
for i,j in edges:
 sl.extend([I(F(1,2))+X(i,j),I(F(1,2))-X(i,j)])
 for a,b in product((-1,1),repeat=2):
  if a*KY[i,j]==-F(1,2):
   # cancel the common half-period and divide by positive t
   sl.append(F(1,8)+a*(gg[j]-gg[i])+b*X(i,j)/2)
  else:sl.append(F(1,2)+t/8+a*Y(i,j)+b*t*X(i,j)/2)
 if KY[i,j]==0:assert (gg[j]-gg[i]).mag()<F(7,4)
 else:assert (F(7,4)+2*KY[i,j]*(gg[j]-gg[i])).lo>0
assert all(a.lo>0 for a in sl)
print('PASS all fixed-phase localization and nearest-lift inequalities')
area=[X(a,b)*Y(a,c)-X(a,c)*Y(a,b) for a,b,c in faces]
assert all(a.hi<0 for a in area);print('min absolute face double area',min(-a.hi/S for a in area))
# Compare with all lattice translates. For |n|>3 the vertical term alone
# is enormous; for |m|>4 and |n|<=3 use the horizontal term alone.
for i in range(4):
 j=i+4;dd=sum((P[j][k]-P[i][k])**2 for k in (0,1))+lam*(rho[j]-rho[i])**2
 assert dd.lo>0 and dd.mag()<1
 assert (xx[j]-xx[i]+xbase[j]-xbase[i]).mag()<1
 assert (I(ybase[j]-ybase[i])+t*(gg[j]-gg[i])).mag()<2
 for m,n in product(range(-4,5),range(-3,4)):
  X0=xx[j]-xx[i]+xbase[j]-xbase[i]+m+F(n,2);Y0=ybase[j]-ybase[i]+n;dg=gg[j]-gg[i]
  diff=X0**2+2*Y0*dg+t*dg**2-dd
  if Y0:diff+=Y0**2/tmax
  assert diff.lo>0,(i,m,n,diff)
 print('nonedge squared distance',i,dd)
def determinant(rows):
 a,b,c=rows;return a[0]*(b[1]*c[2]-b[2]*c[1])-a[1]*(b[0]*c[2]-b[2]*c[0])+a[2]*(b[0]*c[1]-b[1]*c[0])
sg=[]
for S0 in Q:
 a,*rs=S0;rows=[[P[b][k]-P[a][k] for k in (0,1)]+[(int(b in B)-int(a in B))+2*lam*(rho[b]-rho[a])] for b in rs]
 if len(set(int(b in B) for b in S0))==1:
  # remove common positive factor 2*lambda for positive t
  for i,b in enumerate(rs):rows[i][2]=rho[b]-rho[a]
 sg.append(determinant(rows).sign())
assert all(sg)
print('sign model',''.join('+' if x>0 else '-' for x in sg))
crossings=[]
for a,b in edges:
 for tri in sorted(T):
  if {a,b}&set(tri):continue
  W=tuple(sorted((a,b)+tri));sigs=[(-1)**k*sign_lit(W[:k]+W[k+1:],sg) for k in range(5)]
  pos={i for i,d in zip(W,sigs) if d>0};neg=set(W)-pos
  if ({a,b}==pos and set(tri)==neg) or ({a,b}==neg and set(tri)==pos):crossings.append([(a,b),tri])
assert len(crossings)==20
# The same exact sign model satisfies the strict local support and mixed-side
# tests. Thus adding only those local geometric tests does not remove it.
for v in V:
 N={j for j in V if tuple(sorted((v,j))) in edges}
 for q in combinations(sorted(N),4):
  W=tuple(sorted((v,)+q))
  pos={j for k,j in enumerate(W) if (-1)**k*sign_lit(W[:k]+W[k+1:],sg)>0}
  assert pos!={v} and set(W)-pos!={v}
 assert any(v in f and len({sign_lit(f+(j,),sg) for j in N-set(f)})==2 for f in T)
print('PASS strict local support and mixed-side tests')
# Check unlinking of the two long alternating cycles for this witness.
a=(0,2,4,6); b=(1,3,5,7);link=0
for i in range(1,len(a)-1):
 tri=(a[0],a[i],a[i+1])
 for u,v in zip(b,b[1:]+b[:1]):
  W=tuple(sorted(tri+(u,v)))
  pos={j for k,j in enumerate(W) if (-1)**k*sign_lit(W[:k]+W[k+1:],sg)>0}
  if pos==set(tri) or set(W)-pos==set(tri):
   link+=sign_lit(tri+(v,),sg)
assert link==0
print('PASS alternating long rings unlinked in this NONEMBEDDED witness')
print('PASS all 70 affine minors nonzero; 20 certified edge-face crossings',crossings)
print('PASS uniform NONEMBEDDED exact metric witnesses for every y>=10^6')
