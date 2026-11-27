#!/usr/bin/env python3
"""Exact rational phase propagation and verification of the 19 rectangle relaxations."""
from generate import F,V,E,K,faces,rep,combinations,product,permutations,op,num,add,mul,sub,neg,det
from pathlib import Path
from math import isqrt
import sys
P=Path(__file__).resolve().parent
Y=10**6;Q=10**9

def up(t):
 t=F(t);return F(-((-t.numerator*Q)//t.denominator),Q)

def hypot(a):
 v=(a*a+F(1,4))*Q**2;k=isqrt(v.numerator//v.denominator)
 return F(k+int(k*k<v),Q)

def phase(a,q):
 t=[F(i,4) for i in a];bs=[t[i]-t[1]+q[i] for i in V]
 A=[i for i in V if a[i]==0];B=[i for i in V if a[i]==2];C=A+B
 ix={i:k for k,i in enumerate(C)};pairs=list(combinations(sorted(C),2))
 bounds={e:F(Y,500) if a[e[0]]==a[e[1]] else F(13*Y,500) for e in pairs}
 def get(i,j):return bounds[tuple(sorted((i,j)))] if i!=j else F(0)
 rect=[]
 for i,j in combinations(A,2):
  for k,l in combinations(B,2):
   if any(e not in K for e in [(i,k),(j,k),(i,l),(j,l)]):continue
   z=[0]*len(C)
   for ii,jj,sg in [(i,l,1),(j,k,1),(i,k,-1),(j,l,-1)]:
    dis=bs[jj]-bs[ii]+K[ii,jj][1];assert abs(dis)==F(1,2);sig=1 if dis>0 else -1
    z[ix[ii]]-=sg*sig;z[ix[jj]]+=sg*sig
   if any(z):rect.append(((i,j,k,l),tuple(z)))
 for sweep in range(12):
  old=bounds.copy();rr=[]
  for (i,j,k,l),z in rect:
   av,bv=get(i,j),get(k,l)
   rr.append((up(2*(hypot(av)*hypot(bv)+av*bv+F(1,4))/Y),z))
  for i,j in pairs:
   z=[0]*len(C);z[ix[j]]=1;z[ix[i]]=-1;rr.append((get(i,j),tuple(z)))
  basis=[];costs=[];raw=[]
  for r,z in sorted(rr):
   vec=list(map(F,z));coeff=[F(0)]*len(basis)
   for pivot,v,cv in basis:
    c=vec[pivot]
    if c:
     vec=[a-c*b for a,b in zip(vec,v)]
     for j,cj in enumerate(cv):coeff[j]+=c*cj
   if not any(vec):continue
   p=next(k for k,z in enumerate(vec) if z);div=vec[p]
   cv=[-c/div for c in coeff]+[1/div];v=[z/div for z in vec]
   raw.append(z);costs.append(r)
   assert [sum(c*row[k] for c,row in zip(cv,raw)) for k in range(len(C))]==v
   basis.append((p,v,cv))
   if len(basis)==len(C)-1:break
  assert len(costs)==len(C)-1
  for i,j in pairs:
   z=[F(0)]*len(C);z[ix[j]]=1;z[ix[i]]=-1;target=z[:];coef=[F(0)]*len(basis)
   for pivot,v,cv in basis:
    c=z[pivot];z=[a-c*b for a,b in zip(z,v)]
    for k,ck in enumerate(cv):coef[k]+=c*ck
   assert not any(z)
   assert [sum(c*row[k] for c,row in zip(coef,raw)) for k in range(len(C))]==target
   bounds[i,j]=min(bounds[i,j],up(sum(abs(c)*r for c,r in zip(coef,costs))))
  for k in C:
   for i,j in pairs:bounds[i,j]=min(bounds[i,j],get(i,k)+get(k,j))
  if bounds==old:break
 return bounds,rect

def localization(a,values):
 # The same two-center projection, in physical vertical units.
 low=[[],[]];high=[[],[]];eps=F(Y,1000)
 for i,k in enumerate(a):
  h=values[i]
  if k%2==0:
   l=k//2;low[l].append((h-eps,False));high[l].append((h+eps,False))
  elif k==1:
   high[0].append((h-eps,True));low[1].append((h+eps,True))
  else:
   high[1].append((h-eps,True));low[0].append((h+eps-Y,True))
 return low,high

def verify(a,q,values):
 x=dict(zip((0,2,3,4,5,6,7),values[:7]));z=dict(zip((0,2,3,4,5,6,7),values[7:]));x[1]=z[1]=F(0)
 t=[F(i,4) for i in a];b={i:Y*(t[i]-t[1]+q[i])+z[i] for i in V}
 Bnd,rect=phase(a,q)
 for (i,j),c in Bnd.items():assert abs(z[j]-z[i])<=c
 low,high=localization(a,[b[i]-Y*q[i] for i in V])
 for k in (0,1):
  for (l,ls),(r,rs) in product(low[k],high[k]):assert l<r if ls or rs else l<=r
 for (l,_),(r,_) in product(low[0],high[1]):assert l+F(119*Y,250)<r
 for (l,_),(r,_) in product(low[1],high[0]):assert l<r+F(131*Y,250)
 def X(i,j):return x[j]-x[i]+F(K[i,j][0])+F(K[i,j][1],2)
 def Yd(i,j):return b[j]-b[i]+Y*K[i,j][1]
 def d(i,j):return X(i,j)**2+Yd(i,j)**2
 for i,j in E:
  assert abs(X(i,j))<F(1,2)
  for sg in (1,-1):assert abs(Yd(i,j)+sg*X(i,j)/(2*Y))<F(Y,2)+F(1,8*Y)
 areas=[X(i,j)*Yd(i,k)-X(i,k)*Yd(i,j) for i,j,k in faces];assert max(areas)<0 and sum(areas)==-2*Y
 def capdist(i,j):return d(i,j) if (i,j) in K else F(1,4)+(z[j]-z[i])**2
 A=[i for i in V if a[i]==0];B=[i for i in V if a[i]==2];n=0
 for i,j in combinations(A,2):
  for k,l in combinations(B,2):
   if any(e not in K for e in [(i,k),(i,l),(j,k),(j,l)]):continue
   H=(d(i,l)+d(j,k)-d(i,k)-d(j,l))/2
   assert H*H<=capdist(i,j)*capdist(k,l),(i,j,k,l)
   n+=1
 return n

def generate(a,q,mode='gram'):
 lines=['(set-logic QF_NRA)'];defn=lambda n,e:lines.append(f'(define-fun {n} () Real {e})') or n
 decl=lambda n:lines.append(f'(declare-fun {n} () Real)') or n
 ass=lambda e:lines.append(op('assert',e))
 sq=lambda a:mul(a,a)
 Bnd,rect=phase(a,q)
 x={i:'0' if i==1 else decl(f'x{i}') for i in V};z={i:'0' if i==1 else decl(f'z{i}') for i in V}
 t=[F(i,4) for i in a];offs=[Y*(t[i]-t[1]+q[i]) for i in V]
 b={i:defn(f'b{i}',add(z[i],num(offs[i]))) for i in V}
 for (i,j),c in Bnd.items():
  h=sub(z[j],z[i]);ass(op('<=',neg(num(c)),h));ass(op('<=',h,num(c)))
 h=[sub(b[i],num(Y*q[i])) for i in V];low=[[],[]];high=[[],[]];eps=F(Y,1000)
 for i,k in enumerate(a):
  if k%2==0:
   l=k//2;low[l].append((sub(h[i],num(eps)),False));high[l].append((add(h[i],num(eps)),False))
  elif k==1:
   high[0].append((sub(h[i],num(eps)),True));low[1].append((add(h[i],num(eps)),True))
  else:
   high[1].append((sub(h[i],num(eps)),True));low[0].append((add(h[i],num(eps-Y)),True))
 for k in (0,1):
  for (l,ls),(r,rs) in product(low[k],high[k]):ass(op('<' if ls or rs else '<=',l,r))
 for (l,_),(r,_) in product(low[0],high[1]):ass(op('<',add(l,num(F(119*Y,250))),r))
 for (l,_),(r,_) in product(low[1],high[0]):ass(op('<',l,add(r,num(F(131*Y,250)))))
 def dx(i,j,k):return add(sub(x[j],x[i]),num(F(k[0])+F(k[1],2)))
 def dy(i,j,k):return add(sub(z[j],z[i]),num(offs[j]-offs[i]+Y*k[1]))
 d={};U={}
 for i,j in E:
  X=defn(f'X{i}{j}',dx(i,j,K[i,j]));B=defn(f'Y{i}{j}',dy(i,j,K[i,j]))
  U[i,j]=(X,B);U[j,i]=(neg(X),neg(B));d[i,j]=d[j,i]=defn(f'd{i}{j}',add(sq(X),sq(B)))
  ass(op('<',num(-F(1,2)),X));ass(op('<',X,num(F(1,2))))
  for sg in (1,-1):
   v=add(mul(num(F(sg,2*Y)),X),B);bound=num(F(Y,2)+F(1,8*Y));ass(op('<',neg(bound),v));ass(op('<',v,bound))
 for i,j,k in faces:
  X,B=U[i,j];X2,B2=U[i,k];ass(op('<',sub(mul(X,B2),mul(X2,B)),'0'))
 for i in V:d[i,i]='0'
 def capdist(i,j):
  if (i,j) in K:return d[i,j]
  return add(num(F(1,4)),sq(sub(z[j],z[i])))
 A=[i for i in V if a[i]==0];B=[i for i in V if a[i]==2]
 for i,j in combinations(A,2):
  for k,l in combinations(B,2):
   if any(e not in K for e in [(i,k),(i,l),(j,k),(j,l)]):continue
   H=defn(f'R{i}{j}{k}{l}',mul(num(F(1,2)),sub(add(d[i,l],d[j,k]),add(d[i,k],d[j,l]))))
   ass(op('<=',sq(H),mul(capdist(i,j),capdist(k,l))))
 if mode!='rect':
  G={(i,j):defn(f'g{i}{j}',mul(num(F(1,2)),sub(add(d[1,i],d[1,j]),d[i,j]))) for i in V if i!=1 for j in V if j!=1 and i<=j and ((i,j) in K)}
  G.update({(j,i):v for (i,j),v in list(G.items())})
  for i in (2,5):ass(op('>',G[i,i],'0'))
  for i in (0,3,4,6,7):
   I=(2,5,i);ass(op('>',det([[G[j,k] for k in I] for j in I]),'0'))
  for i,j in [(3,j) for j in (0,6,7)]+[(4,0)]:
   I=(2,5,i,j);ass(op('=',det([[G[u,v] for v in I] for u in I]),'0'))
  for j in (6,7):ass(op('=',det([[G[u,v] for v in (2,5,0,j)] for u in (2,5,3,4)]),'0'))
 lines.append('(check-sat)');return '\n'.join(lines)+'\n'

if __name__=='__main__':
 import json
 data=json.loads((P/'phase_witnesses.json').read_text())
 assert set(data)=={''.join(map(str,a)) for a,q in rep}
 for a,q in sorted(rep):
  label=''.join(map(str,a));Bnd,_=phase(a,q);n=verify(a,q,list(map(F,data[label])))
  print(label,'PASS',n,'rectangles; min cross-phase bound',min(v for (i,j),v in Bnd.items() if a[i]!=a[j]),flush=True)
 print('PASS exact rational witnesses for all 19 rectangle relaxations; not Gram feasibility or embeddings')
 if len(sys.argv)>1:
  out=Path(sys.argv[1]);mode=sys.argv[2] if len(sys.argv)>2 else 'gram';assert mode in ('rect','gram');out.mkdir(parents=True,exist_ok=True)
  for a,q in sorted(rep):
   label=''.join(map(str,a));(out/(label+'.smt2')).write_text(generate(a,q,mode))
