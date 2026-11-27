#!/usr/bin/env python3
"""Affine signed-Gram pivot for Type 5. Exact rational coefficients.
Default cubic metric relaxation; --full adds all simplex intersections.
"""
from generate import F,V,E,K,faces,rep,combinations,product,permutations,op,num,add,mul,sub,neg,det
from phase import phase
from pathlib import Path
import sys
P=Path(__file__).resolve().parent
MISSING=set(combinations(V,2))-set(E)
G=lambda v,i,j:tuple(K[i,j][t]+K[v,i][t]-K[v,j][t] for t in (0,1))
links={}
for v in (1,2,5):
 lk={j:[] for j in V if j!=v}
 for f in faces:
  if v in f:
   a,b=[i for i in f if i!=v];lk[a].append(b);lk[b].append(a)
 c=[min(lk),lk[min(lk)][0]]
 while len(c)<7:c.append(next(i for i in lk[c[-1]] if i!=c[-2]))
 assert len(set(c))==7 and c[0] in lk[c[-1]]
 links[v]=c
 for i,j in E:
  if v not in (i,j):assert (G(v,i,j)==(0,0))==((c.index(i)-c.index(j))%7 in (1,6))
 for i,j in combinations(c,2):
  if (c.index(j)-c.index(i))%7 not in (3,4) or tuple(sorted((i,j))) in E:continue
  for s in (1,-1):
   ix=c.index(i);p=[i]
   while p[-1]!=j:ix=(ix+s)%7;p.append(c[ix])
   assert any(tuple(sorted((k,l))) in E and G(v,k,l)!=(0,0) for k,l in combinations(p,2))
for i,j in MISSING:assert len({tuple(K[v,j][t]-K[v,i][t] for t in (0,1)) for v in links})==3
B0=(2,5,7,4);O=(0,3,6,8,9)
assert {tuple(sorted(e)) for e in combinations((1,)+B0,2)}<=set(E)
assert {tuple(sorted(e)) for e in combinations(B0,2) if K[e]!=(0,0)}=={(2,7),(2,4),(4,5)}

def generate(a=None,q=None,w=10**12,mode='cubic',full=False,extra=False):
 lines=['(set-logic QF_NRA)'];defn=lambda n,e:lines.append(f'(define-fun {n} () Real {e})') or n
 decl=lambda n:lines.append(f'(declare-fun {n} () Real)') or n
 ass=lambda e:lines.append(op('assert',e))
 sq=lambda a:mul(a,a)
 x={i:'0' if i==1 else decl(f'x{i}') for i in V};z={i:'0' if i==1 else decl(f'z{i}') for i in V}
 scale=F(1)
 if a is not None:
  assert w==10**12;scale=F(1,10**6);offs=[F(i-a[1],4)+qj for i,qj in zip(a,q)]
 else:offs=[F(0)]*8
 b={i:defn(f'b{i}',add(mul(num(scale),z[i]),num(offs[i]))) for i in V}
 def dx(i,j,k):return add(sub(x[j],x[i]),num(F(k[0])+F(k[1],2)))
 def dy(i,j,k):return add(sub(b[j],b[i]),num(k[1]))
 def norm(i,j,k):return add(sq(dx(i,j,k)),mul(num(w),sq(dy(i,j,k))))
 def delta(i,j,k):return add(mul(num(k[0]+F(k[1],2)),sub(x[j],x[i])),mul(num(w*k[1]),sub(b[j],b[i])),num((F(k[0])+F(k[1],2))**2/2+F(w*k[1]**2,2)))
 if a is not None:
  Bnd,_=phase(a,q)
  for (i,j),c in Bnd.items():
   h=sub(z[j],z[i]);ass(op('<=',neg(num(c)),h));ass(op('<=',h,num(c)))
  h=[sub(b[i],num(q[i])) for i in V];low=[[],[]];high=[[],[]];eps=F(1,1000)
  for i,k in enumerate(a):
   if k%2==0:
    l=k//2;low[l].append((sub(h[i],num(eps)),False));high[l].append((add(h[i],num(eps)),False))
   elif k==1:high[0].append((sub(h[i],num(eps)),True));low[1].append((add(h[i],num(eps)),True))
   else:high[1].append((sub(h[i],num(eps)),True));low[0].append((add(h[i],num(eps-1)),True))
  for k in (0,1):
   for (l,ls),(r,rs) in product(low[k],high[k]):ass(op('<' if ls or rs else '<=',l,r))
  for (l,_),(r,_) in product(low[0],high[1]):ass(op('<',add(l,num(F(119,250))),r))
  for (l,_),(r,_) in product(low[1],high[0]):ass(op('<',l,add(r,num(F(131,250)))))
 d={};U={};S0={}
 for i,j in E:
  X=defn(f'X{i}{j}',dx(i,j,K[i,j]));B=defn(f'Y{i}{j}',dy(i,j,K[i,j]));U[i,j]=(X,B);U[j,i]=(neg(X),neg(B));d[i,j]=d[j,i]=defn(f'd{i}{j}',norm(i,j,K[i,j]));S0[i,j]=S0[j,i]=defn(f's1_{i}{j}',neg(delta(i,j,K[i,j])))
  ass(op('<',num(-F(1,2)),X));ass(op('<',X,num(F(1,2))))
  for sg in (1,-1):
   vv=add(mul(num(F(sg,2*w)),X),B);bound=num(F(1,2)+F(1,8*w));ass(op('<',neg(bound),vv));ass(op('<',vv,bound))
 areas=[]
 for i,j,k in faces:
  X,B=U[i,j];X2,B2=U[i,k];areas.append(sub(mul(X,B2),mul(X2,B)));ass(op('<',areas[-1],'0'))
 ass(op('=',add(*areas),num(-2)))
 for i,j in sorted(MISSING):
  S0[i,j]=S0[j,i]=decl(f's1_{i}{j}');d[i,j]=d[j,i]=defn(f'd{i}{j}',sub(norm(i,j,(0,0)),mul('2',S0[i,j])));ass(op('>',d[i,j],'0'))
  for k in product(range(-1,2),repeat=2):ass(op('>=',add(S0[i,j],delta(i,j,k)),'0'))
 for i in V:d[i,i]='0';S0[i,i]='0'
 VS={}
 for v,c in links.items():
  SS={};VS[v]=SS
  for i,j in combinations(sorted(c),2):
   k=tuple(K[v,j][t]-K[v,i][t] for t in (0,1));s=defn(f's{v}_{i}{j}',add(S0[i,j],delta(i,j,k))) if v!=1 else S0[i,j];SS[i,j]=SS[j,i]=s
   gap=(c.index(j)-c.index(i))%7
   if gap in (1,6):continue
   ass(op('>' if gap in (3,4) or (i,j) in E else '>=',s,'0'))
  aa=[SS[c[i],c[(i+2)%7]] for i in range(7)];bb=[SS[c[i],c[(i+3)%7]] for i in range(7)]
  for i in range(7):
   ass(op('>=',mul(bb[i],bb[(i+1)%7]),mul(bb[(i+4)%7],aa[(i+1)%7])))
   ass(op('>',add(aa[i],aa[(i+1)%7]),'0'))
  if mode=='rank':
   for i in c:SS[i,i]='0'
   for I in combinations(c,6):ass(op('=',det([[SS[i,j] for j in I] for i in I]),'0'))
 if extra:
  for i,j in sorted(MISSING):
   for v,k in combinations(links,2):ass(op('>',add(VS[v][i,j],VS[k][i,j]),'0'))
 if mode=='cubic':
  A0=S0[2,7];B1=S0[2,4];C0=S0[5,4];ac=defn('ac',mul(A0,C0));ass(op('>',A0,'0'));ass(op('>',C0,'0'))
  def H(i,j):
   if i<8 and j<8:return S0[i,j]
   if i>=8 and j>=8:return ('(- 1)' if i==8 else num(-F(1,w))) if i==j else '0'
   if i>=8:i,j=j,i
   return x[i] if j==8 else b[i]
  u={i:decl(f'u{i}') for i in O}
  ass(op('>',add(sq(u[8]),sq(u[9])) if extra else add(*(sq(u[i]) for i in O)),'0'))
  for ii,i in enumerate(O):
   for j in O[ii:]:
    terms=[]
    for k,l,c in [(2,7,C0),(5,7,neg(B1)),(5,4,A0)]:terms.append(mul(c,add(mul(H(k,i),H(l,j)),mul(H(l,i),H(k,j)))))
    R=defn(f'res{i}{j}',sub(mul(ac,H(i,j)),add(*terms)));ass(op('=',R,mul(u[i],u[j])))
  if full:
   T={i:[H(k,i) for k in B0]+[u.get(i,'0')] for i in tuple(V)+(8,9)}
   C={i:[defn(f'C{i}{k}',add(T[i][k],mul(x[i],T[8][k]),mul(num(w),b[i],T[9][k]))) for k in range(5)] for i in V}
   Q=tuple(combinations(V,4));simplex={(i,) for i in V}|set(E)|{tuple(sorted(f)) for f in faces};minors={}
   def aff(S,axes):
    key=(S,axes)
    if key not in minors:minors[key]=defn('D'+''.join(map(str,S))+'c'+''.join(map(str,axes)),det([[sub(C[i][k],C[S[0]][k]) for k in axes] for i in S[1:]]))
    return minors[key]
   def any_(L):return 'false' if not L else op('or',*L)
   def all_(L):return 'true' if not L else op('and',*L)
   for S in Q:
    if all(e in E for e in combinations(S,2)):ass(any_([op('distinct',aff(S,ax),'0') for ax in combinations(range(5),3)]))
   for n in range(2,6):
    for S in combinations(V,n):
     parts=[]
     for k in range(1,min(3,n-1)+1):
      for A in combinations(S,k):
       if S[0] in A and A in simplex and tuple(i for i in S if i not in A) in simplex:parts.append(A)
     if not parts:continue
     if n==2:ass(any_([op('distinct',C[S[0]][k],C[S[1]][k]) for k in range(5)]));continue
     rank=all_([op('=',aff(S,ax),'0') for ax in combinations(range(5),n-1)]) if n<=4 else 'true'
     for A in parts:
      tests=[]
      for ax in combinations(range(5),n-2):
       coeff=[aff(S[:i]+S[i+1:],ax) for i in range(n)];ss=[c if ((i%2==0)==(v in A)) else neg(c) for i,(c,v) in enumerate(zip(coeff,S))]
       tests.append(any_([all_([op('>',s,'0') for s in ss]),all_([op('<',s,'0') for s in ss])]))
      ass(op('not',all_([rank,any_(tests)])))
 if a is not None:
  A=[i for i in V if a[i]==0];B=[i for i in V if a[i]==2]
  for i,j in combinations(A,2):
   for k,l in combinations(B,2):
    H=defn(f'R{i}{j}{k}{l}',mul(num(F(1,2)),sub(add(d[i,l],d[j,k]),add(d[i,k],d[j,l]))));ass(op('<=',sq(H),mul(d[i,j],d[k,l])))
 lines.append('(check-sat)');return '\n'.join(lines)+'\n'
if __name__=='__main__':
 full='--full' in sys.argv;extra='--extra' in sys.argv;args=[x for x in sys.argv[1:] if x not in ('--full','--extra')];out=Path(args[0]) if args else P/'cubic_systems';mode=args[1] if len(args)>1 else 'cubic';assert mode in ('quad','rank','cubic') and (not full or mode=='cubic');out.mkdir(exist_ok=True,parents=True)
 (out/'hex.smt2').write_text(generate(w=F(3,4),mode=mode,full=full,extra=extra))
 for a,q in sorted(rep):
  name=''.join(map(str,a));(out/(name+'.smt2')).write_text(generate(a,q,mode=mode,full=full,extra=extra))
 print('PASS combinatorial checks; generated 19 elongated and one hex system:',mode,full,extra)
