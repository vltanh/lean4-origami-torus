#!/usr/bin/env python3
"""B1.1 common-sign core system. Rational coefficient, univariate leaves.
The --eliminate mode eliminates each leaf independently (necessary relaxation);
the default uses 3 explicit line parameters, retaining all common signs and
metric contraction for missing edges. See README for scope.
"""
from pathlib import Path
import sys,json,itertools as it,argparse
P=Path(__file__).resolve().parent
sys.path.insert(0,str(P.parent.parent))
import focused_system as fs
from satgeom import Q,lit
from generate_base import add,mul,sub,neg,num,rat,op,all_,any_,determinant
A=[1,2,5];R=[3,4];L=[0,6,7];C=set(A+R)
ch=json.loads((P.parent/'branches.json').read_text())[0];assert ch['id']=='B1.1';anchor=lit((1,2,5,3))
S=[]
for pat in ch['chambers']:
 s=[1 if v=='+' else -1 for v in pat];d=s[abs(anchor)-1]*(1 if anchor>0 else -1);S.append([x*d for x in s])
common={q:S[0][i] for i,q in enumerate(Q) if all(s[i]==S[0][i] for s in S)};assert len(common)==64 and all(q in common for q in fs.cl)

def gen(eliminate=False,leaves=(0,6,7),allch=False):
 lines=['(set-logic QF_NRA)'];counter=0
 def decl(n):lines.append(f'(declare-fun {n} () Real)');return n
 def define(n,e):lines.append(f'(define-fun {n} () Real {e})');return n
 def aux(e):
  nonlocal counter
  counter+=1;return define(f'aux{counter}',e)
 def ass(e):lines.append(op('assert',e))
 def vadd(a,b):return [add(x,y) for x,y in zip(a,b)]
 def vsub(a,b):return [sub(x,y) for x,y in zip(a,b)]
 def sc(k,a):return [mul(k,x) for x in a]
 def dot(a,b):return add(mul(a[0],b[0]),mul('3',a[1],b[1]))
 def cross(a,b):return sub(mul(a[0],b[1]),mul(a[1],b[0]))
 def dot2(a,b):return add(*(mul(x,y) for x,y in zip(a,b)))
 def norm(a):return dot(a,a)
 def kvec(i,j):
  a,b=fs.K[i,j];return [rat(2*a+b,2),rat(b,2)]
 def gram(i,j,pp,N='1'):
  # j may be a leaf with coordinate P/N; output N*g_ij.
  k=kvec(i,j);return sub(add(dot(p[i],pp),mul(N,dot(p[i],k))),add(dot(pp,k),mul(N,'(/ 1 2)',norm(k))))
 p={1:['0','0']};p.update({i:[decl(f'p{i}{j}') for j in range(2)] for i in (2,3,4,5)})
 h11=define('h11',norm(p[2]));h12=define('h12',dot(p[2],p[5]));h22=define('h22',norm(p[5]));D=define('D',sub(mul(h11,h22),mul(h12,h12)))
 ass(op('>',cross(p[2],p[5]),'0'));ass(op('>',D,'0'))
 def adj(b):return [sub(mul(h22,b[0]),mul(h12,b[1])),sub(mul(h11,b[1]),mul(h12,b[0]))]
 b={i:[define(f'b{i}{j}',gram(a,i,p[i])) for j,a in enumerate((2,5))] for i in R}
 u={i:[define(f'u{i}{j}',x) for j,x in enumerate(adj(b[i]))] for i in R}
 h={i:define(f'H{i}',sub(mul(D,norm(p[i])),dot2(b[i],u[i]))) for i in R}
 for i in R:ass(op('>',h[i],'0'))
 t=decl('t');ass(op('>',t,'0'));ass(op('=',h[4],mul(t,t,h[3])))
 # Extrinsic affine coordinates, scaled horizontally by D and vertically by H3/z3.
 r={1:['0','0','0'],2:[D,'0','0'],5:['0',D,'0'],3:u[3]+[h[3]],4:u[4]+[neg(mul(t,h[3]))]}
 # All core constraints: nearest, oriented faces, common determinant signs.
 def near(i,j,Pj,Pi,N):
  d=vadd(vsub(Pj,Pi),sc(N,kvec(i,j)));ans=[]
  for a,b0 in ((1,0),(0,1),(-1,1)):
   expr=add(mul(num(2*a+b0),d[0]),mul(num(3*b0),d[1]));ans.extend([(sub(N,expr),True),(add(N,expr),True)])
  return ans
 def area(f,pp,N):
  a,b0,c=f;return neg(cross(vadd(vsub(pp[b0],pp[a]),sc(N,kvec(a,b0))),vadd(vsub(pp[c],pp[a]),sc(N,kvec(a,c)))))
 def orient(q,rr):
  a,*rs=q;v=determinant([vsub(rr[i],rr[a]) for i in rs]);return v if common[q]>0 else neg(v)
 for i,j in fs.E:
  if {i,j}<=C:
   for e,s in near(i,j,p[j],p[i],'1'):ass(op('>',e,'0'))
 for f in fs.F:
  if set(f)<=C:ass(op('>',area(f,p,'1'),'0'))
 for q in common:
  if set(q)<=C:ass(op('>' if q in fs.cl else '>=',orient(q,r),'0'))
 # core nonedge 34 and pairwise missing edges: use contraction in dot product form.
 def contraction(i,j,Pi,Pj,Ni,Nj,Ui,Uj,Zi,Zj):
  # physical r_i dot r_j = (b_i^T adjH b_j + Zi*Zj/H3)/(D*Ni*Nj).
  # reconstruct b_i from U_i using H, or use U_i^T H U_j / D.
  proj=add(mul(h11,Ui[0],Uj[0]),mul(h12,Ui[0],Uj[1]),mul(h12,Ui[1],Uj[0]),mul(h22,Ui[1],Uj[1]))
  left=add(mul(h[3],proj),mul(D,Zi,Zj));den=mul(D,D,h[3]);ans=[]
  for aa,bb in it.product(range(-1,2),repeat=2):
   k=[rat(2*aa+bb,2),rat(bb,2)];g=sub(add(dot(Pi,Pj),mul(Nj,dot(Pi,k))),add(mul(Ni,dot(Pj,k)),mul(Ni,Nj,'(/ 1 2)',norm(k))))
   ans.append(sub(left,mul(den,g)))
  return ans
 for e in contraction(3,4,p[3],p[4],'1','1',u[3],u[4],r[3][2],r[4][2]):ass(op('>=',e,'0'))
 def leafdata(j,Pj,N):
  bb=[gram(a,j,Pj,N) for a in (2,5)];uu=adj(bb)
  cc={i:sub(mul(D,gram(i,j,Pj,N)),dot2(b[i],uu)) for i in R}
  hh=sub(mul(D,norm(Pj)),dot2(bb,uu))
  return uu,cc,hh
 def leaf_equation(j,Pj,N):
  _,cc,_=leafdata(j,Pj,N);return add(cc[4],mul(t,cc[3]))
 def leaf_line(j):
  c=define(f'l{j}c',leaf_equation(j,['0','0'],'1'))
  a=define(f'l{j}a',sub(leaf_equation(j,['1','0'],'1'),c));bb=define(f'l{j}b',sub(leaf_equation(j,['0','1'],'1'),c));n=define(f'l{j}N',add(mul(a,a),mul(bb,bb)))
  ass(op('>',n,'0'));return a,bb,c,n
 def eval_leaf(j,s,a,bb,c,n,cons=True):
  ppj=[sub(neg(mul(a,c)),mul(bb,s)),add(neg(mul(bb,c)),mul(a,s))]
  uu,cc,hh=leafdata(j,ppj,n);rrj=uu+[cc[3]]
  q=sub(mul(h[3],hh),mul(cc[3],cc[3]))
  if not cons:return q,ppj,rrj
  pp={i:sc(n,v) for i,v in p.items()};pp[j]=ppj
  rr={i:sc(n,v) for i,v in r.items()};rr[j]=rrj
  checks=[]
  for i,k in fs.E:
   if j in (i,k):checks.extend(near(i,k,pp[k],pp[i],n))
  for f in fs.F:
   if j in f:checks.append((area(f,pp,n),True))
  for S in common:
   if j in S and set(S)-{j}<=C:checks.append((orient(S,rr),S in fs.cl))
  return q,checks,ppj,rrj
 def sign_rad(x,y,d,strict):
  pos=lambda z:op('>',z,'0');non=lambda z:op('>=',z,'0');less=lambda z:op('<',z,'0');zero=lambda z:op('=',z,'0')
  dd=mul(y,y,d);xx=mul(x,x);cmp='>' if strict else '>='
  out=[all_([pos(x) if strict else non(x),non(y)]),all_([less(x),pos(y),op(cmp,dd,xx)]),all_([pos(x) if strict else non(x),less(y),op(cmp,xx,dd)])]
  if strict:out.append(all_([zero(x),pos(y),pos(d)]))
  return any_(out)
 nump={i:p[i] for i in C};numr={i:r[i] for i in C};denom={i:'1' for i in C}
 for j in leaves:
  a,bb,c,n=leaf_line(j)
  if not eliminate:
   s=decl(f's{j}');q,checks,ppj,rrj=eval_leaf(j,s,a,bb,c,n)
   ass(op('=',q,'0'))
   for e,st in checks:ass(op('>' if st else '>=',e,'0'))
   nump[j]=[define(f'P{j}{k}',v) for k,v in enumerate(ppj)];numr[j]=[define(f'R{j}{k}',v) for k,v in enumerate(rrj)];denom[j]=n
  else:
   # Interpolate exact quadratic and affine polynomials in s; no leaf variable.
   e0=eval_leaf(j,'0',a,bb,c,n);ep=eval_leaf(j,'1',a,bb,c,n);em=eval_leaf(j,'(- 1)',a,bb,c,n)
   Cq=define(f'q{j}C',e0[0]);Aq=define(f'q{j}A',mul('(/ 1 2)',sub(add(ep[0],em[0]),mul('2',Cq))));Bq=define(f'q{j}B',mul('(/ 1 2)',sub(ep[0],em[0])));disc=define(f'q{j}disc',sub(mul(Bq,Bq),mul('4',Aq,Cq)))
   lc=[]
   for (v,st),(vp,stp) in zip(e0[1],ep[1]):
    assert st==stp;beta=aux(v);alpha=aux(sub(vp,beta));lc.append((alpha,beta,st))
   root=[]
   for sgn in (1,-1):
    checks=[]
    for al,be,st in lc:
     x=aux(mul(Aq,sub(mul('2',Aq,be),mul(Bq,al))));y=aux(mul(num(sgn),Aq,al));checks.append(sign_rad(x,y,disc,st))
    root.append(all_(checks))
   lin=[op('>' if st else '>=',mul(Bq,sub(mul(Bq,be),mul(Cq,al))),'0') for al,be,st in lc]
   # Allow identically-zero quadratic as a conservative relaxation, rather than rely on its prior exclusion.
   ass(any_([all_([op('distinct',Aq,'0'),op('>=',disc,'0'),any_(root)]),all_([op('=',Aq,'0'),op('distinct',Bq,'0'),all_(lin)]),all_([op('=',Aq,'0'),op('=',Bq,'0'),op('=',Cq,'0')])]))
 if not eliminate:
  # Remaining sign constraints involving two or more leaves; scale all coordinates by common positive denominator.
  V=C|set(leaves)
  for q in common:
   if len(set(q)-C)>=2 and set(q)<=V:
    rr={i:sc(mul(*(denom[k] for k in q if k!=i)),numr[i]) for i in q};ass(op('>' if q in fs.cl else '>=',orient(q,rr),'0'))
  # All pairwise missing distances that involve two leaves; the core pair was already included.
  for i,j in it.combinations(leaves,2):
   for e in contraction(i,j,nump[i],nump[j],denom[i],denom[j],numr[i][:2],numr[j][:2],numr[i][2],numr[j][2]):ass(op('>=',e,'0'))
  if allch:
   assert set(leaves)==set(L)
   def d(q):
    rr={i:sc(mul(*(denom[k] for k in q if k!=i)),numr[i]) for i in q};a,*b=q;return aux(determinant([vsub(rr[i],rr[a]) for i in b]))
   v={q:d(q) for q in Q if q not in common};ass(any_([all_([op('>=' if s[Q.index(q)]==1 else '<=',e,'0') for q,e in v.items()]) for s in S]))
 lines.append('(check-sat)');return '\n'.join(lines)+'\n'

if __name__=='__main__':
 ap=argparse.ArgumentParser();ap.add_argument('--eliminate',action='store_true');ap.add_argument('--leaves',default='0,6,7');ap.add_argument('--allch',action='store_true');a=ap.parse_args();leaves=tuple(int(x) for x in a.leaves.split(',') if x);s=gen(a.eliminate,leaves,a.allch);path=P/('core_'+('_'.join(map(str,leaves)) or 'none')+('_elim' if a.eliminate else '')+('_ch' if a.allch else '')+'.smt2');path.write_text(s);print(path,len(s),'bytes',s.count('(declare-fun'),'variables')
