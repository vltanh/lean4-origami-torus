#!/usr/bin/env python3
"""Exact finite sharp-ray Type 4 systems; import cell enumeration."""
from type4_gap_enum import F,E,SH,enumerate_cells,orbits,maximal
from itertools import combinations,product
from fractions import Fraction as Q
from pathlib import Path
import sys,ctypes as ct,ctypes.util
V=tuple(range(8)); R=tuple(i for i in V if i!=4);E=set(E);W=10**12;Y=10**6

def num(x):
 x=Q(x)
 if x<0:return '(- '+num(-x)+')'
 if x.denominator!=1:return '(/ %d %d)'%(x.numerator,x.denominator)
 return str(x.numerator)
def expr(op,*x):return '('+op+' '+' '.join(map(str,x))+')'
def add(*x):return expr('+',*x) if len(x)>1 else str(x[0]) if x else '0'
def neg(a):return expr('-',a)
def sub(a,b):return expr('-',a,b)
def mul(*x):return expr('*',*x) if len(x)>1 else str(x[0]) if x else '1'
def sq(x):return mul(x,x)
def dot(a,b):return add(*(mul(x,y) for x,y in zip(a,b)))
def det(M):
 if len(M)==1:return M[0][0]
 return add(*(mul(num((-1)**j),v,det([row[:j]+row[j+1:] for row in M[1:]])) for j,v in enumerate(M[0])))

def build(K,cell,full=False):
 lines=['(set-logic QF_NRA)'];nvar=0;nas=0
 def v(name):
  nonlocal nvar;nvar+=1;lines.append(f'(declare-const {name} Real)');return name
 def df(name,x):lines.append(f'(define-fun {name} () Real {x})');return name
 def ass(x):
  nonlocal nas;nas+=1;lines.append(f'(assert {x})')
 def c(op,a,b='0'):ass(expr(op,a,b))
 p={i:(v(f'x{i}'),v(f'b{i}')) if i!=4 else ('0','0') for i in V}
 def diff(i,j,k=(0,0)):
  m,n=k;return (add(sub(p[j][0],p[i][0]),num(Q(m)+Q(n,2))),add(sub(p[j][1],p[i][1]),num(n)))
 def norm(a):return add(sq(a[0]),mul(str(W),sq(a[1])))
 S={};D={}
 for i,j in combinations(V,2):
  a,b=diff(i,j)
  if (i,j) in E:
   X,B=diff(i,j,K[i,j]);m,n=K[i,j];s=Q(m)+Q(n,2)
   D[i,j]=df(f'd{i}{j}',norm((X,B)))
   for t,bd in [(X,Q(1,2)),(add(B,mul(num(Q(1,2*W)),X)),Q(1,2)+Q(1,8*W)),(sub(B,mul(num(Q(1,2*W)),X)),Q(1,2)+Q(1,8*W))]:
    c('<',t,num(bd));c('>',t,num(-bd))
   if i!=4 and j!=4:
    S[i,j]=df(f's{i}{j}',neg(add(mul(num(s),a),mul(num(W*n),b),num((s*s+W*n*n)/2)))) if (m,n)!=(0,0) else '0'
    if (m,n)!=(0,0):c('>',S[i,j])
  else:
   S[i,j]=v(f's{i}{j}');c('>=',S[i,j]);D[i,j]=df(f'd{i}{j}',sub(norm((a,b)),mul('2',S[i,j])))
   c('>',D[i,j])
   for k in product(range(-1,2),repeat=2):c('<=',D[i,j],norm(diff(i,j,k)))
 A=[]
 for i,j,k in F:
  x,y=diff(i,j,K[i,j]);u,z=diff(i,k,K[i,k]);A.append(df(f'a{i}{j}{k}',sub(mul(x,z),mul(y,u))))
 ass(expr('or',expr('and',*(expr('>',a,'0') for a in A),expr('=',add(*A),'2')),expr('and',*(expr('<',a,'0') for a in A),expr('=',add(*A),'(- 2)'))))
 eps=Q(1,1000);low=[[],[]];high=[[],[]]
 for i,(l,q) in enumerate(cell):
  a=sub(p[i][1],num(q))
  if l==0:low[0].append(sub(a,num(eps)));high[0].append(add(a,num(eps)))
  elif l==2:low[1].append(sub(a,num(eps)));high[1].append(add(a,num(eps)))
  elif l==1:high[0].append(add(a,num(eps)));low[1].append(sub(a,num(eps)))
  else:high[1].append(add(a,num(eps)));low[0].append(sub(a,num(1+eps)))
 for j in range(2):
  for l,h in product(low[j],high[j]):c('<=',l,h)
 for l,h in product(low[0],high[1]):c('<',add(l,num(Q(119,250))),h)
 for l,h in product(low[1],high[0]):c('<',l,add(h,num(Q(131,250))))
 for i,j in combinations(V,2):
  li,lj=cell[i][0],cell[j][0]
  if li==lj and li%2==0:c('<=',D[i,j],num(4*eps*eps*W+Q(1,4)))
  elif {li,lj}=={0,2}:c('>',D[i,j],num(W*Q(11,25)**2))
 if K[1,5]==(1,0):
  s=neg(p[5][0]);T=mul(str(W),p[5][1]);u=mul(str(W),sub(p[2][1],num(Q(1,2))));vv=mul(str(W),add(p[3][1],num(Q(1,2))))
  for op,a,b in [('>',s,'0'),('<',s,num(Q(1,2))),('<',T,mul(num(Q(1,2)),s)),('>',T,mul(num(Q(-1,2)),s)),('>',u,num(Q(-3,8))),('<',u,num(Q(1,8))),('>',vv,num(Q(-1,8))),('<',vv,num(Q(3,8)))]:c(op,a,b)
  t={i:mul('2' if i in (0,6) else '(- 2)',p[i][1]) for i in (0,1,6,7)}
  for i in t:c('>',t[i],num(Q(-1,W)));c('<',t[i],num(1+Q(1,4*W)))
  for z in [mul(t[1],t[6]),mul(sub('1',t[0]),sub('1',t[1])),mul(sub('1',t[6]),sub('1',t[7]))]:c('<',z,num(Q(21,W)))
 def h(i,j):
  if i in R and j in R:return '0' if i==j else S[tuple(sorted((i,j)))]
  if i in R and j in (8,9):return p[i][j-8]
  if j in R and i in (8,9):return p[j][i-8]
  return num(-1 if i==j==8 else Q(-1,W) if i==j==9 else 0)
 P=(2,6,1,3);J=tuple(i for i in R+(8,9) if i not in P);aa=h(2,1);bb=h(2,3);cc=h(6,3);ac=df('AC',mul(aa,cc));c('>',aa);c('>',cc)
 assert h(2,6)==h(1,3)==h(6,1)=='0'
 N=[['0','0',cc,'0'],['0','0',neg(bb),aa],[cc,neg(bb),'0','0'],['0',aa,'0','0']]
 U={i:v(f'u{i}') if i in J else '0' for i in R+(8,9)}
 for i,j in [(i,j) for a,i in enumerate(J) for j in J[a:]]:
  L=df(f'L{i}{j}',sub(mul(ac,h(i,j)),add(*(mul(h(i,P[k]),N[k][l],h(P[l],j)) for k,l in product(range(4),repeat=2) if N[k][l]!='0'))));c('=',L,mul(U[i],U[j]))
 c('>',add(*(sq(U[i]) for i in J)))
 def d(i,j):return '0' if i==j else D[tuple(sorted((i,j)))]
 G={}
 for i in V:
  for j in range(i,8):G[i,j]=df(f'G{i}{j}',add('1',mul(num(Q(1,2)),sub(add(d(4,i),d(4,j)),d(i,j)))))
 def g(i,j):return G[tuple(sorted((i,j)))]
 for B in combinations(V,4):
  if all(e in E for e in combinations(B,2)):c('>',det([[g(i,j) for j in B] for i in B]))
 if full:
  simplices={(i,) for i in V}|E|{tuple(sorted(f)) for f in F}
  byset={}
  for A,B in combinations(sorted(simplices),2):
   if set(A)&set(B) or len(A)+len(B)>5:continue
   S0=tuple(sorted(A+B));a=A if S0[0] in A else B;byset.setdefault(S0,set()).add(tuple(a))
  for S0,parts in sorted(byset.items()):
   n=len(S0);tag=''.join(map(str,S0));H=[[g(i,j) for j in S0] for i in S0]
   d0=df('H'+tag,det(H)) if n<5 else '0'
   co=[df('co'+tag+'_'+str(j),mul(num((-1)**j),det([row[:j]+row[j+1:] for row in H[1:]]))) for j in range(n)]
   for A in sorted(parts):
    ass(expr('not',expr('and',expr('=',d0,'0'),*(expr('>',a,'0') if i in A else expr('<',a,'0') for i,a in zip(S0,co)))))
 return '\n'.join(lines)+'\n',nvar,nas

def solve(smt,timeout):
 z=ct.CDLL(ctypes.util.find_library('z3'));p=ct.c_void_p
 for f,ret,args in [('Z3_mk_config',p,[]),('Z3_set_param_value',None,[p,ct.c_char_p,ct.c_char_p]),('Z3_mk_context',p,[p]),('Z3_del_config',None,[p]),('Z3_mk_solver_for_logic',p,[p,p]),('Z3_mk_string_symbol',p,[p,ct.c_char_p]),('Z3_solver_inc_ref',None,[p,p]),('Z3_solver_from_string',None,[p,p,ct.c_char_p]),('Z3_solver_check',ct.c_int,[p,p]),('Z3_solver_get_reason_unknown',ct.c_char_p,[p,p]),('Z3_del_context',None,[p])]:
  f0=getattr(z,f);f0.restype=ret;f0.argtypes=args
 cfg=z.Z3_mk_config();z.Z3_set_param_value(cfg,b'timeout',str(timeout).encode());ctx=z.Z3_mk_context(cfg);z.Z3_del_config(cfg);s=z.Z3_mk_solver_for_logic(ctx,z.Z3_mk_string_symbol(ctx,b'QF_NRA'));z.Z3_solver_inc_ref(ctx,s);z.Z3_solver_from_string(ctx,s,smt.encode());o=z.Z3_solver_check(ctx,s);why=z.Z3_solver_get_reason_unknown(ctx,s).decode() if o==0 else '';z.Z3_del_context(ctx);return o,why
if __name__=='__main__':
 import argparse
 parser=argparse.ArgumentParser(description=__doc__)
 parser.add_argument('output',type=Path)
 parser.add_argument('--full',action='store_true',help='include all degenerate simplex-intersection exclusions')
 parser.add_argument('--case',choices=[f'ray1_{j}' for j in range(1,7)]+['ray2_1','ray2_2'],
                     help='generate only this complete maximal case (default: all eight)')
 args=parser.parse_args()
 out=args.output;out.mkdir(exist_ok=True,parents=True)
 for m,sh in enumerate(SH,1):
  if args.case and not args.case.startswith(f'ray{m}_'):continue
  K,raw=enumerate_cells(sh);rs=orbits(K,maximal(raw));assert len(rs)==(6 if m==1 else 2)
  for j,c in enumerate(rs,1):
   name=f'ray{m}_{j}'
   if args.case and name!=args.case:continue
   smt,nv,na=build(K,c,args.full)
   (out/(name+'.smt2')).write_text(smt+'(check-sat)\n');print(name,nv,na,len(smt),flush=True)

