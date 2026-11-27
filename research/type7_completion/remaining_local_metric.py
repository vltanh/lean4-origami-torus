#!/usr/bin/env python3
"""Low-degree intrinsic-only necessary systems for Type-7 rays 1 and 2.

The sixteen strict tetrahedron inequalities are exact local Euclidean
conditions. These systems omit global reconstruction/embeddedness; a SAT
result is not an origami torus. All zero boundaries of the masks are kept.
"""
from fractions import Fraction as F
from pathlib import Path
import sys
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'type7_focus'))
from generate_remaining import op,add,mul,sub,neg,rat,all_,any_,solve,MASKS

def generate(mark,mask,y=10**6):
 assert mark in (1,2) and mask in MASKS and y>=10**6
 t=F(1,y*y); H=F(7 if mark==1 else 5,2); shift=H-3
 lines=['(set-logic QF_NRA)']
 def dec(s):lines.append(f'(declare-fun {s} () Real)');return s
 def df(s,p):lines.append(f'(define-fun {s} () Real {p})');return s
 def req(p):lines.append(op('assert',p))
 def abslt(p,q):return all_([op('<',p,q),op('>',p,neg(q))])
 def sq(p):return mul(p,p)
 h=[dec(f'h{i}') for i in range(7)];h.append(df('h7',sub(rat(H),add(*h))))
 b=[dec(f'b{i}') for i in range(7)];b.append(df('b7',sub('1',add(*b))))
 for i in range(8):
  req(op('>',h[i],'0'));req(op('<',h[i],'(/ 1 2)'))
  req((any_([op('>=',b[i],'(/ 1 1000)'),op('<=',b[i],'(- (/ 1 1000))')]) if str(i) in mask else abslt(b[i],'(/ 1 1000)')))
  for k in (1,2,3):
   ids=[(i+j)%8 for j in range(k)]
   X=neg(h[i]) if k==1 else sub('1',add(*(h[j] for j in ids)))
   V=add(*(b[j] for j in ids))
   req(abslt(X,'(/ 1 2)'))
   for z in (X,neg(X)):req(abslt(add(V,mul(rat(t/2),z)),rat(F(1,2)+t/8)))
 f=[];g=[]
 for i in range(8):
  j=(i+1)%8;k=(i+2)%8
  f.append(df(f'f{i}',add(mul(h[i],add(b[j],b[k])),mul(sub('1',add(h[j],h[k])),b[i]))))
  g.append(df(f'g{i}',add(mul(h[k],add(b[i],b[j])),mul(sub('1',add(h[i],h[j])),b[k]))))
  req(op('>',f[-1],'0'));req(op('>',g[-1],'0'))
 for i in range(8):
  ids=[(i+j)%8 for j in (3,4,5)]
  X=sub('1',add(*(h[j] for j in ids)));V=add(*(b[j] for j in ids))
  delta=df(f'delta{i}',add(sub('1',mul('2',V)),mul(rat(t),add(mul(rat(2*shift),X),rat(shift*shift)))))
  req(op('>',delta,'0'))
  req(op('<',mul(delta,add(sq(b[i]),mul(rat(t),sq(h[i])))),mul(rat(4*t),f[i],g[(i-2)%8])))
  ids=[(i+j)%8 for j in range(3)];X=sub('1',add(*(h[j] for j in ids)));V=add(*(b[j] for j in ids))
  req(op('<',mul(sub('1',mul('2',h[(i+1)%8])),add(sq(V),mul(rat(t),sq(X)))),mul('4',f[i],g[i])))
 lines.append('(check-sat)');return '\n'.join(lines)+'\n'

if __name__=='__main__':
 import argparse,time
 p=argparse.ArgumentParser();p.add_argument('output',type=Path);p.add_argument('--timeout',type=int,default=0);p.add_argument('--mark',type=int,choices=(1,2));p.add_argument('--mask',choices=MASKS);a=p.parse_args();a.output.mkdir(parents=True,exist_ok=True)
 for mark in (a.mark,) if a.mark else (1,2):
  for mask in (a.mask,) if a.mask else MASKS:
   s=generate(mark,mask);name=f'ray{mark}_{mask}';(a.output/(name+'.smt2')).write_text(s);st=time.monotonic();r=solve(s,a.timeout) if a.timeout else 'generated';print(name,len(s),round(time.monotonic()-st,3),r,flush=True)
