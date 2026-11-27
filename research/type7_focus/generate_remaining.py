#!/usr/bin/env python3
"""Generate the 15 localized fixed-metric necessary Gram systems.
Usage: python generate_remaining.py OUTPUT_DIR [TIMEOUT_MS]
The optional timeout runs libz3 on each system. No embedding constraints
except clique nondegeneracy and nonedge contractions are imposed: UNSAT
would be sufficient for exclusion; SAT would not imply an embedding.
"""
from itertools import combinations, permutations
from fractions import Fraction as F
from pathlib import Path
import ctypes as ct, ctypes.util, json, sys
V=range(8); A=(0,1,2,3); B=(4,5,6,7)
MASKS=('03','04','014','015','025','0125','0145')
Y=10**6; W=Y*Y; t=F(1,W); DELTA=F(1,1000)
def op(f,*xs):return '('+f+' '+' '.join(xs)+')'
def add(*xs):return '0' if not xs else xs[0] if len(xs)==1 else op('+',*xs)
def mul(*xs):return '1' if not xs else xs[0] if len(xs)==1 else op('*',*xs)
def sub(a,b):return op('-',a,b)
def neg(a):return op('-',a)
def rat(x):
 x=F(x); n=str(x.numerator) if x.numerator>=0 else neg(str(-x.numerator));return n if x.denominator==1 else op('/',n,str(x.denominator))
def all_(xs):return 'true' if not xs else op('and',*xs)
def any_(xs):return 'false' if not xs else op('or',*xs)
def det(M):
 n=len(M);return add(*(neg(mul(*(M[i][p[i]] for i in range(n)))) if sum(p[i]>p[j] for i,j in combinations(range(n),2))%2 else mul(*(M[i][p[i]] for i in range(n))) for p in permutations(range(n))))
def gen(mark,K,faces,mask):
 E={tuple(sorted(e)) for f in faces for e in combinations(f,2)}; lines=['(set-logic QF_NRA)']; nv=0
 def decl(a):
  nonlocal nv
  nv+=1;lines.append(f'(declare-fun {a} () Real)');return a
 def define(a,b):lines.append(f'(define-fun {a} () Real {b})');return a
 def require(a):lines.append(op('assert',a))
 def abslt(a,b):return all_([op('<',a,b),op('>',a,neg(b))])
 def absgte(a,b):return any_([op('>=',a,b),op('<=',a,neg(b))])
 x=['0']+[decl(f'x{i}') for i in V[1:]];v=['0']+[decl(f'v{i}') for i in V[1:]]
 X={}; Z={}; D={}
 def direction(i,j,m,n):return add(sub(x[j],x[i]),rat(F(m)+F(n,2))),add(sub(v[j],v[i]),rat(n))
 def norm(x,z):return add(mul(rat(t),x,x),mul(z,z))
 for i,j in combinations(V,2):
  if (i,j) in E:
   a,b=direction(i,j,*K[i,j]);a=define(f'X{i}{j}',a);b=define(f'V{i}{j}',b);X[i,j]=a;X[j,i]=neg(a);Z[i,j]=b;Z[j,i]=neg(b)
   d=define(f'D{i}{j}',norm(a,b));require(op('>',d,'0'));require(abslt(a,'(/ 1 2)'))
   for s in (a,neg(a)):require(abslt(add(b,mul(rat(t/2),s)),rat(F(1,2)+t/8)))
  else:
   d=decl(f'z{i}{j}');require(op('>',d,'0'))
   for m in range(-4,5):
    for n in range(-3,4):require(op('<=',d,norm(*direction(i,j,m,n))))
  D[i,j]=D[j,i]=d
 for i in V:D[i,i]='0'
 area=[define(f'area{k}',sub(mul(X[a,b],Z[a,c]),mul(X[a,c],Z[a,b]))) for k,(a,b,c) in enumerate(faces)]
 require(any_([all_([op('>',a,'0') for a in area]+[op('=',add(*area),'2')]),all_([op('<',a,'0') for a in area]+[op('=',add(*area),'(- 2)')])]))
 if mark in (1,2):
  for i in V:require((absgte if str(i) in mask else abslt)(Z[i,(i+1)%8],rat(DELTA)))
 else:
  for i,j in sorted(E):
   short=(i in (0,1,4,5))==(j in (0,1,4,5));b=Z[i,j];require((abslt if short else absgte)(b,rat(7*t/4 if short else F(1,2)-7*t/4)))
 # The four consecutive anchors form a clique. All clique minors are strict
 # by the earlier strict support lemma (not needed for localization itself).
 G={}
 for i in V[1:]:
  for j in range(i,8):G[i,j]=G[j,i]=define(f'G{i}{j}',mul('(/ 1 2)',sub(add(D[0,i],D[0,j]),D[i,j])))
 M=[[G[i,j] for j in A[1:]] for i in A[1:]];g=define('g',det(M));require(op('>',M[0][0],'0'));require(op('>',det([r[:2] for r in M[:2]]),'0'));require(op('>',g,'0'))
 H=[[define(f'H{i}{j}',(neg if (i+j)%2 else lambda a:a)(det([[M[k][l] for l in range(3) if l!=i] for k in range(3) if k!=j]))) for j in range(3)] for i in range(3)]
 U={0:['0']*3}
 for i in V[1:]:U[i]=[G[i,j] for j in A[1:]]
 R={i:[define(f'R{i}{k}',add(*(mul(H[k][l],U[i][l]) for l in range(3)))) for k in range(3)] for i in B}
 for i in B:
  for j in B:
   if i<=j:require(op('=',add(*(mul(U[i][k],R[j][k]) for k in range(3))),mul(g,G[i,j])))
 for S in combinations(V,4):
  if all(e in E for e in combinations(S,2)):
   a,*rest=S;d=define('m'+''.join(map(str,S)),det([[sub(U[b][k],U[a][k]) for k in range(3)] for b in rest]));require(op('distinct',d,'0'))
 assert nv==18
 lines.append('(check-sat)');return '\n'.join(lines)+'\n'
def solve(s,ms=2000):
 z=ct.CDLL(ctypes.util.find_library('z3'));P=ct.c_void_p;S=ct.c_char_p
 for name,restype,args in [('Z3_mk_config',P,[]),('Z3_mk_context',P,[P]),('Z3_del_config',None,[P]),('Z3_del_context',None,[P]),('Z3_eval_smtlib2_string',S,[P,S])]:
  f=getattr(z,name);f.restype=restype;f.argtypes=args
 cfg=z.Z3_mk_config();ctx=z.Z3_mk_context(cfg);z.Z3_del_config(cfg)
 ans=z.Z3_eval_smtlib2_string(ctx,(f'(set-option :timeout {ms})\n'+s+'\n(get-info :reason-unknown)\n').encode()).decode();z.Z3_del_context(ctx);return ans.strip().replace('\n',' ')
if __name__=='__main__':
 D=Path(__file__).resolve().parent.parent/'linking_checkpoint'
 cases=json.loads((D/'cases.json').read_text())
 faces=[tuple(map(int,f)) for f in json.loads((D/'lutz_faces.json').read_text())['7'].split()]
 out=Path(sys.argv[1]);out.mkdir(exist_ok=True,parents=True)
 for mark in (1,2,3):
  case=next(c for c in cases if c['file']==f't7_ray_{mark}.smt2')
  K={tuple(z['edge']):tuple(z['shift']) for z in case['edge_shifts']}
  K.update({(j,i):(-m,-n) for (i,j),(m,n) in list(K.items())})
  for mask in MASKS if mark!=3 else ('phase0',):
   s=gen(mark,K,faces,mask);name=f'ray{mark}_{mask}';(out/(name+'.smt2')).write_text(s)
   print(name,len(s),solve(s,int(sys.argv[2])) if len(sys.argv)>2 else 'generated',flush=True)
