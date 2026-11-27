import json,itertools as it,sys
from pathlib import Path
import ctypes as c
from ctypes.util import find_library
V=range(8);Q=list(it.combinations(V,4));ids={q:i+1 for i,q in enumerate(Q)}
F=json.loads(Path(__file__).resolve().with_name('lutz_faces.json').read_text())
def lit(q):return ids[tuple(sorted(q))]*(-1)**sum(a>b for i,a in enumerate(q) for b in q[i+1:])
def formula(t):
 T=tuple(sorted(tuple(sorted(map(int,f))) for f in F[str(t)].split()));E={e for tri in T for e in it.combinations(tri,2)};N={i:{j for j in V if tuple(sorted((i,j))) in E} for i in V};clauses=[[1]]
 for s in it.combinations(V,2):
  for a,b,d,e in it.combinations(sorted(set(V)-set(s)),4):
   L=[lit((*s,a,b)),lit((*s,d,e)),-lit((*s,a,d)),lit((*s,b,e)),lit((*s,a,e)),lit((*s,b,d))]
   for B in it.product([-1,1],repeat=6):
    if B[0]*B[1]==B[2]*B[3]==B[4]*B[5]:clauses.append([-x*y for x,y in zip(L,B)])
 for C in it.combinations(V,5):
  s=[(-1)**i*lit(C[:i]+C[i+1:]) for i in range(5)];clauses.extend([s,[-x for x in s]])
  def forbid(A):
   L=[x if v in A else -x for x,v in zip(s,C)];clauses.extend([L,[-x for x in L]])
  for A in it.combinations(C,2):
   if A in E and tuple(v for v in C if v not in A) in T:forbid(A)
  for v in C:
   if set(C)-{v}<=N[v]:forbid({v})
 nvar=70
 for v in V:
  ms=[]
  for tri in T:
   if v in tri:
    nvar+=1;ms.append(nvar);D=[lit((*tri,w)) for w in sorted(N[v]-set(tri))];clauses.extend([[-nvar]+D,[-nvar]+[-d for d in D]])
  clauses.append(ms)
 return nvar,clauses,T,E,N
class SAT:
 def __init__(self,n,cls):
  self.z=z=c.CDLL(find_library('z3'));P=c.c_void_p;I=c.c_uint;B=c.c_bool
  for name,res,args in [('Z3_mk_config',P,[]),('Z3_mk_context',P,[P]),('Z3_del_config',None,[P]),('Z3_mk_solver',P,[P]),('Z3_solver_inc_ref',None,[P,P]),('Z3_mk_bool_sort',P,[P]),('Z3_mk_int_symbol',P,[P,c.c_int]),('Z3_mk_const',P,[P,P,P]),('Z3_mk_not',P,[P,P]),('Z3_mk_or',P,[P,I,c.POINTER(P)]),('Z3_solver_assert',None,[P,P,P]),('Z3_solver_check',c.c_int,[P,P]),('Z3_solver_push',None,[P,P]),('Z3_solver_pop',None,[P,P,I]),('Z3_solver_get_model',P,[P,P]),('Z3_model_inc_ref',None,[P,P]),('Z3_model_dec_ref',None,[P,P]),('Z3_model_eval',B,[P,P,P,B,c.POINTER(P)]),('Z3_get_bool_value',c.c_int,[P,P])]:
   f=getattr(z,name);f.restype=res;f.argtypes=args
  cfg=z.Z3_mk_config();self.ctx=z.Z3_mk_context(cfg);z.Z3_del_config(cfg);self.s=z.Z3_mk_solver(self.ctx);z.Z3_solver_inc_ref(self.ctx,self.s);sort=z.Z3_mk_bool_sort(self.ctx);self.v={i:z.Z3_mk_const(self.ctx,z.Z3_mk_int_symbol(self.ctx,i),sort) for i in range(1,n+1)};self.v.update({-i:z.Z3_mk_not(self.ctx,p) for i,p in list(self.v.items())});self.P=P
  for cl in cls:self.add(cl)
 def add(self,cl):self.z.Z3_solver_assert(self.ctx,self.s,self.z.Z3_mk_or(self.ctx,len(cl),(self.P*len(cl))(*[self.v[x] for x in cl])))
 def check(self):return self.z.Z3_solver_check(self.ctx,self.s)
 def model(self,n=70):
  z,ctx=self.z,self.ctx;m=z.Z3_solver_get_model(ctx,self.s);z.Z3_model_inc_ref(ctx,m);a=[]
  for i in range(1,n+1):
   p=self.P();assert z.Z3_model_eval(ctx,m,self.v[i],True,c.byref(p));a.append(z.Z3_get_bool_value(ctx,p.value));assert a[-1] in (-1,1)
  z.Z3_model_dec_ref(ctx,m);return a
 def push(self):self.z.Z3_solver_push(self.ctx,self.s)
 def pop(self):self.z.Z3_solver_pop(self.ctx,self.s,1)
def run(t):
 n,C,T,E,N=formula(t);s=SAT(n,C);print('type',t,'vars',n,'clauses',len(C),'initial',s.check(),flush=True)
 if t==5:
  b,d=lit((1,2,5,3)),lit((1,2,5,4));
  s.push();s.add([b,-d]);s.add([-b,d]);print('root same side?',s.check(),flush=True);s.pop()
  s.push();s.add([b,d]);s.add([-b,-d]);print('root opposite sides?',s.check(),flush=True);s.pop()
 from collections import Counter
 ctr=Counter();hp=Counter();allm=[];i=0
 # block all primary orientation signs (not auxiliaries)
 while s.check()==1:
  m=s.model();d=lambda q:m[abs(lit(q))-1]*(1 if lit(q)>0 else -1);h=tuple(tri for tri in it.combinations(V,3) if len({d((*tri,j)) for j in V if j not in tri})==1);hv=tuple(sorted(set(sum(h,()))));ctr[(len(hv),len(set(h)&set(T)))]+=1;hp[h]+=1;allm.append(''.join('+' if v==1 else '-' for v in m));i+=1
  s.add([-v*(j+1) for j,v in enumerate(m)])
  if i%500==0:print('progress',t,i,ctr,len(hp),flush=True)
  if i>=20000:raise RuntimeError('cap reached')
 print('DONE',t,i,ctr,'hull patterns',len(hp),flush=True);(Path(__file__).resolve().parent / f'm{t}.json').write_text(json.dumps(allm));(Path(__file__).resolve().parent / f'hulls{t}.json').write_text(json.dumps([[h,c] for h,c in hp.items()]))
if __name__=='__main__':run(int(sys.argv[1]))
