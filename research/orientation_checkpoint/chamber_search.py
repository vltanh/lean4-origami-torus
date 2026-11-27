#!/usr/bin/env python3
'''Heuristic only. Search full SAT sign chambers with the metric tree reconstruction.'''
# Load definitions (not the trial loop) from metric_tree_search.py
from pathlib import Path
import sys
src=Path(__file__).with_name('metric_tree_search.py').read_text().split("eqj=jax.jit(eq);")[0]
# metric_tree_search expects args type, marking, y, trials. Additional args here: start, count.
exec(compile(src,str(Path(__file__).with_name('metric_tree_search.py')),'exec'))
from satgeom import lit,formula,SAT
from collections import defaultdict
# Include metric-only witness and harmonic seeds. Search symmetry orbit rep closest to a seed.
full=json.loads((ROOT/f'full_sign_orbits{t}.json').read_text());aut=[p for p in it.permutations(range(8)) if {tuple(sorted(p[i] for i in f)) for f in FS}==FS]
# for Type5 the unique hex marking orbit is already a single orbit of the 12 lattice symmetries,
# so all 6 automorphisms can be compensated by lattice symmetry. For other types do not quotient without checking.
assert t==5 and sys.argv[3]=='hex'
M=[[(abs(lit(tuple(p[i] for i in q)))-1,1 if lit(tuple(p[i] for i in q))>0 else -1) for q in Q] for p in aut];Midx=np.array([[a for a,b in m] for m in M]);Msg=np.array([[b for a,b in m] for m in M])
Tids=[qi[tuple(sorted(A+(v,)))] for v,A in order];Tpar=np.array([parity(A+(v,)) for v,A in order]);
# all branches normalized with first orientation +
S=[np.array((1,)+s) for s in it.product([-1,1],repeat=4)];seeds=defaultdict(list)
for sg in S:
 v=np.r_[p0[1:].ravel(),-.01];r=unpack(v,j.array(sg))[1];dd=np.array(dets(r));seeds[tuple(sg)].append((v,dd))
PTH=ROOT/f'metric_cliquewin_{t}_{sys.argv[2]}_{sys.argv[3]}.npz'
if PTH.exists():
 w=np.load(PTH);v=w['v'];sg=w['sign'];dd=np.array(dets(j.array(w['r'])));seeds[tuple(sg)].append((v,dd))
queue=[]
for k,s in enumerate(full):
 a=np.array([1 if c=='+' else -1 for c in s]);orb=a[Midx]*Msg;orb=orb*orb[:,0,None];best=None
 for b in orb:
  sg=b[Tids]*Tpar
  for v,dd in seeds[tuple(sg)]:
   score=np.sum(np.maximum(-b*dd,0));rank=(score,np.sum(b*dd<0))
   if best is None or rank<best[0]:best=(rank,b,sg,v)
 queue.append((best[0],k,*best[1:]))
queue.sort(key=lambda x:x[0]);print('full chambers',len(queue),'first scores',[(q[0],q[1]) for q in queue[:5]],flush=True)
def ineq(v,sg,target):
 p,r,D,hs=unpack(v,sg);m=v[-1];u=p[E[:,1]]-p[E[:,0]]+Kj[E[:,0],E[:,1]];proj=2*u@latj.T;u1=p[F[:,1]]-p[F[:,0]]+Kj[F[:,0],F[:,1]];u2=p[F[:,2]]-p[F[:,0]]+Kj[F[:,0],F[:,2]];dd=dets(r)
 return j.concatenate((hs-m*.1,ori*cross(u1,u2)-m,(lat2-proj).ravel()-m,(lat2+proj).ravel()-m,target*dd-m*.1))
eqj=jax.jit(eq);eqjac=jax.jit(jax.jacfwd(eq));inj=jax.jit(ineq);injac=jax.jit(jax.jacfwd(ineq));grad=np.r_[np.zeros(14),-1.];best=-1e6
rng=np.random.default_rng(5555);start=int(sys.argv[5]);num=int(sys.argv[6]);cache=[]
for i,(score,k,target,sg,v0) in enumerate(queue[start:start+num],start):
 target=j.array(target);sg=j.array(sg);v=v0.copy();v[-1]=-.01
 # If nearby feasible equality solution already found, use it as an additional start.
 opts=[v]
 compat=[(np.sum(a!=np.array(target)),q) for a,g,q in cache if tuple(g)==tuple(np.array(sg))];
 if compat:
  q=min(compat,key=lambda z:z[0])[1].copy();q[-1]=-.01;opts.append(q)
 cons=[{'type':'eq','fun':lambda v:np.array(eqj(v,sg)),'jac':lambda v:np.array(eqjac(v,sg))},{'type':'ineq','fun':lambda v:np.array(inj(v,sg,target)),'jac':lambda v:np.array(injac(v,sg,target))}]
 for v in opts:
  sol=minimize(lambda a:-a[-1],v,jac=lambda a:grad,bounds=[(-3,3)]*14+[(-2,.1)],constraints=cons,method='SLSQP',options={'maxiter':120,'ftol':1e-11});err=max(abs(cons[0]['fun'](sol.x)));sl=min(cons[1]['fun'](sol.x));m=sol.x[-1]
  if err<1e-8 and sl>-1e-8:
   cache.append((np.array(target),np.array(sg),sol.x.copy()))
   if m>best:
    best=m;print('best',i,k,m,'err',err,'sl',sl,flush=True);np.savez(ROOT/f'chamber_best_{t}_{start}.npz',v=sol.x,sign=np.array(sg),target=np.array(target),p=np.array(unpack(sol.x,sg)[0]),r=np.array(unpack(sol.x,sg)[1]));
   if m>1e-7 and err<1e-9 and sl>-1e-9:print('POTENTIAL EMBEDDING',i,k,m,flush=True);sys.exit(0)
 if i%25==0:print('tested',i+1,'best',best,flush=True)
print('DONE',start,num,'best',best,flush=True)
