#!/usr/bin/env python3
'''Numerical heuristic, NOT a proof. Reconstruct a spanning 3-tree and optimize only intrinsic coordinates.
Input: type, index of sharp-ray marking (one-based), y (hex for sqrt(3)/2), trial count per sign branch.
'''
import os
os.environ['JAX_ENABLE_X64']='true';os.environ['OPENBLAS_NUM_THREADS']='1';os.environ['OMP_NUM_THREADS']='1';os.environ['XLA_FLAGS']='--xla_cpu_multi_thread_eigen=false intra_op_parallelism_threads=1'
import numpy as np,itertools as it,sys,json,time
from pathlib import Path
import jax,jax.numpy as j
from scipy.optimize import minimize
ROOT=Path(__file__).resolve().parent
P=Path(__file__).resolve().parent;C=json.loads((P/'cases.json').read_text());F0=json.loads((P/'lutz_faces.json').read_text());t=int(sys.argv[1]);case=[c for c in C if c['type']==t and c['sharp']][int(sys.argv[2])-1]; y=3**.5/2 if sys.argv[3]=='hex' else float(sys.argv[3]);trials=int(sys.argv[4]);x=.5
L=np.array([[1,0],[x,y]]);lat=np.array([[1,0],[x,y],[x-1,y]]);latj=j.array(lat)
F=np.array([tuple(map(int,s)) for s in F0[str(t)].split()]);E=np.array(sorted({tuple(sorted(e)) for f in F for e in it.combinations(f,2)}));ES={tuple(e) for e in E};FS={tuple(sorted(f)) for f in F}
K=np.zeros((8,8,2));
for v in case['edge_shifts']:
 a,b=v['edge'];K[a,b]=v['shift'];K[b,a]=-K[a,b]
K=K@L
T=json.loads((ROOT/f'clique_signs{t}.json').read_text());order=[(a,tuple(b)) for a,b in T['true_tree']];cliques=[tuple(q) for q in T['cliques']];tree_cliques=[tuple(q) for q in T['true_tree_cliques']];branch_signs=T['true_tree_signs'];
# tree branches sorted signs up to global reflection. Convert to insertion order.
def parity(q):return (-1)**sum(a>b for i,a in enumerate(q) for b in q[i+1:])
branches=np.array([[(1 if s[tree_cliques.index(tuple(sorted(A+(a,))))]=='+' else -1)*parity(A+(a,)) for a,A in order] for s in branch_signs]);A=order[0][1];assert A==(0,1,2)
ET=set(it.combinations(A,2));placed=set(A)
for v,abc in order:
 assert set(abc)<=placed and v not in placed and set(it.combinations(abc,2))<=ET;ET.update(tuple(sorted((v,a))) for a in abc);placed.add(v)
ER=np.array(sorted(ES-ET));assert len(ER)==6 and len(ET)==18
Q=np.array(list(it.combinations(range(8),4)));qi={tuple(q):i for i,q in enumerate(Q)};CI=np.array([qi[q] for q in cliques]);PI=[];PS=[]
for c0 in it.combinations(range(8),5):
 for a in it.combinations(c0,2):
  if a in ES and tuple(i for i in c0 if i not in a) in FS:PI.append([qi[c0[:i]+c0[i+1:]] for i in range(5)]);PS.append([(-1)**i*(1 if c0[i] in a else -1) for i in range(5)])
PI=np.array(PI);PS=np.array(PS);CP=np.array([[1 if s=='+' else -1 for s in a] for a in T['patterns']]);CP=np.r_[CP,-CP];
# filter patterns by tree branch sign. For each branch the array shape varies; pad to maximum with duplicates.
sel=np.array([cliques.index(q) for q in tree_cliques]);PATS=[]
for s in branch_signs:
 d=np.array([1 if a=='+' else -1 for a in s]);PATS.append(CP[np.all(CP[:,sel]==d,axis=1)])
maxn=max(map(len,PATS));PATS=np.array([np.concatenate((a,np.repeat(a[:1],maxn-len(a),axis=0))) for a in PATS]);assert maxn>0
# harmonic intrinsic seed
N={i:[b for b in range(8) if i!=b and tuple(sorted((i,b))) in ES] for i in range(8)};lap=np.array([[len(N[i]) if i==k else -int(k in N[i]) for k in range(1,8)] for i in range(1,8)]);p0=np.zeros((8,2));p0[1:]=np.linalg.solve(lap,np.array([sum(K[i,b] for b in N[i]) for i in range(1,8)]));
def cross(a,b):return a[...,0]*b[...,1]-a[...,1]*b[...,0]
ori=np.sign(cross(p0[F[:,1]]-p0[F[:,0]]+K[F[:,0],F[:,1]],p0[F[:,2]]-p0[F[:,0]]+K[F[:,0],F[:,2]]))[0]
lat2=np.sum(lat*lat,axis=1);Kj=j.array(K)
def ds(p):
 u=p[None,:,:]-p[:,None,:]+Kj;return j.sum(u*u,axis=2)
def safe(x):return j.maximum(x,1e-12)
def reconstruct(p,sg):
 D=ds(p);r=j.zeros((8,3));a,b,c=A;l=j.sqrt(safe(D[a,b]));q=(D[a,c]+D[a,b]-D[b,c])/(2*l);h2=D[a,c]-q*q;r=r.at[b].set(j.array([l,0.,0.]));r=r.at[c].set(j.array([q,j.sqrt(safe(h2)),0.]));hs=[h2]
 for k,(v,(a,b,c)) in enumerate(order):
  g11=D[a,b];g22=D[a,c];g12=(g11+g22-D[b,c])/2;u=(D[a,v]+g11-D[b,v])/2;w=(D[a,v]+g22-D[c,v])/2;det=g11*g22-g12*g12;al=(u*g22-w*g12)/safe(det);be=(w*g11-u*g12)/safe(det);h2=D[a,v]-al*u-be*w;U=r[b]-r[a];V=r[c]-r[a];r=r.at[v].set(r[a]+al*U+be*V+sg[k]*j.sqrt(safe(h2)/safe(det))*j.cross(U,V));hs.extend([det,h2])
 return r,D,j.array(hs)
def dets(r):
 v=r[Q[:,1:]]-r[Q[:,0,None]];return j.sum(j.cross(v[:,0],v[:,1])*v[:,2],axis=1)
def unpack(v,sg):p=j.concatenate((j.zeros((1,2)),v[:14].reshape((7,2))),axis=0);r,D,hs=reconstruct(p,sg);return p,r,D,hs
# Smooth equality constraints: six remaining edge squared lengths.
def eq(v,sg):
 p,r,D,hs=unpack(v,sg);w=r[ER[:,1]]-r[ER[:,0]];return j.sum(w*w,axis=1)-D[ER[:,0],ER[:,1]]
def inequality(v,sg,pat):
 p,r,D,hs=unpack(v,sg);m=v[-1];u=p[E[:,1]]-p[E[:,0]]+Kj[E[:,0],E[:,1]];proj=2*u@latj.T;u1=p[F[:,1]]-p[F[:,0]]+Kj[F[:,0],F[:,1]];u2=p[F[:,2]]-p[F[:,0]]+Kj[F[:,0],F[:,2]];dd=dets(r);seps=dd[PI]*PS;cp=dd[CI]*pat
 return j.concatenate((hs-m*.1,ori*cross(u1,u2)-m,(lat2-proj).ravel()-m,(lat2+proj).ravel()-m,j.max(seps,axis=1)-m*.1,-j.min(seps,axis=1)-m*.1,j.array([j.max(j.min(cp,axis=1))-m*.1])))
eqj=jax.jit(eq);eqjac=jax.jit(jax.jacfwd(eq));inj=jax.jit(inequality);injac=jax.jit(jax.jacfwd(inequality));rng=np.random.default_rng(1926);grad=np.r_[np.zeros(14),-1.];best=-1e6;bestv=None
print('type',t,'marking',case['marking'],'y',y,'branches',len(branches),'max patterns per branch',maxn,'remaining edges',ER,flush=True)
for i,(sg,pat) in enumerate(zip(branches,PATS)):
 sg=j.array(sg);pat=j.array(pat);cons=[{'type':'eq','fun':lambda v:np.array(eqj(v,sg)),'jac':lambda v:np.array(eqjac(v,sg))},{'type':'ineq','fun':lambda v:np.array(inj(v,sg,pat)),'jac':lambda v:np.array(injac(v,sg,pat))}];b=-1e6;bv=None
 for k in range(trials):
  p=p0.copy();p[1:]+=rng.normal(0,0.01 if k%3==0 else .04 if k%3==1 else .075,(7,2));v=np.r_[p[1:].ravel(),-.05]
  if k==0:v=np.r_[p0[1:].ravel(),-.05]
  if k>1 and k%2==0 and bv is not None:v=bv.copy();v[:14]+=rng.normal(0,.02,14);v[-1]=-.01
  sol=minimize(lambda a:-a[-1],v,jac=lambda a:grad,bounds=[(-3*max(1,y),3*max(1,y))]*14+[(-2,.1)],constraints=cons,method='SLSQP',options={'maxiter':140,'ftol':1e-10})
  err=max(abs(cons[0]['fun'](sol.x)));sl=min(cons[1]['fun'](sol.x));m=sol.x[-1]
  if err<1e-7 and sl>-1e-7 and m>b:b=m;bv=sol.x.copy()
  if err<1e-8 and sl>-1e-8 and m>best:best=m;bestv=sol.x.copy();print('new best',i,k,m,'eq',err,'sl',sl,flush=True)
  if err<1e-9 and sl>-1e-9 and m>1e-7:
   p,r,D,hs=unpack(sol.x,sg);print('POTENTIAL EMBEDDING',i,k,m,err,sl,flush=True);np.savez(ROOT/f'treewin_{t}_{sys.argv[2]}_{sys.argv[3]}.npz',p=np.array(p),r=np.array(r),sign=np.array(sg),v=sol.x);sys.exit(0)
 print('branch',i,'best',b,flush=True)
print('DONE best',best,flush=True)
