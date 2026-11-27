#!/usr/bin/env python3
"""Numerical search only, in the 16 full sign chambers for Type7 ray_4.
Positive margin would require a separate exact root certificate. Negative margin
or failed convergence does not certify impossibility.
Usage: python search_ring4.py aspect_ratio number_of_starts_per_chamber
"""
import os
os.environ.setdefault('OPENBLAS_NUM_THREADS','1')
os.environ.setdefault('OMP_NUM_THREADS','1')
import numpy as np
import jax
jax.config.update('jax_enable_x64',True)
import jax.numpy as jnp
from scipy.optimize import minimize
from verify_linking import *
import sys
c=next(c for c in cases if c['file']=='t7_ray_4.smt2');K,_,_=data(c);A,B=short_pairs(K)[0];q=[-1,-1,-1,-1,0,-2,-1,-2];G={e:(v[0],v[1]+q[e[1]]-q[e[0]]) for e,v in K.items()}
levels=np.array([i%2 for i in V],dtype=float);F0=np.array([tuple(map(int,f)) for f in F['7'].split()]);E=np.array(sorted((i,j) for i,j in G if i<j));q4=np.array(Q);Kx=np.zeros((8,8));Ky=np.zeros((8,8))
for (i,j),(m,n) in G.items():Kx[i,j]=m+n/2;Ky[i,j]=n
v0=(levels[None,:]-levels[:,None])/2+Ky;assert all(v0[i,j]==0 if levels[i]==levels[j] else abs(v0[i,j])==.5 for i,j in E)
xx0=np.array([0,-1,1,0,-2,1,-1,2])/4;PP0=np.c_[np.array([0,0,-1,1,0,0,-1,1])/4,np.zeros(8)];rr0=np.array([0,0,1,-1,0,0,1,-1])/8;vseed=np.r_[xx0[1:],np.zeros(7),PP0[2:].ravel(),rr0[2:],-.001];t=1/float(sys.argv[1])**2;Nstart=int(sys.argv[2]);assert t<=4/35
I,J=E.T;cross=levels[J]-levels[I];v0e=v0[I,J];rem=np.array([k for k,(i,j) in enumerate(E) if (i,j)!=(0,1)]);kappa=Kx[I,J];L=levels
F1,F2,F3=F0.T;U=xx0[None,:]-xx0[:,None]+Kx;orient=np.sign((U[F1,F2]*v0[F1,F3]-U[F1,F3]*v0[F1,F2])[0]);assert np.all(orient*(U[F1,F2]*v0[F1,F3]-U[F1,F3]*v0[F1,F2])>0)
Qscale=np.array([1/t if len(set(levels[q]))==1 else 1 for q in q4]);crossedge=np.abs(v0e)>.1;cross_idx=np.flatnonzero(crossedge);ring_idx=np.flatnonzero(~crossedge)
def vals(v):
 x=jnp.r_[0.,v[:7]];g=jnp.r_[0.,v[7:14]];P=jnp.concatenate((jnp.zeros((2,2)),v[14:26].reshape((6,2))));r=jnp.r_[0.,0.,v[26:32]];m=v[-1];dx=x[J]-x[I]+kappa;dg=g[J]-g[I];dr=r[J]-r[I];c0=(x[1]+Kx[0,1])**2+2*v0[0,1]*g[1]+t*g[1]**2;lam=t/(1+4*t*c0);dz=L+2*lam*r;R=jnp.column_stack((P,dz));eq=jnp.sum((P[J]-P[I])**2,axis=1)+cross*dr+lam*dr*dr+(cross*cross)*c0-dx*dx-2*v0e*dg-t*dg*dg
 X=x[None,:]-x[:,None]+Kx;Y=v0+t*(g[None,:]-g[:,None]);a=orient*(X[F1,F2]*Y[F1,F3]-X[F1,F3]*Y[F1,F2]);u=R[q4[:,1:]]-R[q4[:,0,None]];d=jnp.sum(jnp.cross(u[:,0],u[:,1])*u[:,2],axis=1)*Qscale
 # For cross edges remove the common 1/(2t) term, avoiding ill conditioning.
 g0=.125-2*v0e[cross_idx]*dg[cross_idx];d0=dx[cross_idx]/2
 ir=Y[I[ring_idx],J[ring_idx]];dring=t*dx[ring_idx]/2
 ineq=jnp.concatenate((.5-dx-m,.5+dx-m,g0+d0-m,g0-d0-m,.5+t/8-ir+dring-m,.5+t/8-ir-dring-m,.5+t/8+ir+dring-m,.5+t/8+ir-dring-m,a-m))
 return eq[rem],ineq,d
@jax.jit
def eq(v):return vals(v)[0]
@jax.jit
def ine(v,s):
 _,a,d=vals(v);return jnp.r_[a,s*d-v[-1]*.02]
je=jax.jit(jax.jacfwd(eq));ji=jax.jit(jax.jacfwd(ine));obj=lambda v:-v[-1];grad=np.r_[np.zeros(32),-1.]
sgs=json.loads((P/'ring4_full_signs.json').read_text());assert len(sgs)==16
rng=np.random.default_rng(1926);bounds=[(-3,3)]*7+[(-.375,.375)]*7+[(-2,2)]*12+[(-6,6)]*6+[(-1,.1)];best=-1.;wins=[]
for i,p in enumerate(sgs):
 s=np.array([1. if b=='+' else -1. for b in p]);c0=[{'type':'eq','fun':eq,'jac':je},{'type':'ineq','fun':lambda v:ine(v,s),'jac':lambda v:ji(v,s)}];b=-1.;me=1e9
 for k in range(Nstart):
  v=vseed.copy();v[:32]+=rng.normal(0,.02 if k%2==0 else .08,32);v[-1]=-.01
  sol=minimize(obj,v,jac=lambda v:grad,constraints=c0,bounds=bounds,method='SLSQP',options={'maxiter':180,'ftol':1e-11})
  e=float(np.max(abs(eq(sol.x))));sl=float(np.min(ine(sol.x,s)));m=sol.x[-1];me=min(me,e)
  if e<1e-7 and sl>-1e-7:
   b=max(b,m)
   if m>best:best=m;print('new best',i,k,m,'eq',e,'slack',sl,flush=True)
   if m>1e-7 and e<1e-9 and sl>-1e-9:
    print('CANDIDATE EMBEDDING',i,k,m,e,sl,flush=True);np.savez(P/'ring4_candidate.npz',v=sol.x,sign=s,t=t);sys.exit(0)
 print('chamber',i,'best margin',b,'min eq residual',me,flush=True)
print('DONE best',best,'No proof of infeasibility',flush=True)
