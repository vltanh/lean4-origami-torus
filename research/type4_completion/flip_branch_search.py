#!/usr/bin/env python3
"""Sample the seven-parameter nonsingular flip chart at the hexagonal modulus.

Numerical research diagnostic only: no inference of infeasibility from
the sampled candidates, no interval certification of residuals or signs.
Requires NumPy (batched linear solves / SVD).
"""
from itertools import combinations
from collections import Counter
import argparse
import numpy as np

F = [tuple(map(int,s)) for s in
     '015 052 031 024 043 136 145 174 167 264 257 276 347 356 375 465'.split()]
E = sorted({tuple(sorted(e)) for f in F for e in combinations(f,2)})
K = {'04':(0,-1),'24':(0,-1),'26':(-1,0),'27':(-1,0),'34':(0,-1),
     '35':(1,-1),'37':(0,-1),'46':(-1,1),'56':(-1,1),'57':(-1,0)}
x, y = .5, np.sqrt(.75)
shift = np.array([(m+n*x,n*y) for i,j in E for m,n in [K.get(f'{i}{j}',(0,0))]])
I,J = np.array(E).T
D=np.zeros((8,8,2));mask=np.zeros((8,8),bool)
for (i,j),v in zip(E,shift):D[i,j]=v;D[j,i]=-v;mask[i,j]=mask[j,i]=True
D[2,3]=D[2,5]+D[5,3];D[3,2]=-D[2,3];mask[2,3]=mask[3,2]=True
quad=[5,7,2,3]
comp=np.array([[1,0],[-1,0],[.5,y],[-.5,-y],[-.5,y],[.5,-y]])
nc=np.vstack([np.zeros(2),comp])
rng=np.random.default_rng(808)
Fnew=[f for f in F if not {5,7}<=set(f)]+[(5,3,2),(7,2,3)]
stat=Counter()

def keep(R,Q,known,stage):
    if len(R)==0:return R,Q
    ok=np.isfinite(R).all(axis=(1,2))&np.isfinite(Q).all(axis=(1,2))
    for i,j in combinations(sorted(known),2):
        diff=Q[:,j]-Q[:,i]+D[i,j];d=R[:,j]-R[:,i];d2=(d*d).sum(1)
        if mask[i,j]:
            # The six Voronoi inequalities are complete at the hexagon.
            ok&=(np.max(np.abs(diff@comp.T),axis=1)<.5-1e-9)
            ok&=(abs((diff*diff).sum(1)-d2)<1e-8)
        else:
            # Necessary contraction against seven particular translates;
            # not a complete check for arbitrary lifts of nonedges.
            ds=Q[:,j]-Q[:,i]
            dmin=((ds[:,None,:]+nc[None,:,:])**2).sum(2).min(1)
            ok&=dmin>=d2-1e-9
    for f in F+Fnew[-2:]:
        if not set(f)<=set(known):continue
        a,b,c=f;u=Q[:,b]-Q[:,a]+D[a,b];v=Q[:,c]-Q[:,a]+D[a,c]
        ok&=u[:,0]*v[:,1]-u[:,1]*v[:,0]>1e-9
    stat[stage]+=int(ok.sum())
    return R[ok],Q[ok]

def newquad(N):
    u=rng.uniform(-.58,.58,(N,2));v=rng.uniform(-.58,.58,(N,2))
    s=rng.uniform(.005,.995,N);t=rng.uniform(.005,.995,N)
    # Half uniform, half perturbations around the explicit intrinsic seed.
    if N>2:
        n=N//2;sd=rng.choice([.025,.08,.18,.35],n)
        u[:n]=[-.4,0]+rng.normal(0,1,(n,2))*sd[:,None]
        v[:n]=[0,.46188]+rng.normal(0,1,(n,2))*sd[:,None]
        s[:n]=np.clip(.5+rng.normal(0,.23,n),.005,.995)
        t[:n]=np.clip(.75+rng.normal(0,.23,n),.005,.995)
    A=np.stack([np.zeros_like(u),u,s[:,None]*u-t[:,None]*v,s[:,None]*u+(1-t)[:,None]*v],axis=1)
    ok=u[:,0]*v[:,1]-u[:,1]*v[:,0]<-1e-7
    for i,j in combinations(range(4),2):
        ok&=np.max(abs((A[:,i]-A[:,j])@comp.T),axis=1)<.5-1e-8
    A=A[ok];lam=np.stack([1-s,s,t-1,-t],axis=1)[ok]
    stat['quad']+=len(A)
    R=np.zeros((len(A),8,3));Q=np.zeros((len(A),8,2))
    R[:,quad,:2]=A;Q[:,quad]=A-D[5,quad]
    # Linear compatibility at 4; choose points on the feasible interval.
    S=Q[:,quad]-D[quad,4]
    J=(lam[:,:,None]*S).sum(1)
    rhs=.5*(lam*((S*S).sum(2)-(A*A).sum(2))).sum(1)
    jj=(J*J).sum(1)
    base=rhs[:,None]*J/jj[:,None]
    e=np.stack([-J[:,1],J[:,0]],1)/np.sqrt(jj)[:,None]
    B=.5-(base[:,None,:]-S)@comp.T
    L=np.broadcast_to(e[:,None,:]@comp.T,B.shape)
    with np.errstate(divide='ignore',invalid='ignore'):
        lower=np.max(np.where(L<-1e-12,B/L,-np.inf),axis=(1,2))
        upper=np.min(np.where(L>1e-12,B/L,np.inf),axis=(1,2))
    ok=(lower<upper)&np.isfinite(lower)&np.isfinite(upper)&~np.any((abs(L)<=1e-12)&(B<=0),axis=(1,2))
    R=R[ok];Q=Q[ok];A=A[ok];S=S[ok];base=base[ok];e=e[ok]
    lower=lower[ok];upper=upper[ok];stat['p4line']+=len(R)
    nrep=5
    R=np.repeat(R,nrep,axis=0);Q=np.repeat(Q,nrep,axis=0)
    A=np.repeat(A,nrep,axis=0);S=np.repeat(S,nrep,axis=0)
    base=np.repeat(base,nrep,axis=0);e=np.repeat(e,nrep,axis=0)
    lower=np.repeat(lower,nrep);upper=np.repeat(upper,nrep)
    P=base+(lower+(upper-lower)*rng.uniform(.001,.999,len(base)))[:,None]*e
    d2=((P[:,None,:]-S)**2).sum(2);M=A[:,1:3]-A[:,:1]
    C=((A[:,1:3]**2).sum(2)-(A[:,:1]**2).sum(2)-d2[:,1:3]+d2[:,:1])/2
    U=np.linalg.solve(M,C[...,None])[...,0]
    H=d2[:,0]-((U-A[:,0])**2).sum(1);ok=H>1e-10
    R=R[ok];Q=Q[ok];R[:,4,:2]=U[ok];R[:,4,2]=np.sqrt(H[ok]);Q[:,4]=P[ok]
    stat['p4height']+=len(R)
    return keep(R,Q,quad+[4],'core4')

def later(R,Q,i,N,known):
    if not len(R):return R,Q
    A=R[:,N];S=Q[:,N]-D[N,i]
    M=np.concatenate([A[:,1:]-A[:,:1],-(S[:,1:]-S[:,:1])],axis=2)
    C=((A[:,1:]**2).sum(2)-(A[:,:1]**2).sum(2)-(S[:,1:]**2).sum(2)+(S[:,:1]**2).sum(2))/2
    U,ss,V=np.linalg.svd(M,full_matrices=True)
    ok=ss[:,-1]>1e-9
    R=R[ok];Q=Q[ok];A=A[ok];S=S[ok];U=U[ok];ss=ss[ok];V=V[ok];C=C[ok]
    P=np.einsum('nji,nj->ni',V[:,:4],np.einsum('nji,nj->ni',U,C)/ss)
    e=V[:,4];center=np.concatenate([A[:,0],S[:,0]],axis=1)
    P0=P-center;sig=np.array([1,1,1,-1,-1])
    a=(e*e*sig).sum(1);b=2*(e*P0*sig).sum(1);c=(P0*P0*sig).sum(1)
    disc=b*b-4*a*c
    # This numerical chart deliberately skips singular, linear and
    # near-degenerate quadratics; the mathematical coverage proof does not.
    ok=(disc>=0)&(abs(a)>1e-12)
    R=R[ok];Q=Q[ok];a=a[ok];b=b[ok];c=c[ok];disc=disc[ok];P=P[ok];e=e[ok]
    stat['roots'+str(i)]+=2*len(R)
    root=np.stack([(-b-np.sqrt(disc))/(2*a),(-b+np.sqrt(disc))/(2*a)],axis=1)
    coords=(P[:,None,:]+root[:,:,None]*e[:,None,:]).reshape(-1,5)
    R=np.repeat(R,2,axis=0);Q=np.repeat(Q,2,axis=0)
    R[:,i]=coords[:,:3];Q[:,i]=coords[:,3:]
    ok=abs(R[:,i,2])>1e-8
    if i==1:ok&=R[:,1,2]*R[:,6,2]>0
    if i==0:ok&=R[:,0,2]>0
    return keep(R[ok],Q[ok],known+[i],'accepted'+str(i))

QARR=np.array(list(combinations(range(8),4)));a,b,c,d=QARR.T
idx={tuple(q):i for i,q in enumerate(QARR)}
PAIRS=np.array([list(e)+list(f) for e in E for f in sorted(map(lambda f:tuple(sorted(f)),F))
                if set(e).isdisjoint(f)])
assert len(PAIRS)==140
def parity(q):return (-1)**sum(i>j for i,j in combinations(q,2))
I5=np.array([[idx[tuple(sorted(np.delete(pair,k)))] for k in range(5)] for pair in PAIRS])
S5=np.array([[(-1)**k*parity(np.delete(pair,k))*(1 if k<2 else -1)
              for k in range(5)] for pair in PAIRS])
zero=idx[tuple(sorted(quad))]

def crossing_scores(R):
    A=R[:,b]-R[:,a];B=R[:,c]-R[:,a];C=R[:,d]-R[:,a]
    vals=np.einsum('nqi,nqi->nq',A,np.cross(B,C))
    vals[:,zero]=0 # the quad is coplanar by construction
    co=vals[:,I5]*S5;neg=co.min(2);pos=co.max(2)
    # Count potential crossings, including ambiguous zero signs.
    hits=((neg>=-1e-10)|(pos<=1e-10)).sum(1)
    viol=np.maximum(0,np.maximum(neg,-pos))
    return hits,(viol**2).sum(1)**.5

def run(N,nbatch,output):
    best=100;best_score=float('inf');nfull=0
    for k in range(nbatch):
        R,Q=newquad(N)
        R,Q=later(R,Q,6,[5,7,2,3,4],quad+[4])
        R,Q=later(R,Q,1,[5,7,3,4,6],quad+[4,6])
        R,Q=later(R,Q,0,[5,2,3,4,1],quad+[4,6,1])
        nfull+=len(R)
        if not len(R):continue
        hits,score=crossing_scores(R)
        for u in set([np.argmin(hits),np.argmin(score)]):
            if hits[u]<best:
                best=int(hits[u])
                print('BEST potential crossings',best,'score',score[u],'batch',k,
                      'metric residual',max(abs(((R[u,J]-R[u,I])**2).sum(1)-((Q[u,J]-Q[u,I]+shift)**2).sum(1))),flush=True)
                if output:np.savez(output,R=R[u],Q=Q[u],hits=hits[u])
            best_score=min(best_score,float(score[u]))
            if hits[u]==0:
                print('ZERO crossing count: numerical candidate requiring full exact validation',flush=True)
                if output:np.savez(output,R=R[u],Q=Q[u],hits=hits[u])
                return
        if k%10==0:print('batch',k,'full',nfull,'stats',dict(stat),flush=True)
    print('FINAL',dict(stat),'full',nfull,'best',best,'score',best_score,flush=True)

if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--batch-size',type=int,default=20000)
    p.add_argument('--batches',type=int,default=100)
    p.add_argument('--output',help='optional .npz of best crossing-count candidate')
    args=p.parse_args()
    run(args.batch_size,args.batches,args.output)
