#!/usr/bin/env python3
"""Exact outward-rounded dyadic interval pruning of the full B1.1 core.
No floating arithmetic is used for exclusion. All exceptional denominators
and unresolved inequalities are kept (never interpreted as infeasibility).
"""
from fractions import Fraction as Fq
from itertools import combinations, product
from pathlib import Path
from math import isqrt
import json,sys,collections,argparse
P=Path(__file__).resolve().parent;sys.path.insert(0,str(P.parent.parent))
import focused_system as fs
from satgeom import Q,lit
B=1<<100
class I:
 __slots__=('l','h')
 def __init__(self,a,b=None):
  if b is not None:self.l,self.h=a,b;return
  if isinstance(a,I):self.l,self.h=a.l,a.h;return
  q=Fq(a);self.l=q.numerator*B//q.denominator;self.h=-((-q.numerator*B)//q.denominator)
 def __add__(a,b):b=I(b);return I(a.l+b.l,a.h+b.h)
 __radd__=__add__
 def __neg__(a):return I(-a.h,-a.l)
 def __sub__(a,b):return a+-I(b)
 def __rsub__(a,b):return I(b)+-a
 def __mul__(a,b):
  b=I(b);v=[x*y for x in (a.l,a.h) for y in (b.l,b.h)];return I(min(v)//B,-((-max(v))//B))
 __rmul__=__mul__
 def __truediv__(a,b):
  b=I(b)
  if b.l<=0<=b.h:raise ZeroDivisionError
  return I(min(x*B//y for x in (a.l,a.h) for y in (b.l,b.h)),max(-((-x*B)//y) for x in (a.l,a.h) for y in (b.l,b.h)))
 def sq(a):
  lo=0 if a.l<=0<=a.h else min(a.l*a.l,a.h*a.h);hi=max(a.l*a.l,a.h*a.h);return I(lo//B,-((-hi)//B))
 def sqrt(a):
  if a.h<0:raise ValueError('negative radicand')
  l=isqrt(max(a.l,0)*B);h=isqrt(a.h*B);return I(l,h+(h*h<a.h*B))
 def intersect(a,b):
  b=I(b);lo=max(a.l,b.l);hi=min(a.h,b.h);return None if lo>hi else I(lo,hi)
 def __repr__(a):return f'[{a.l/B:.12g},{a.h/B:.12g}]' # diagnostic only

def phys(a,b):return [I(Fq(2*a+b,2)),I(Fq(b,2))]
K={e:phys(*k) for e,k in fs.K.items()};lat=[phys(1,0),phys(0,1),phys(-1,1)];shift=[phys(a,b) for a,b in product(range(-1,2),repeat=2)]
def add(a,b):return [x+y for x,y in zip(a,b)]
def sub(a,b):return [x-y for x,y in zip(a,b)]
def sc(k,a):return [k*x for x in a]
def dot(a,b):return a[0]*b[0]+3*a[1]*b[1]+(a[2]*b[2] if len(a)==len(b)==3 else 0)
def norm(a):return a[0].sq()+3*a[1].sq()+(a[2].sq() if len(a)==3 else 0)
def cross(a,b):return a[0]*b[1]-a[1]*b[0]
def det3(a,b,c):return a[0]*cross(b[1:],c[1:])-a[1]*(b[0]*c[2]-b[2]*c[0])+a[2]*cross(b,c)
def sl(p,i,j,k=None):
 if k is None:k=K[i,j]
 return -dot(sub(p[j],p[i]),k)-norm(k)/2
# In gauge v, the shift for edge ij is K_ij + K_vi - K_vj.
def gauge_k(v,i,j):
 g=lambda j:fs.K[v,j] if j!=v else (0,0)
 return tuple(fs.K[i,j][t]+g(i)[t]-g(j)[t] for t in range(2))
G=[(1,2,5,3,4,0,7),(2,1,5,4,3,0,6),(5,1,2,3,4,7,6)]
for v,a,b,c,d,l,m in G:
 for i,j in [(a,b),(a,l),(b,m),(c,l),(d,m)]:assert gauge_k(v,i,j)==(0,0),(v,i,j)
 for i,j in [(a,m),(b,l),(a,c),(b,c),(a,d),(b,d),(c,m),(d,l)]:assert gauge_k(v,i,j)!=(0,0),(v,i,j)
 assert (min(c,d),max(c,d)) not in fs.E

def gsl(p,v,i,j):
 k=phys(*gauge_k(v,i,j));u=add(sub(p[j],p[i]),K[i,j]);return norm(k)/2-dot(u,k)
def product_test(p):
 for v,a,b,c,d,l,m in G:
  # Opposite roots require s_ac*s_bd < s_ad*s_bc (proof in README).
  if (gsl(p,v,a,d)*gsl(p,v,b,c)-gsl(p,v,a,c)*gsl(p,v,b,d)).h<=0:return False
 return True

C=[2,3,4,5];LE=[0,6,7];ALL=[0,2,3,4,5,6,7];VI={(i,k):2*j+k for j,i in enumerate(ALL) for k in range(2)}
# Strict nearest-image inequalities on every edge, in exact integer form.
LIN=[]
for i,j in fs.E:
 a,b=fs.K[i,j]
 for u,v in [(1,0),(0,1),(-1,1)]:
  coeff=(2*u+v,3*v);const=Fq((2*u+v)*(2*a+b)+3*v*b,2);assert const.denominator==1
  t=[]
  for sgn in [1,-1]:
   row=[]
   for ix,z in [(i,-sgn),(j,sgn)]:
    if ix!=1:row.extend((VI[ix,k],z*c) for k,c in enumerate(coeff) if c)
   LIN.append((row,(1-sgn*int(const))*B))

def propagate(box,sweeps=3):
 # Round bounds outward, so the result encloses all solutions of strict rows.
 box=list(box)
 for _ in range(sweeps):
  change=False
  for row,rhs in LIN:
   mn=sum(a*(box[k].l if a>0 else box[k].h) for k,a in row)
   if mn>=rhs:return None
   for k,a in row:
    z=box[k];v=rhs-(mn-a*(z.l if a>0 else z.h))
    # recompute from current bounds in other terms for soundness after changes
    v=rhs-sum(c*(box[j].l if c>0 else box[j].h) for j,c in row if j!=k)
    if a>0:
     hi=min(z.h,-((-v)//a));new=I(z.l,hi)
    else:
     lo=max(z.l,v//a);new=I(lo,z.h)
    if new.l>new.h:return None
    if (new.l,new.h)!=(z.l,z.h):change=True;box[k]=new
  if not change:break
 return box

def unpack(box):return {1:[I(0),I(0)],**{i:[box[VI[i,k]] for k in range(2)] for i in ALL}}
ch=json.loads((P.parent/'branches.json').read_text())[0];assert ch['id']=='B1.1';an=lit((1,2,5,3))
SS=[]
for pat in ch['chambers']:
 s=[1 if c=='+' else -1 for c in pat];d=s[abs(an)-1]*(1 if an>0 else -1);SS.append([z*d for z in s])
COMMON={q:SS[0][j] for j,q in enumerate(Q) if all(t[j]==SS[0][j] for t in SS)};CL=set(fs.cl);assert len(COMMON)==64
E=set(fs.E);NE=set(combinations(range(8),2))-E

def check(p,r,V):
 # V is the set of assigned vertices. Others are not used.
 for i,j in E:
  if i not in V or j not in V:continue
  u=add(sub(p[j],p[i]),K[i,j]);
  if any((I(1)-sg*2*dot(u,w)).h<=0 for w in lat for sg in (1,-1)):return False
 for a,b,c in fs.F:
  if {a,b,c}<=V and cross(add(sub(p[b],p[a]),K[a,b]),add(sub(p[c],p[a]),K[a,c])).l>=0:return False
 for q,s in COMMON.items():
  if set(q)<=V:
   a,*vs=q;w=s*det3(*(sub(r[i],r[a]) for i in vs))
   if w.h<0 or (q in CL and w.h<=0):return False
 for i,j in NE:
  if {i,j}<=V:
   d=norm(sub(r[i],r[j]));
   if d.l>I(Fq(1,3)).h:return False
   for k in shift:
    if (norm(add(sub(p[j],p[i]),k))-d).h<0:return False
 if len(V)==8:
  # A weak nonclique sign may vanish. The chamber disjunction is necessary.
  D=[det3(*(sub(r[i],r[q[0]]) for i in q[1:])) for q in Q]
  if not any(all((s*z).h>=0 if q not in CL else (s*z).h>0 for q,s,z in zip(Q,pat,D)) for pat in SS):return False
 return True

def coeffs(p,r,j,sg):
 # Solve for physical projection using the two anchor inner products.
 def gram(i,j,q):return dot(p[i],q)-dot(sub(q,p[i]),K[i,j])-norm(K[i,j])/2
 def solve(M,b):
  d=cross(*M)
  if d.l<=0<=d.h:raise ZeroDivisionError
  return [(b[0]*M[1][1]-b[1]*M[0][1])/d,(M[0][0]*b[1]-M[1][0]*b[0])/d]
 M=[[p[i][0],3*p[i][1]] for i in (2,5)]
 def projection(q):return solve(M,[gram(i,j,q) for i in (2,5)])
 # Evaluate affine coefficients directly instead of subtracting interval evaluations
 # at 0 and 1 (which unnecessarily widens them).
 h0=projection([I(0),I(0)])
 H=[]
 for k in range(2):
  # gradient in q_k of gram(i,j,q) = metric_k*(p_i-k_ij)_k
  H.append(solve(M,[(1 if k==0 else 3)*(p[i][k]-K[i,j][k]) for i in (2,5)]))
 # h(q) = h0 + H[0]*q_x + H[1]*q_y
 N=[];b=[];h=[]
 for i in (3,4):
  N.append([(1 if k==0 else 3)*(p[i][k]-K[i,j][k])-dot(r[i][:2],H[k]) for k in range(2)])
  b.append(dot(r[i][:2],h0)-gram(i,j,[I(0),I(0)]))
  h.append(sg*r[i][2])
 q0=solve(N,b);q1=solve(N,h)
 t0=add(h0,add(sc(q0[0],H[0]),sc(q0[1],H[1])));t1=add(sc(q1[0],H[0]),sc(q1[1],H[1]))
 return (I(1)+norm(t1)-norm(q1),2*(dot(t0,t1)-dot(q0,q1)),norm(t0)-norm(q0)),q0,q1,t0,t1

def root_intervals(co):
 a,b,c=co;bound=I(0,I(Fq(3,5)).h) # |height| <= 1/sqrt(3) < 3/5
 # Nonzero positive roots only. This handles degenerate linear polynomials conservatively.
 if (a.l>=0 and b.l>=0 and c.l>=0 and (a.l>0 or b.l>0 or c.l>0)) or (a.h<=0 and b.h<=0 and c.h<=0 and (a.h<0 or b.h<0 or c.h<0)):return []
 if a.l<=0<=a.h:return [bound]
 disc=b.sq()-4*a*c
 if disc.h<0:return []
 rt=disc.sqrt();ret=[]
 for s in (-1,1):
  x=((-b+s*rt)/(2*a)).intersect(bound)
  if x is not None and x.h>0:ret.append(x)
 return ret

def polynomial_core_test(p,Delta):
 # These identities avoid inverse anchor Gram matrices; Delta is positive in
 # every actual solution, even when its interval enclosure includes zero.
 g22=norm(p[2]);g55=norm(p[5]);g25=dot(p[2],p[5]);D=3*Delta.sq()
 V={i:[sl(p,a,i) for a in (2,5)] for i in (3,4)}
 A={i:[cross(p[i],p[5]),cross(p[2],p[i])] for i in (3,4)}
 pair=lambda a,b:a[0]*b[0]+a[1]*b[1]
 adj=lambda a,b:g55*a[0]*b[0]-g25*(a[0]*b[1]+a[1]*b[0])+g22*a[1]*b[1]
 H={i:-6*Delta*pair(V[i],A[i])-adj(V[i],V[i]) for i in (3,4)}
 if any(v.h<=0 for v in H.values()):return 'polynomial root height'
 L=3*Delta*(pair(V[4],A[3])+pair(V[3],A[4]))+adj(V[3],V[4])
 if L.h<=0 or (L.sq()-H[3]*H[4]).h<0:return 'polynomial root contraction'
 # Scaled extrinsic positions, all multiplied by the same positive Delta.
 r={i:sc(Delta,p[i])+[I(0)] for i in (1,2,5)}
 for i,sg in ((3,1),(4,-1)):
  a,b=V[i]
  t=add(sc(Delta,p[i]),[a*p[5][1]-b*p[2][1],(p[2][0]*b-p[5][0]*a)/3])
  r[i]=t+[sg*(H[i]/3).sqrt()]
 for q,sg in COMMON.items():
  if set(q)<=set(r):
   a,*vs=q;w=sg*det3(*(sub(r[i],r[a]) for i in vs))
   if w.h<0 or (q in CL and w.h<=0):return 'polynomial core orientation'
 return None

def prune(box,detail=False,poly=False):
 p=unpack(box);D=cross(p[2],p[5]);
 if D.h<=0:return 'anchor'
 if not product_test(p):return 'slack products'
 if poly:
  why=polynomial_core_test(p,D)
  if why is not None:return why
 if D.l<=0:return None
 # Root projections via Gram equations. No division by root heights.
 r={i:p[i]+[I(0)] for i in [1,2,5]}
 for i,sg in [(3,1),(4,-1)]:
  w=[dot(p[a],p[i])+sl(p,a,i) for a in [2,5]]
  t=[(w[0]*p[5][1]-w[1]*p[2][1])/D,(p[2][0]*w[1]-p[5][0]*w[0])/(3*D)]
  h=norm(p[i])-norm(t)
  if h.h<=0:return 'root height'
  r[i]=t+[sg*h.sqrt()]
 V=set(C)|{1}
 if not check(p,r,V):return 'core constraints'
 opts={}
 for j,sg in [(0,1),(6,-1),(7,-1)]:
  try:co,q0,q1,t0,t1=coeffs(p,r,j,sg)
  except ZeroDivisionError:return None # singular projection system remains open
  if detail:print('leaf',j,'height coefficients',co)
  xs=root_intervals(co)
  if not xs:return f'leaf {j} no positive root'
  opts[j]=[]
  for z in xs:
   pp=add(q0,sc(z,q1));rr=add(t0,sc(z,t1))+[sg*z]
   pp=[a.intersect(b) for a,b in zip(pp,p[j])]
   if any(a is None for a in pp):continue
   p1={**p,j:pp};r1={**r,j:rr}
   if check(p1,r1,V|{j}):opts[j].append((pp,rr))
  if not opts[j]:return f'leaf {j} constraints'
 # All combinations of the surviving height intervals; test mutual nonedge distances
 # and every determinant, including those containing two or three leaves.
 for combo in product(*(opts[j] for j in LE)):
  pp=dict(p);rr=dict(r)
  for j,(pj,rj) in zip(LE,combo):pp[j]=pj;rr[j]=rj
  if check(pp,rr,set(range(8))):return None
 return 'coupled leaf constraints'

def initial():
 return [I(-I(Fq(1,2 if k%2==0 else 3)).h,I(Fq(1,2 if k%2==0 else 3)).h) for k in range(14)]
def witness_test():
 # Replay the earlier exact six-vertex witness, then check its actual radical
 # core is contained in the rational box. The decimal centers are not evidence.
 from importlib.util import spec_from_file_location,module_from_spec
 spec=spec_from_file_location('prior_six',P.parent/'b11_core'/'verify_six.py');old=module_from_spec(spec);spec.loader.exec_module(old)
 x3=old.Fr('-0.281057368722');x4=old.Fr('0.064852921665')
 pold=dict(old.p)
 for i,x,want in [(3,x3,-1),(4,x4,1)]:
  _,q,_=next(t for t in old.root(i,x) if t[0]==want);pold[i]=q
 # old p_i = new p_i - new p5 + K[5,i], origin5 -> origin1.
 qold={i:[old.I(x) for x in pold[i]] for i in [1,2,3,4,5]}
 center={2:('0.370172461232','0.049030942559'),3:('0.161261472737','-0.267213319645047'),4:('-0.492828236876','-0.092695539023835'),5:('-0.057681158541','0.100369943614')}
 for i in C:
  g1=fs.K[5,1];gi=(0,0) if i==5 else fs.K[5,i];k=old.phys(*(a-b for a,b in zip(g1,gi)))
  q=[x-y+z for x,y,z in zip(qold[i],qold[1],k)]
  for x,c in zip(q,center[i]):
   c=Fq(c);rad=Fq(1,10**10);assert Fq(x.l,old.B)>=c-rad and Fq(x.h,old.B)<=c+rad
 print('PASS: old exact radical core lies inside the smallest certified box')
 for rad in [Fq(1,10**k) for k in (10,9,8,7,6,5)]:
  box=initial()
  for i in C:
   for k in range(2):
    a=Fq(center[i][k]);box[VI[i,k]]=I(I(a-rad).l,I(a+rad).h)
  b=propagate(box);why='linear' if b is None else prune(b)
  print('core box radius',rad,'result',why)
  assert why is not None

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--budget',type=int,default=5000);ap.add_argument('--depth',type=int,default=32);ap.add_argument('--output',default='frontier.json');ap.add_argument('--witness',action='store_true');ap.add_argument('--poly',action='store_true');a=ap.parse_args()
 if a.witness:witness_test();return
 # Breadth-first deterministic partition; every split covers its parent, including midpoint.
 work=collections.deque([(initial(),0)]);stats=collections.Counter();stop=[];done=0;maxdepth=0
 while work and done<a.budget:
  box,depth=work.popleft();done+=1;maxdepth=max(maxdepth,depth)
  tight=propagate(box)
  why='nearest linear' if tight is None else prune(tight,poly=a.poly)
  if why is not None:stats[why]+=1;continue
  if depth>=a.depth:stop.append((tight,depth));continue
  # split only the 8 core coordinates, normalized by initial widths
  k=max((VI[i,k] for i in C for k in range(2)),key=lambda k:(tight[k].h-tight[k].l)*(3 if k%2 else 2));z=tight[k];mid=(z.l+z.h)//2
  if mid in (z.l,z.h):stop.append((tight,depth));continue
  for lo,hi in [(z.l,mid),(mid,z.h)]:
   b=tight.copy();b[k]=I(lo,hi);work.append((b,depth+1))
  stats['split']+=1
  if done%1000==0:print('visited',done,'queue',len(work),'stats',dict(stats),flush=True)
 stop.extend(work)
 out={'scale':B,'budget':a.budget,'depth_limit':a.depth,'polynomial':a.poly,'visited':done,'maxdepth':maxdepth,'stats':dict(stats),'open':[[d,[[z.l,z.h] for z in b]] for b,d in stop]}
 (P/a.output).write_text(json.dumps(out,separators=(',',':'))+'\n');print('visited',done,'maxdepth',maxdepth,'exclusions',dict(stats),'unresolved frontier',len(stop));assert sum(v for k,v in stats.items() if k!='split')+len(stop)==1+stats['split']
if __name__=='__main__':main()
