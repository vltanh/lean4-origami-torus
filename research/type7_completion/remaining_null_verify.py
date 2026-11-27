#!/usr/bin/env python3
"""Independent exact checks for the quadratic face-023 metric chart."""
from fractions import Fraction as F
from itertools import combinations,permutations
import re
import sympy as sym
import remaining_null_metric as q
from remaining_verify import parse_count
from verify_projected_metric import parse,evaluate


def det(M):
 def product(xs):
  z=F(1)
  for x in xs:z*=x
  return z
 n=len(M)
 return sum((-1)**sum(p[i]>p[j]for i,j in combinations(range(n),2))*product(M[i][p[i]]for i in range(n))for p in permutations(range(n)))

def cancelled_factor(points,axes,env,y):
 """Independently recover the positive scale removed from eight minors."""
 if (len(points)==4 and {0,2,3}<=set(points) and axes==(0,1,2)) or (points==(0,2,3) and axes==(0,2)):
  t=F(1,y*y)
  factor=env['x2']*(1-2*t*env['gamma3'])-env['x3']*(1-2*t*env['gamma2'])
 elif points in ((2,3,6),(2,3,7)) and axes==(0,1):factor=env['x2']-env['x3']
 else:return F(1)
 assert factor>0
 return factor


def check(y,zero=False):
 text,meta=q.generate(y);forms=parse(text);t=F(1,y*y)
 declarations=[x[1]for x in forms if x[0]=='declare-fun' and x[3]=='Real']
 assert len(declarations)==29
 env={name:F((i*7)%13-6,17)for i,name in enumerate(declarations)}
 env.update(x2=F(1,10),gamma2=F(1,7),x3=-F(1,5),gamma3=F(1,9),z1=-F(1,3))
 if zero:
  for i in q.FREE:env[f'u{i}']=env[f'z{i}']=env[f'zeta{i}']=F(0)
 x=[F(0)]+[env[f'x{i}']for i in range(1,8)];g=[F(0)]+[env[f'gamma{i}']for i in range(1,8)]
 U={0:F(0),2:x[2],3:x[3]};Z={0:F(0),2:F(0),3:F(0)};zz={0:F(0),2:g[2],3:g[3]}
 for i in q.FREE:U[i],Z[i],zz[i]=(env[f'{s}{i}']for s in ('u','z','zeta'))
 c={i:int(i in q.p.CAP_B)for i in range(8)}
 spatial={i:(U[i],-F(y,2)*c[i]+zz[i]/y,Z[i])for i in range(8)}
 incidence={i:(U[i],Z[i],F(c[i])-2*t*zz[i])for i in range(8)}
 faces,K,edges,xb,yb,kx,ky=q.d.load_data()
 def dist(i,j):return sum((spatial[j][k]-spatial[i][k])**2 for k in range(3))
 def physical_residual(i,j):
  X=x[j]-x[i]+kx[i,j];V=ky[i,j]+t*(g[j]-g[i])
  return dist(i,j)-X*X-y*y*V*V
 degrees={name:1 for name in declarations}
 def degree(term):
  if isinstance(term,str):return degrees.get(term,0)
  op,*args=term;ds=list(map(degree,args))
  if op in ('+','-'):return max(ds,default=0)
  if op=='*':return sum(ds)
  if op=='/':assert ds[1]==0;return ds[0]
  raise ValueError(op)
 metrics=minors=0
 for f in forms:
  if f[0]!='define-fun' or f[1]=='long_link':continue
  name=f[1];env[name]=evaluate(f[4],env);degrees[name]=degree(f[4])
  if name.startswith('metric'):
   i,j=map(int,name[6:]);k={ (1,2):1,(2,5):5,(2,7):7}.get((i,j))
   # The chosen difference residual equals edge(0,k)-edge(2,k),
   # using the anchor02 equality, which is identically satisfied here.
   expected=physical_residual(i,j) if k is None else physical_residual(0,k)-physical_residual(2,k)
   assert env[name]==expected,(name,env[name]-expected)
   assert degrees[name]<=2;metrics+=1
  if name.startswith('nonedge'):
   i,j=map(int,name[7:]);assert env[name]==dist(i,j);assert degrees[name]<=2
  mm=re.fullmatch(r'a([0-7]+)c([012]+)',name)
  if mm:
   pts,axes=[tuple(map(int,a))for a in mm.groups()];a,*rest=pts
   expected=det([[incidence[b][j]-incidence[a][j]for j in axes]for b in rest])
   if len({c[i]for i in pts})==1 and 2 in axes:expected/=2*t
   expected/=cancelled_factor(pts,axes,env,y)
   assert env[name]==expected,(name,env[name]-expected);minors+=1
  if name.startswith('projected_area_'):assert degrees[name]<=2
 assert metrics==21 and minors==322
 assert all(physical_residual(*e)==0 for e in ((0,2),(0,3),(2,3)))
 for name,(i,j),(k,l) in q.p.determinant_pairs():
  area=(U[j]-U[i])*(Z[l]-Z[k])-(Z[j]-Z[i])*(U[l]-U[k])
  assert env['projected_area_'+name]==area
 # The six normalized atoms agree with the original area inequalities,
 # including equality and zero.  They are linear in the unknowns.
 union=forms[-2][1];assert union[0]=='or' and len(union)==25
 h23=env['x2']-env['x3'];assert h23>0
 cancelled=0
 for test,(name,a,b) in zip(union[1:],q.p.relative_comparisons()):
  h=lambda e:-evaluate(parse(q.p.directed_symbol('X',e))[0],env)
  original=abs(env['projected_area_'+name])<=53*t*h(a)*h(b)
  assert test[0]=='and' and all(evaluate(atom,env)for atom in test[1:])==original
  if (2,3) in (a,b):
   other=b if a==(2,3)else a;i,j=other
   assert abs(env['projected_area_'+name])==h23*abs(Z[j]-Z[i])
   assert max(degree(test[1][1]),degree(test[1][2]))<=1
   cancelled+=1
 assert cancelled==meta['cancelled_area_atoms']==6
 # For every full determinant the incidence map preserves orientation.
 for pts in combinations(range(8),4):
  a,*rest=pts
  ds=det([[spatial[b][k]-spatial[a][k]for k in range(3)]for b in rest])
  di=det([[incidence[b][k]-incidence[a][k]for k in range(3)]for b in rest])
  assert di==F(2,y)*ds
 # True same-cap zero minors remain zero after the positive rescaling.
 return text,meta


def constants_and_paths():
 t=F(1,64)
 assert (1+t/4)**2+t < F(33,32)**2
 assert 1-3*t/4==F(253,256)>0
 assert 6*F(33,32)/F(253,256)<7
 assert (36+14)*F(33,32)/F(253,256)==F(13200,253)<53
 assert F(3,8)+(F(1,2)+t)<F(7,4)
 assert (F(1,2)+t)/2<F(7,4)
 # Any nonzero vertical translate has squared length >16; the nearer
 # of the two horizontal arcs has squared length <1.
 gamma_bound=F(1,4)+t/2
 assert t*gamma_bound<F(1,2)
 assert F(1,4)+t*gamma_bound**2<1
 _,K,_,xb,yb,kx,ky=q.d.load_data()
 for cap in (q.p.CAP_A,q.p.CAP_B):
  for k in (0,1):
   a,b,c=cap[k:k+3]
   m1,n1=[K[a,b][j]+K[b,c][j]for j in (0,1)]
   assert yb[c]-yb[a]+n1==0
   assert xb[c]-xb[a]+m1+F(n1,2)==kx[a,b]+kx[b,c]
   # The other arc differs by the full (-1,0) cap period.
   other=(cap[(k-1)%4],)
   m2,n2=[K[a,other[0]][j]+K[other[0],c][j]for j in (0,1)]
   assert (m2-m1,n2-n1)==(1,0)
 print('PASS exact uniform frame, area-transfer and two-arc constants')


def symbolic_cancellations():
 x2,x3,g2,g3,t=sym.symbols('x2 x3 g2 g3 t')
 coords={0:sym.zeros(3,1),2:sym.Matrix([x2,0,1-2*t*g2]),3:sym.Matrix([x3,0,1-2*t*g3])}
 for i in q.FREE:coords[i]=sym.Matrix(sym.symbols(f'u{i} z{i} H{i}'))
 scale=x2*(1-2*t*g3)-x3*(1-2*t*g2)
 for i in q.FREE:
  points=tuple(sorted((0,2,3,i)));a,*rest=points
  actual=sym.Matrix.hstack(*(coords[j]-coords[a]for j in rest)).det()
  assert sym.expand(actual+scale*coords[i][1])==0
 assert sym.expand(sym.Matrix([[x2,1-2*t*g2],[x3,1-2*t*g3]]).det()-scale)==0
 for i in (6,7):
  actual=sym.Matrix([[coords[j][k]-coords[2][k]for k in (0,1)]for j in (3,i)]).det()
  assert sym.expand(actual+(x2-x3)*coords[i][1])==0
 print('PASS eight symbolic positive-factor identities, including all zero boundaries')


def main():
 for y,zero in ((8,False),(10**6,False),(8,True)):
  text,meta=check(y,zero)
  print(f'PASS y={y}, zero fixture={zero}: 21 quadratic metric equations, 322 minors')
 constants_and_paths();symbolic_cancellations();text,meta=q.generate();count=parse_count(text)
 assert meta['metric_degree_bound']==2 and meta['nonedge_translate_inequalities']==8
 assert text.count('(declare-fun ')==29+312
 print(f'PASS full query parses: {count} assertions, {len(text)} bytes')
 print('No whole-phase exclusion is claimed.')

if __name__=='__main__':main()
