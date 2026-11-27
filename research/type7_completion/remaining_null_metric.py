#!/usr/bin/env python3
"""Exact 29-variable, 21-quadratic ray-3 metric chart using face 023.

Physical points are (u_i,-y*c_i/2+zeta_i/y,z_i), c_i=I[i in cap B].
The three face vertices are fixed to their intrinsic chart: u0=zeta0=z0=0,
u2=x2,zeta2=gamma2,z2=0,u3=x3,zeta3=gamma3,z3=0.
This cancels the common y^2/4 terms, without radicals or variable division.
Every metric equation is quadratic; three are anchor-distance differences.
The incidence chart (u,z,c-2*t*zeta) has positive determinant relative to
physical coordinates. Same-cap axial minors may be divided by positive2t.
"""
import argparse,json,re
from fractions import Fraction as F
from itertools import combinations
from pathlib import Path
import direct_metric as d
p=d.p;m=d.m;V=tuple(range(8));FREE=(1,4,5,6,7)

def generate(y=10**6):
 if not isinstance(y,int) or isinstance(y,bool) or y<8:raise ValueError('integer y >= 8 required')
 t=F(1,y*y);beta=F(1,2)+t
 faces,shifts,edges,xb,yb,kx,ky=d.load_data()
 L=['(set-logic QF_NRA)'];n=0
 def dec(name):
  nonlocal n
  n+=1;L.append(f'(declare-fun {name} () Real)');return name
 def df(name,expr):L.append(f'(define-fun {name} () Real {expr})');return name
 def req(expr):L.append(m.op('assert',expr))
 def sq(x):return m.mul(x,x)
 def bound(x,b,strict=True):return m.all_([m.op('<' if strict else '<=',x,b),m.op('>' if strict else '>=',x,m.neg(b))])
 xx=['0']+[dec(f'x{i}')for i in V[1:]];gam=['0']+[dec(f'gamma{i}')for i in V[1:]]
 U={0:'0',2:xx[2],3:xx[3]};Z={0:'0',2:'0',3:'0'};zz={0:'0',2:gam[2],3:gam[3]}
 for i in FREE:U[i]=dec(f'u{i}');Z[i]=dec(f'z{i}');zz[i]=dec(f'zeta{i}')
 assert n==29
 c={i:int(i in p.CAP_B) for i in V}
 X={};Y={}
 for i,j in edges:
  X[i,j]=df(f'X{i}{j}',m.add(m.sub(xx[j],xx[i]),m.rat(kx[i,j])))
  Y[i,j]=df(f'V{i}{j}',m.add(m.rat(ky[i,j]),m.mul(m.rat(t),m.sub(gam[j],gam[i]))))
  X[j,i],Y[j,i]=m.neg(X[i,j]),m.neg(Y[i,j])
 assert all(kx[e]==0 for e in ((0,2),(0,3),(2,3)))
 c0=df('c0',m.add(sq(xx[2]),m.neg(gam[2]),m.mul(m.rat(t),sq(gam[2]))))
 den=df('den',m.add('1',m.mul(m.rat(4*t),c0)))
 req(m.op('>',den,'0'));req(m.op('<',den,m.rat(F(33,32)**2)));req(bound(c0,m.rat(F(41,20))));req(m.op('<',Z[1],'0'))
 # Long-ring shortest bounds eliminate the large extraneous gamma root.
 for ring in ((0,2,4,6),(1,3,5,7)):
  for i,j in p.ring_edges(ring):
   delta=m.sub(gam[j],gam[i]);req(m.op('>',delta,'(- (/ 1 8))'));req(m.op('<',delta,'(/ 3 8)'))
 for i in (1,3,4,5,6,7):
  req(bound(m.sub(xx[i],m.mul(str(c[i]),xx[2])),'(/ 1 2)'))
  req(bound(m.sub(gam[i],m.mul(str(c[i]),gam[2])),m.rat(F(1,4)+t/2)))
  req(bound(m.sub(zz[i],m.mul(str(c[i]),gam[2])),'(/ 7 2)'))
  req(m.op('<',m.add(sq(m.sub(U[i],m.mul(str(c[i]),xx[2]))),sq(Z[i])),m.rat(F(33,64)**2)))
 L.extend(p.relative_edge_constraints(y))
 for i,j in p.ring_edges(p.CAP_A)+p.ring_edges(p.CAP_B):
  h=m.neg(X[i,j]);du=m.sub(U[j],U[i]);dz=m.sub(Z[j],Z[i]);dt=m.sub(zz[j],zz[i]);norm=m.add(sq(du),sq(dz))
  req(bound(dt,m.mul('7',h)))
  req(m.op('>',norm,m.mul(m.rat(1-49*t),sq(h))))
  req(m.op('<',norm,m.mul(m.rat(1+t*beta*beta),sq(h))))
 metric=[]
 # Difference equations have no u_i^2,z_i^2,zeta_i^2 terms.
 differences={1:m.add(m.mul(m.rat(2*t),gam[1],gam[2]),gam[1],m.neg(m.mul('2',gam[2])),m.mul('2',xx[1],xx[2]),m.neg(xx[1]),xx[2],m.rat(-F(1,4))),
              5:m.add(m.mul(m.rat(2*t),gam[2],gam[5]),m.neg(m.mul('2',gam[2])),gam[5],m.mul('2',xx[2],xx[5]),xx[5],m.rat(F(1,4))),
              7:m.add(m.mul(m.rat(2*t),gam[2],gam[7]),m.neg(gam[7]),m.mul('2',xx[2],xx[7]),xx[2])}
 replaced={tuple(sorted((2,i))):i for i in differences}
 for i,j in edges:
  x,v=X[i,j],Y[i,j]
  req(m.op('>',m.add(m.mul(m.rat(t),sq(x)),sq(v)),'0'));req(bound(x,'(/ 1 2)'))
  for sign in (x,m.neg(x)):req(bound(m.add(v,m.mul(m.rat(t/2),sign)),m.rat(F(1,2)+t/8)))
  ell=c[j]-c[i]
  # The explicit cap-gamma bounds give |dgamma|<beta/2 on short
  # edges and |dgamma|<3/8+beta<7/4 on cross edges.  Hence the old
  # 24 phase tests, including 16 absolute-value disjunctions, follow
  # already; every cross V has the fixed sign of its nonzero ky.
  if (i,j) in ((0,2),(0,3),(2,3)):continue
  if (i,j) in replaced:
   k=replaced[i,j]
   residual=m.sub(m.add(m.mul('2',xx[2],U[k]),m.mul(m.add('(- 1)',m.mul(m.rat(2*t),gam[2])),zz[k])),differences[k])
  else:
   du,dz,dzeta,dgamma=[m.sub(q[j],q[i])for q in (U,Z,zz,gam)]
   residual=m.add(sq(du),sq(dz),m.neg(sq(x)),m.neg(m.mul(str(ell),dzeta)),m.neg(m.mul(m.rat(2*ky[i,j]),dgamma)),m.mul(m.rat(t),m.sub(sq(dzeta),sq(dgamma))))
  name=df(f'metric{i}{j}',residual);req(m.op('=',name,'0'));metric.append(name)
 assert len(metric)==21
 for k,(a,b,cface) in enumerate(faces):
  area=df(f'area{k}',m.sub(m.mul(X[a,b],Y[a,cface]),m.mul(X[a,cface],Y[a,b])))
  req(m.op('<',area,'0'))
 # Two arcs give every shortest nonedge translate. Vertical alternatives
 # are dominated by the relative-gamma bounds at y>=8.
 nonedge_count=0
 for cap in (p.CAP_A,p.CAP_B):
  for k in (0,1):
   i,j,l=cap[k],cap[k+1],cap[k+2]
   du,dz,dzeta,dgamma=[m.sub(q[l],q[i])for q in (U,Z,zz,gam)]
   dist=df(f'nonedge{i}{l}',m.add(sq(du),sq(dz),m.mul(m.rat(t),sq(dzeta))))
   req(m.op('>',dist,'0'))
   arc=m.add(X[i,j],X[j,l])
   for a in (arc,m.add(arc,'1')):req(m.op('<=',dist,m.add(sq(a),m.mul(m.rat(t),sq(dgamma)))))
   nonedge_count+=2
 assert nonedge_count==8
 coords={i:(U[i],Z[i],m.sub(str(c[i]),m.mul(m.rat(2*t),zz[i])))for i in V}
 def minor(points,axes):
  # These quantities occur only in sign and zero tests.  The intrinsic
  # face gives F3=2*area023<0 and h23=x2-x3>0.  Divide by -F3 or h23
  # exactly, retaining zero and avoiding an arbitrarily tiny anchor
  # factor.  All other minors keep their original positive scaling.
  if axes==(0,1,2) and len(points)==4 and {0,2,3}<=set(points):
   assert tuple(sorted(points))==tuple(points)
   i=next(v for v in points if v not in (0,2,3))
   return m.neg(Z[i])
  if points==(0,2,3) and axes==(0,2):return '1'
  if points in ((2,3,6),(2,3,7)) and axes==(0,1):return m.neg(Z[points[-1]])
  same=len({c[i]for i in points})==1
  C={i:(U[i],Z[i],m.neg(zz[i]) if same else coords[i][2])for i in points}
  origin,*rest=points
  return m.det([[m.sub(C[j][k],C[origin][k])for k in axes]for j in rest])
 for Q in combinations(V,4):
  if all(e in edges for e in combinations(Q,2)):
   val=df('m'+''.join(map(str,Q)),minor(Q,(0,1,2)));req(m.op('distinct',val,'0'))
 full,meta=p.linked.generate(y);suffix=full[full.index('(declare-fun b1 () Bool)'):].splitlines();assert suffix[-1]=='(check-sat)'
 nm=0
 for line in suffix[:-1]:
  match=re.fullmatch(r'\(define-fun (a([0-7]+)c([012]+)) \(\) Real .*\)',line)
  if match:
   name,pts,axes=match.groups();df(name,minor(tuple(map(int,pts)),tuple(map(int,axes))));nm+=1
  else:
   assert not re.search(r'\bG[1-7][1-7]\b',line);L.append(line)
 relative=[];cancelled=0
 for name,(i,j),(k,l) in p.determinant_pairs():
  # The plane (u,z) differs from the orthogonal transverse plane by
  # O(t) times the uniformly relative zeta slope. The audited transfer
  # gives the inclusive coefficient 53, without any cubic expressions.
  df('projected_area_'+name,m.sub(m.mul(m.sub(U[j],U[i]),m.sub(Z[l],Z[k])),m.mul(m.sub(Z[j],Z[i]),m.sub(U[l],U[k]))))
 for name,a,b in p.relative_comparisons():
  if (2,3) in (a,b):
   other=b if a==(2,3) else a;i,j=other
   # |D|=h23*|delta z_other|; h23>0 permits cancellation even
   # when this edge is arbitrarily short.  Six of the 24 atoms
   # are therefore linear, with their equality boundaries intact.
   relative.append(bound(m.sub(Z[j],Z[i]),m.mul(m.rat(53*t),m.neg(X[other])),False));cancelled+=1
  else:relative.append(bound('projected_area_'+name,m.mul(m.rat(53*t),X[a],X[b]),False))
 assert cancelled==6
 req(m.any_(relative));L.append('(check-sat)')
 meta|=dict(real_variables=n,metric_equations=21,metric_degree_bound=2,anchor_difference_equations=3,nonedge_translate_inequalities=8,incidence_minor_definitions=nm,positive_factor_minor_cancellations=8,projected_determinants=24,cancelled_area_atoms=6,inferred_phase_tests=24,relative_area_coefficient=53,chart='intrinsic face 023 with rescaled vertical corrections',zero_projected_determinants_retained=True)
 return '\n'.join(L)+'\n',meta

if __name__=='__main__':
 a=argparse.ArgumentParser();a.add_argument('output',type=Path);a.add_argument('--y',type=int,default=10**6);a.add_argument('--timeout',type=int,default=0);args=a.parse_args();text,meta=generate(args.y);args.output.write_text(text);print(json.dumps(meta));print('bytes',len(text))
 if args.timeout:print(m.solve(text,args.timeout))
