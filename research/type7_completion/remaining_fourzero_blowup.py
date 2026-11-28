#!/usr/bin/env python3
"""Exclude 48 four-zero two-line orders with a triple cluster in each cap.

Usage: python remaining_fourzero_blowup.py [OUTPUT_DIRECTORY]

Every exported height implication is reconstructed from exact stress and
corner distance identities. SAT only selects useful implications; each
of the 27 final CNFs is replayed independently by check_unsat.cpp.
The other 32 four-zero orders have a split partner and remain open here.
"""
import sys,json,time,itertools
from pathlib import Path
from functools import lru_cache
from itertools import combinations,product
from collections import Counter
import sympy as s
import solver_chambers as c
from direct_metric import load_data
from verify_linking import SAT
from remaining_one_v import DirectionalModel
from verify_nonparallel_corner import allowed_sum
A=(0,1,4,5);B=(2,3,6,7)
ax,ay,bx,by,cx,cy,dx,dy=s.symbols('ax ay bx by cx cy dx dy');vs=(ax,ay,bx,by,cx,cy,dx,dy)
ea,eb,ec,ed,ep,et=s.symbols('ea eb ec ed ep et')
V=[s.Matrix(v)for v in[(1,0),(0,1),(ax,ay),(bx,by),(cx,cy),(dx,dy)]]
def det(a,b):return s.expand(a[0]*b[1]-a[1]*b[0])

def build(kind,ha,hb):
 # Each actual zero edge retains its own positive normalization. A
 # collapsed nonedge pair uses its cluster scale and the chosen hierarchy.
 m=DirectionalModel.__new__(DirectionalModel);m.n,orig,*_=c.base_formula();m.clauses=[list(row)for row in orig[1:]];m.trits={};polys={}
 def entry(poly):
  poly=s.expand(poly)
  if not poly:return 0
  if poly in(1,-1):return int(poly)
  terms=s.Poly(poly,*vs).terms();sg=1 if terms[0][1]>0 else -1;canonical=s.expand(sg*poly);key=str(canonical)
  if key not in m.trits:
   m.trits[key]=(m.n+1,m.n+2);m.n+=2;m.clauses.append([-m.n+1,-m.n]);polys[key]=canonical
  return(key,sg)
 def deny(e,val):
  if isinstance(e,int):return [] if e!=val else None
  return m.deny(e[0],val*e[1])
 def constrain_sum(aa,bb,cc):
  es=[entry(q)for q in(aa,bb,cc)];keys=sorted({e[0]for e in es if isinstance(e,tuple)})
  for vals in product((-1,0,1),repeat=len(keys)):
   env=dict(zip(keys,vals));ev=[env[e[0]]*e[1]if isinstance(e,tuple)else e for e in es]
   if not allowed_sum(*ev):m.clauses.append(sum((m.deny(k,env[k])for k in keys),[]))
 AA=V[2]if ha<0 else V[3]if ha>0 else V[2]+V[3]
 BB=V[4]if hb<0 else V[5]if hb>0 else V[4]+V[5]
 vectors=V+[AA]+([]if kind==2 else[BB]);pairs={(i,j):entry(det(vectors[i],vectors[j]))for i,j in combinations(range(len(vectors)),2)}
 for v in V[2:]:
  es=[entry(q)for q in v];row=[]
  for e in es:
   assert isinstance(e,tuple);row+=list(m.trits[e[0]])
  m.clauses.append(row)
 m.rank_two_axioms(len(vectors),pairs)
 if ha==0:
  for v in vectors:constrain_sum(det(V[2],v),det(V[3],v),det(AA,v))
 if kind!=2 and hb==0:
  for v in vectors:constrain_sum(det(V[4],v),det(V[5],v),det(BB,v))
 p={0:s.Matrix([0,0]),1:ea*V[2],4:ea*V[2]+eb*V[3],5:s.Matrix([1,0])}
 if kind==0:p|={2:s.Matrix([0,0]),3:ec*V[4],6:ec*V[4]+ed*V[5],7:s.Matrix([0,1])};bc=((2,3,6),(7,));bedges=((2,3),(3,6))
 if kind==1:p|={2:s.Matrix([0,0]),3:ec*V[4],6:s.Matrix([0,1]),7:-ed*V[5]};bc=((2,3,7),(6,));bedges=((2,3),(2,7))
 if kind==2:p|={2:s.Matrix([0,0]),3:s.Matrix([0,1]),6:s.Matrix([0,1])+ec*V[4],7:-ed*V[5]};bc=((2,7),(3,6));bedges=((3,6),(2,7))
 if kind==3:p|={2:s.Matrix([0,1]),3:s.Matrix([0,0]),6:s.Matrix([0,1])-ec*V[4]-ed*V[5],7:s.Matrix([0,1])-ed*V[5]};bc=((2,6,7),(3,));bedges=((6,7),(2,7))
 p={i:s.Matrix([*p[i],int(i in B)])for i in range(8)};counts=Counter();allowed=set(m.trits)
 for ix,q in enumerate(c.Q,1):
  origin,*rest=q;raw=s.expand(s.Matrix.hstack(*(p[v]-p[origin]for v in rest)).det())
  degrees=[sum(max(0,len(set(q)&set(group))-1)for group in groups)for groups in(((0,1,4),(5,)),bc)]
  for vi,(var,pair)in enumerate(zip((ea,eb,ec,ed),((0,1),(1,4),*bedges))):
   if set(pair)<=set(q):raw=s.cancel(raw/var);degrees[vi//2]-=1
  assert min(degrees)>=0
  # A common cluster normalization is used only for its nonedge pair;
  # the individual present short edges were already divided separately.
  sub={ea:ep*(0 if ha>0 else 1),eb:ep*(0 if ha<0 else 1),ec:et*(0 if hb>0 else 1),ed:et*(0 if hb<0 else 1)}
  if kind==2:sub[ec]=et;sub[ed]=et
  raw=s.cancel(raw.subs(sub)/(ep**degrees[0]*et**degrees[1]));assert raw.is_polynomial(ep,et,*vs)
  leading=s.expand(raw.subs({ep:0,et:0}));en=entry(leading)
  assert not isinstance(en,tuple) or en[0] in allowed, (q,leading)
  if en==0:counts['zero']+=1;continue
  if isinstance(en,int):m.clauses.append([ix*en]);counts['constant']+=1;continue
  key,sg=en;m.bracket_link(ix,key,sg);counts['direction']+=1
 return m,counts


# Exact metric data; no floating-point arithmetic is used below.
half=s.Rational(1,2)
_,_,edges,_,_,kx,ky=load_data();t=s.symbols('t');x=[s.Integer(0)]+list(s.symbols('x1:8'));g=[s.Integer(0)]+list(s.symbols('g1:8'))
X=lambda i,j:x[j]-x[i]+kx[i,j];G=lambda i,j:g[j]-g[i];D=lambda i,j:X(i,j)**2+2*ky[i,j]*G(i,j)+t*G(i,j)**2
p=(4,1,6,3,0,5,2,7);assert p in[tuple(r['permutation'])for r in c.marked_symmetries()if r['phase_preserving']]

@lru_cache(None)
def calc(order):
 # Independent exact intrinsic corner reconstruction and relative heights.
 P=dict(zip(A,(0,0,0,half)))|dict(zip(B,[half*v for v in order]));ha=(0,0,half,half);eb=[P[j]-P[i]for i,j in zip(B,B[1:]+B[:1])];hb=list(map(abs,eb));res=[]
 for ai,(i,j)in enumerate(zip(A,A[1:]+A[:1])):
  for bi,(k,l)in enumerate(zip(B,B[1:]+B[:1])):
   R=s.expand(X(i,j)*X(k,l)+t*G(i,j)*G(k,l)-(D(i,l)+D(j,k)-D(i,k)-D(j,l))/2);res.append(R-ha[ai]*hb[bi]+(P[j]-P[i])*(P[l]-P[k]))
 for cap,hh in((A,ha),(B,hb)):res.extend(X(i,j)+h for(i,j),h in zip(zip(cap,cap[1:]+cap[:1]),hh))
 M,rhs=s.linear_eq_to_matrix(res,x[1:]+g[1:]);assert M.shape==(24,14) and M.rank()==14 and not M.free_symbols;sol=next(iter(s.linsolve((M,rhs))));sub=dict(zip(x[1:]+g[1:],sol))|{t:0}
 rho5=s.expand((D(0,5)-D(2,5)+D(0,2)).subs(sub));j0=next(v for v in B if P[v]==0);j1=next(v for v in B if P[v]==half)
 rhoB=s.expand((D(0,j1)-D(0,j0)).subs(sub)-(half-P[2])**2+P[2]**2)
 vals={}
 for sig in(-1,1):
  R=[hb[i]-sig*eb[i]for i in range(4)];c0=2*(R[2]+R[3]);g1=half-R[1];rho1=-c0+1-2*sub[x[2]]+g1
  for axis in('A','B'):vals[axis+str(sig)]=s.expand(2*(rho1-2*sig*(rho5 if axis=='A'else rhoB)))
 return rho5,rhoB,vals,sol


from remaining_flat_blowup import rank_tuple
orders=[(0,0,0,1),(0,0,1,0),(0,1,1,0),(1,0,1,1)]
phase=[tuple(row['permutation'])for row in c.marked_symmetries()if row['phase_preserving']]
zero_edges=[[(0,1),(1,4),(2,3),(3,6)],[(0,1),(1,4),(2,3),(7,2)],[(0,1),(1,4),(3,6),(7,2)],[(0,1),(1,4),(6,7),(7,2)]]
components=('ax','ay','bx','by','cx','cy','dx','dy')

def range_for_y(xx,yy):
 assert (xx or yy)and xx*yy>=0
 sig=xx or yy
 if yy==0:return sig,(s.Integer(0),s.Integer(0))
 if xx==0:return sig,(s.Integer(2*yy),s.Integer(2*yy))
 return sig,(s.Integer(0),s.Integer(2*yy))

def lemma(kind,pattern,perm,ref):
 # Swapping caps swaps the two transverse bases and reverses the level
 # axis; their two orientation reversals cancel. A common horizontal
 # reflection reverses both transverse bases, also preserving orientation.
 swap=perm[0] in B
 assert {perm[i]for i in A}==set(B if swap else A)
 assert (-1 if swap else 1)**2*ref**2==1
 P=dict(zip(A,(0,0,0,1)))|dict(zip(B,orders[kind]));newa=rank_tuple([ref*P[perm[i]]for i in A]);newb=rank_tuple([ref*P[perm[i]]for i in B]);assert newa==(0,0,0,1)
 coords=[]
 for ii,jj in((0,1),(1,4)):
  edge=(perm[ii],perm[jj]);found=[]
  for index,e in enumerate(zero_edges[kind]):
   if edge==e:found.append((index,1))
   if edge==e[::-1]:found.append((index,-1))
  assert len(found)==1;index,sg=found[0];xx,yy=[sg*ref*pattern[k]for k in components[2*index:2*index+2]]
  if perm[0]in B:xx,yy=yy,xx
  if xx*yy<0:return None
  coords.append(range_for_y(xx,yy))
 oa=tuple(newb);rb=(oa[2],oa[1],oa[0],oa[3]);rhoA,rhoB,h,_=calc(oa);rA,rB,rh,_=calc(rb)
 assert rhoA-rhoB==rA-rB
 siga,ya=coords[0];sigb,yb=coords[1]
 ca=-rh['A'+str(-sigb)];cb=-h['A'+str(siga)]
 values=[s.expand(ca*x+cb*y)for x,y in itertools.product(ya,yb)]
 if min(values)>=0 and max(values)>0:sg=1
 elif max(values)<=0 and min(values)<0:sg=-1
 else:return None
 q=tuple(perm[i]for i in A);parity=(-1)**sum(q[i]>q[j]for i,j in itertools.combinations(range(4),2));sg*=parity
 return {'quad':tuple(sorted(q)),'sign':sg,'permutation':perm,'reflection':ref,'coefficients':(int(ca),int(cb)),'ranges':[[str(v)for v in ya],[str(v)for v in yb]],'macro_b':oa}


def relative_identities():
 # These identities hold before taking any limits or dividing by an edge.
 ae,be=[tuple(zip(cap,cap[1:]+cap[:1])) for cap in (A,B)]
 stress=[[s.expand(X(i,j)*X(k,l)+t*G(i,j)*G(k,l)
                   -(D(i,l)+D(j,k)-D(i,k)-D(j,l))/2)
          for k,l in be] for i,j in ae]
 alpha=-X(0,1)
 c0=-x[2]+s.Rational(1,4)+2*g[2]
 assert s.expand(c0-2*(stress[0][2]+stress[0][3]))==0
 assert s.expand(G(0,1)-alpha/2+stress[0][1])==0
 # Add the common long-distance term here to audit the rho identities.
 full=lambda i,j:D(i,j)+ky[i,j]**2/t
 rho1=-c0+(1-2*x[2])*alpha+G(0,1)+2*t*g[2]*G(0,1)
 rho5=x[5]+s.Rational(1,4)+2*x[5]*x[2]+g[5]-2*g[2]+2*t*g[5]*g[2]
 assert s.expand(full(0,1)-full(1,2)+full(0,2)-rho1)==0
 assert s.expand(full(0,5)-full(2,5)+full(0,2)-rho5)==0
 # The small-height formula uses 1/(2|02|^2 t) -> 2.
 assert ky[0,2]**2==s.Rational(1,4)
 print('PASS exact relative stress, gamma and axis-projection identities')


def order_cover(rows):
 from collections import defaultdict
 grouped=defaultdict(list)
 for row in rows:
  if len(row['zero_a_edges'])!=2 or len(row['zero_b_edges'])!=2:continue
  values=dict(zip(A,row['a']))|dict(zip(B,row['b']))
  choices=[]
  for perm,ref in product(phase,(-1,1)):
   aa=rank_tuple([ref*values[perm[i]]for i in A])
   bb=rank_tuple([ref*values[perm[i]]for i in B])
   choices.append((aa,bb,perm,ref))
  aa,bb,perm,ref=min(choices)
  assert aa==(0,0,0,1) and bb in orders
  grouped[orders.index(bb)].append(dict(row,canonical_map={
   'permutation':perm,'horizontal_reflection':ref}))
 assert {k:len(v)for k,v in grouped.items()}=={0:16,1:16,2:32,3:16}
 return grouped


def cases_for_kind(kind):
 # A satisfiable sign pattern only suggests a useful exact implication.
 # Missing patterns could weaken the final CNF, but cannot make it unsound.
 for ha in(-1,0,1):
  for hb in(-1,0,1):
   m,_=build(kind,ha,hb)
   solver=SAT(m.n,m.clauses)
   patterns=[]
   while True:
    status=solver.check()
    if status==-1:break
    assert status==1
    values=solver.model(m.n)
    pattern={key:1 if values[m.trits[key][0]-1]>0
             else -1 if values[m.trits[key][1]-1]>0 else 0 for key in components}
    patterns.append(pattern)
    solver.add(sum((m.deny(key,value)for key,value in pattern.items()),[]))
   macro=dict(zip(A,(0,0,0,1)))|dict(zip(B,orders[kind]))
   maps=[(perm,ref)for perm,ref in product(phase,(-1,1))
         if rank_tuple([ref*macro[perm[i]]for i in A])==(0,0,0,1)]
   cuts=[];proofs=[]
   for pattern in patterns:
    for perm,ref in maps:
     proof=lemma(kind,pattern,perm,ref)
     if proof is None:continue
     cuts.append(sum((m.deny(key,value)for key,value in pattern.items()),[])
                 +[proof['sign']*abs(c.lit(proof['quad']))])
     proofs.append({'pattern':pattern,'height_certificate':proof})
   necessary=m.clauses+cuts
   assert SAT(m.n,necessary).check()==-1
   solver.z.Z3_del_context.restype=None
   solver.z.Z3_del_context.argtypes=[solver.P]
   solver.z.Z3_del_context(solver.ctx)
   yield ha,hb,m.n,necessary,proofs,len(patterns)


def main():
 import common_line_edge_collapse as two_line
 if len(sys.argv)>2:raise SystemExit(__doc__)
 output=Path(sys.argv[1]) if len(sys.argv)==2 else None
 if output:output.mkdir(parents=True,exist_ok=True)
 relative_identities()
 symmetries=c.marked_symmetries()
 variables,clauses,*_=c.base_formula()
 models=c.enumerate_models(variables,clauses,symmetries)
 _,zeros=two_line.check(models)
 grouped=order_cover(zeros)
 records=[]
 for kind in(0,1,3):
  for ha,hb,n,necessary,proofs,patterns in cases_for_kind(kind):
   name=f'fourzero_{kind}_{ha:+d}_{hb:+d}'.replace('+','p').replace('-','m')
   record={'kind':kind,'a_hierarchy':ha,'b_hierarchy':hb,'patterns':patterns,
           'variables':n,'clauses':len(necessary),'height_certificates':proofs}
   records.append(record)
   print(f'PASS {name}: UNSAT, {len(proofs)} independently reconstructed height implications',flush=True)
   if output:c.write_cnf(output/(name+'.cnf'),n,necessary)
 assert len(records)==27
 if output:
  (output/'fourzero_height_certificates.json').write_text(json.dumps(records,indent=2)+'\n')
  (output/'fourzero_cells.json').write_text(json.dumps(dict(grouped),indent=2)+'\n')
  blocked=clauses+[[-(i+1)*value for i,value in enumerate(model)]for model in models]
  c.write_cnf(output/'fourzero_model_coverage.cnf',variables,blocked)
 print('PASS 48 four-zero orders with two triple clusters; the 32 triple/split orders remain open here')
 print('Scope: unbounded-sequence blow-up exclusion; no explicit height or full marking exclusion')


if __name__=='__main__':
 if not __debug__:raise RuntimeError('run with assertions enabled')
 main()
