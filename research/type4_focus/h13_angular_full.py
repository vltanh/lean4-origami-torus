#!/usr/bin/env python3
"""Complete strict/weak H13 metric and embedding test using five radicals.
The angular-cycle base certifies the metric and angular order. Here the
five tree rotations reconstruct every determinant without division.
"""
import itertools as it,sys,ctypes as ct,ctypes.util
import h13_angular_cycles as h
F={tuple(sorted(f)) for f in h.F};E=set(h.E);Q=h.Q;S=h.S;strict=h.strict
Z=set(Q)-strict;V=set(range(8));simp=F|E|{(i,) for i in V}
# No affine circuit of size <=3: each triple has a strictly nonzero
# extension. This also rules out coincident vertices.
assert all(any(tuple(sorted(t+(w,))) in strict for w in V-set(t)) for t in it.combinations(range(8),3))
def partition(C,omit=None):
    a=tuple(v for k,v in enumerate(C) if v!=omit and (-1)**k*(1 if S[C[:k]+C[k+1:]]=='+' else -1)>0)
    b=tuple(v for v in C if v!=omit and v not in a)
    return a,b
# In a 5-point minimal circuit the four-point minors are all nonzero.
for C in it.combinations(range(8),5):
    a,b=partition(C);assert a and b and not(a in simp and b in simp)
# In a 4-point minimal circuit, append ANY point off its plane. The
# four nonzero cofactor signs then select precisely its sign partition.
for q in sorted(Z):
    for w in V-set(q):
        a,b=partition(tuple(sorted(q+(w,))),w);assert a and b and not(a in simp and b in simp)
print('PASS all 56 five-point and 28 four-point circuit sign tests',flush=True)
# All 63 strict and seven weak H13 signs are therefore sufficient for
# embeddedness, in addition to being necessary for the H13 closure.
add,mul,sub,neg,sq,df,var,c=h.add,h.mul,h.sub,h.neg,h.sq,h.df,h.var,h.c
g,L,a=h.g,h.L,h.a
# Multiply both physical transverse coordinates by sqrt(C00)>0. Use
# complex tree rotations (Cij+i signed sqrt(Delta_ij))/Cii. Store
# each point as two polynomial numerators with a positive denominator.
N={0:(g(0,0),'0','1'),4:('0','0','1'),5:('0','0','1')}
for i,j in [(0,2),(2,6),(6,1),(2,7),(6,3)]:
    t=var(f't{i}{j}');c('>',t);c('=',sq(t),sub(mul(g(i,i),g(j,j)),sq(g(i,j))))
    if h.W.index(j)<h.W.index(i):t=neg(t)
    x,y,d=N[i];z=g(i,j)
    N[j]=(df(f'nx{j}',sub(mul(x,z),mul(y,t))),df(f'ny{j}',add(mul(x,t),mul(y,z))),df(f'den{j}',mul(d,g(i,i))))
assert len(N)==8
# Difference vector multiplied by the product of two positive denominators.
def dif(i,j):
    x,y,d=N[i];X,Y,D=N[j]
    return (sub(mul(d,X),mul(D,x)),sub(mul(d,Y),mul(D,y)),mul(d,D,sub(a[j],a[i])))
def det(u,v,w):
    return add(mul(u[0],sub(mul(v[1],w[2]),mul(v[2],w[1]))),neg(mul(u[1],sub(mul(v[0],w[2]),mul(v[2],w[0])))),mul(u[2],sub(mul(v[0],w[1]),mul(v[1],w[0]))))
for q in Q:
    i,j,k,l=q
    x=df('vol'+''.join(map(str,q)),det(dif(i,j),dif(i,k),dif(i,l)))
    if S[q]=='-':x=neg(x)
    c('>' if q in strict else '>=',x)
# Optional redundant chord inequalities: the exact shortest-lift bound
# from section 11 reduces to these seven translates. The extra sqrt(C00)
# scaling of transverse axes is undone by multiplying by C00.
shifts=[(0,0),(1,0),(-1,0),(0,1),(0,-1),(1,-1),(-1,1)]
for i,j in it.combinations(range(8),2):
    if (i,j) in E:continue
    x,y,z=dif(i,j);lft=add(sq(x),sq(y),mul(g(0,0),sq(z)))
    fac=mul('4',L,g(0,0),sq(N[i][2]),sq(N[j][2]))
    c('>',lft)
    for k in shifts:c('<',lft,mul(fac,h.norm(h.shift(i,j,k))))
print('full variables',h.nvar,'assertions',h.nas,flush=True)
assert h.nvar==19 and h.nas==310
smt='\n'.join(h.lines)+'\n'
if len(sys.argv)>1 and sys.argv[1]=='--write':
    print(smt+'(check-sat)');sys.exit()
if __name__=='__main__':
    z=ct.CDLL(ctypes.util.find_library('z3'));p=ct.c_void_p
    for f,ret,args in [('Z3_mk_config',p,[]),('Z3_set_param_value',None,[p,ct.c_char_p,ct.c_char_p]),('Z3_mk_context',p,[p]),('Z3_del_config',None,[p]),('Z3_mk_solver_for_logic',p,[p,p]),('Z3_mk_string_symbol',p,[p,ct.c_char_p]),('Z3_solver_inc_ref',None,[p,p]),('Z3_solver_from_string',None,[p,p,ct.c_char_p]),('Z3_solver_check',ct.c_int,[p,p]),('Z3_solver_get_reason_unknown',ct.c_char_p,[p,p])]:
        fn=getattr(z,f);fn.restype=ret;fn.argtypes=args
    cfg=z.Z3_mk_config();z.Z3_set_param_value(cfg,b'timeout',(sys.argv[1] if len(sys.argv)>1 else '10000').encode());ctx=z.Z3_mk_context(cfg);z.Z3_del_config(cfg)
    solver=z.Z3_mk_solver_for_logic(ctx,z.Z3_mk_string_symbol(ctx,b'QF_NRA'));z.Z3_solver_inc_ref(ctx,solver);z.Z3_solver_from_string(ctx,solver,smt.encode());out=z.Z3_solver_check(ctx,solver);print({-1:'UNSAT',0:'UNKNOWN',1:'SAT'}[out],z.Z3_solver_get_reason_unknown(ctx,solver).decode() if out==0 else '',flush=True)
