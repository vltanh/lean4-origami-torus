#!/usr/bin/env python3
"""Intrinsic-only H13 angular-cycle relaxation. Exact polynomial coefficients."""
import itertools as it, ctypes as ct, ctypes.util, sys
F=[tuple(map(int,s)) for s in '012 031 024 053 045 152 134 146 165 264 257 276 374 356 367 475'.split()]
E=sorted({tuple(sorted(e)) for f in F for e in it.combinations(f,2)})
# First sharp-ray marking, gauge K_4j=0.
sh={'01':(-1,0),'03':(-1,0),'12':(1,0),'15':(0,1),'25':(-1,1),'27':(-1,1),'35':(1,0),'36':(1,-1),'56':(0,-1),'67':(-1,1)}
K={}
for i,j in E:
    K[i,j]=sh.get(str(i)+str(j),(0,0));K[j,i]=tuple(-a for a in K[i,j])
assert all(K[4,j]==(0,0) for j in range(8) if j!=4)
for f in F:assert tuple(sum(K[i,j][k] for i,j in zip(f,f[1:]+f[:1])) for k in (0,1))==(0,0)
W=(0,7,2,3,6,1)
Q=list(it.combinations(range(8),4));S=dict(zip(Q,'-++-++--++--+-+--+-++++--++-+-+++++-++--+--+--+--++--+-+-++--+--++----'))
strict=set(Q)-{(0,1,4,7),(0,2,3,7),(0,2,5,6),(0,2,5,7),(0,4,6,7),(1,2,4,7),(1,3,5,7)}
assert len(S)==70 and len(strict)==63
for i,j in it.combinations(W,2):
    q=(4,5,i,j);s=(1 if S[tuple(sorted(q))]=='+' else -1)*(-1)**sum(a>b for k,a in enumerate(q) for b in q[k+1:]);assert s==1 and tuple(sorted(q)) in strict
A=[(i,j) for i,j in it.combinations(W,2) if tuple(sorted((i,j))) in E]
T=[q for q in it.combinations(W,3) if all(e in A for e in it.combinations(q,2))]
assert T==[(0,2,1),(0,3,1),(7,2,6),(7,3,6),(2,6,1),(3,6,1)]
# Each triangle has a distinct non-tree edge, or can be solved from tree gaps.
tree={(0,2),(2,6),(6,1),(7,2),(3,6)};used=set(tree)
for i,j,k,new in [(2,6,1,(2,1)),(0,2,1,(0,1)),(3,6,1,(3,1)),(0,3,1,(0,3)),(7,2,6,(7,6)),(7,3,6,(7,3))]:
    es={(i,j),(j,k),(i,k)};assert es-used=={new};used|=es
assert used==set(A) and len(A)==11

def op(name,*args):return '('+name+' '+' '.join(map(str,args))+')'
def add(*a):return op('+',*a)
def mul(*a):return op('*',*a)
def sub(a,b):return op('-',a,b)
def neg(a):return op('-',a)
def sq(a):return mul(a,a)
def num(a):return str(a) if a>=0 else neg(-a)
def norm(p):x,y=p;return add(sq(x),mul(x,y),sq(y))
def diff(p,q):return tuple(sub(a,b) for a,b in zip(p,q))
def det2(a,b):return sub(mul(a[0],b[1]),mul(a[1],b[0]))
lines=['(set-logic QF_NRA)'];nvar=0;nas=0
def var(v):
    global nvar;nvar+=1;lines.append(f'(declare-const {v} Real)');return v
def df(v,e):lines.append(f'(define-fun {v} () Real {e})');return v
def ass(e):
    global nas;nas+=1;lines.append(f'(assert {e})')
def c(op_,a,b='0'):ass(op(op_,a,b))
P={i:tuple(var(f'p{i}{j}') for j in 'xy') if i!=4 else ('0','0') for i in range(8)}
def shift(i,j,k=None):return tuple(add(sub(P[j][t],P[i][t]),num(a)) for t,a in enumerate(K[i,j] if k is None else k))
D={(i,j):df(f'd{i}{j}',norm(shift(i,j))) for i,j in E}
def d(i,j):return '0' if i==j else D[tuple(sorted((i,j)))]
L=d(4,5);c('>',L)
a={i:df(f'a{i}',add(L,d(4,i),neg(d(5,i)))) for i in range(8)}
C={}
for i,j in it.combinations_with_replacement(sorted(W),2):
    if i==j or (i,j) in E:C[i,j]=df(f'g{i}{j}',sub(mul('2',L,add(d(4,i),d(4,j),neg(d(i,j)))),mul(a[i],a[j])))
def g(i,j):return C[tuple(sorted((i,j)))]
for i in W:c('>',g(i,i))
for i,j in A:c('>',sub(mul(g(i,i),g(j,j)),sq(g(i,j))))
# Strict normalized comparison: a/sqrt(u)>b/sqrt(v), u,v>0.
def gt_norm(a,u,b,v):
    return op('or',op('and',op('>=',a,'0'),op('<',b,'0')),
        op('and',op('>=',a,'0'),op('>=',b,'0'),op('>',mul(sq(a),v),mul(sq(b),u))),
        op('and',op('<',a,'0'),op('<',b,'0'),op('<',mul(sq(a),v),mul(sq(b),u))))
for i,j,k in T:
    ii,jj,kk=g(i,i),g(j,j),g(k,k);ij,jk,ik=g(i,j),g(j,k),g(i,k)
    c('=',add(mul(ii,jj,kk),mul('2',ij,jk,ik),neg(mul(ii,sq(jk))),neg(mul(jj,sq(ik))),neg(mul(kk,sq(ij)))))
    c('>',sub(mul(ij,jk),mul(jj,ik)))
    ass(gt_norm(ij,ii,neg(jk),kk))
# Missing adjacent pairs (0,7) and (2,3) in the angular order.
ass(gt_norm(g(7,2),g(7,7),g(0,2),g(0,0)))
ass(gt_norm(g(3,6),g(3,3),g(2,6),g(2,2)))
for i,j in E:
    x,y=shift(i,j)
    for z in (add(mul('2',x),y),add(x,mul('2',y)),sub(x,y)):
        c('<',z,'1');c('>',z,'(- 1)')
for i,j,k in F:c('<',det2(shift(i,j),shift(i,k)))
print('variables',nvar,'assertions',nas,flush=True)
assert nvar==14 and nas==198,(nvar,nas)
smt='\n'.join(lines)+'\n'
if len(sys.argv)>1 and sys.argv[1]=='--write':
    print(smt+'(check-sat)');sys.exit()
if __name__=='__main__':
    z=ct.CDLL(ctypes.util.find_library('z3'));p=ct.c_void_p
    for f,ret,args in [('Z3_mk_config',p,[]),('Z3_set_param_value',None,[p,ct.c_char_p,ct.c_char_p]),('Z3_mk_context',p,[p]),('Z3_del_config',None,[p]),('Z3_mk_solver_for_logic',p,[p,p]),('Z3_mk_string_symbol',p,[p,ct.c_char_p]),('Z3_solver_inc_ref',None,[p,p]),('Z3_solver_from_string',None,[p,p,ct.c_char_p]),('Z3_solver_check',ct.c_int,[p,p]),('Z3_solver_get_reason_unknown',ct.c_char_p,[p,p])]:
        fn=getattr(z,f);fn.restype=ret;fn.argtypes=args
    cfg=z.Z3_mk_config();z.Z3_set_param_value(cfg,b'timeout',(sys.argv[1] if len(sys.argv)>1 else '10000').encode());ctx=z.Z3_mk_context(cfg);z.Z3_del_config(cfg)
    solver=z.Z3_mk_solver_for_logic(ctx,z.Z3_mk_string_symbol(ctx,b'QF_NRA'));z.Z3_solver_inc_ref(ctx,solver);z.Z3_solver_from_string(ctx,solver,smt.encode());out=z.Z3_solver_check(ctx,solver);print({-1:'UNSAT',0:'UNKNOWN',1:'SAT'}[out],z.Z3_solver_get_reason_unknown(ctx,solver).decode() if out==0 else '',flush=True)
