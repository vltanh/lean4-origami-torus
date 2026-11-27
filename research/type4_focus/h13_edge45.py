#!/usr/bin/env python3
"""H13: universal-edge Gram relaxation with exact coefficients.
Run with Python stdlib + libz3. UNSAT excludes H13 subject to the prior
marking/sign reductions; SAT of this relaxation is not an embedding.
"""
import itertools as it, ctypes as ct, ctypes.util, sys
F=[tuple(map(int,s)) for s in '012 031 024 053 045 152 134 146 165 264 257 276 374 356 367 475'.split()]
E=sorted({tuple(sorted(e)) for f in F for e in it.combinations(f,2)})
# t4_ray_1, gauge K_4j=0. Normalized hexagonal metric x^2+xy+y^2.
sh={'01':(-1,0),'03':(-1,0),'12':(1,0),'15':(0,1),'25':(-1,1),'27':(-1,1),'35':(1,0),'36':(1,-1),'56':(0,-1),'67':(-1,1)}
K={}
for i,j in E:
    K[i,j]=sh.get(str(i)+str(j),(0,0));K[j,i]=tuple(-a for a in K[i,j])
assert all(K[4,j]==(0,0) for j in range(8) if j!=4)
for f in F:assert tuple(sum(K[i,j][k] for i,j in zip(f,f[1:]+f[:1])) for k in (0,1))==(0,0)
Q=list(it.combinations(range(8),4));signs='-++-++--++--+-+--+-++++--++-+-+++++-++--+--+--+--++--+-+-++--+--++----'
assert len(signs)==70
S=dict(zip(Q,signs));cliques={q for q in Q if all(e in E for e in it.combinations(q,2))}
def parity(q):return sum(a>b for i,a in enumerate(q) for b in q[i+1:])%2
def sg(q):return (1 if S[tuple(sorted(q))]=='+' else -1)*(-1)**parity(q)
order=(0,7,2,3,6,1)
assert all(sg((4,5,i,j))==1 for i,j in it.combinations(order,2))
def add(*x):
    x=[str(a) for a in x if str(a)!='0'];return '0' if not x else x[0] if len(x)==1 else '(+ '+' '.join(x)+')'
def neg(a):return f'(- {a})' if str(a)!='0' else '0'
def sub(a,b):return add(a,neg(b))
def mul(*x):
    x=[str(a) for a in x];return '0' if '0' in x else x[0] if len(x)==1 else '(* '+' '.join(x)+')'
def num(a):return str(a) if a>=0 else f'(- {-a})'
def sq(a):return mul(a,a)
def norm(p):x,y=p;return add(sq(x),mul(x,y),sq(y))
def diff(p,q):return tuple(sub(a,b) for a,b in zip(p,q))
def det2(a,b):return sub(mul(a[0],b[1]),mul(a[1],b[0]))
def det3(a,b,c):return add(mul(a[0],det2(b[1:],c[1:])),neg(mul(a[1],det2((b[0],b[2]),(c[0],c[2])))),mul(a[2],det2(b[:2],c[:2])))
lines=['(set-logic QF_NRA)'];nvar=0;nassert=0
def var(v):
    global nvar;nvar+=1;lines.append(f'(declare-const {v} Real)');return v
def define(v,e):lines.append(f'(define-fun {v} () Real {e})');return v
def A(op,x,y='0'):
    global nassert;nassert+=1;lines.append(f'(assert ({op} {x} {y}))')
P={i:tuple(var(f'p{i}{j}') for j in 'xy') if i!=4 else ('0','0') for i in range(8)}
def shift(i,j,k=None):return tuple(add(sub(P[j][t],P[i][t]),num(a)) for t,a in enumerate(K[i,j] if k is None else k))
D={(i,j):define(f'd{i}{j}',norm(shift(i,j))) for i,j in E}
def d(i,j):return '0' if i==j else D[tuple(sorted((i,j)))]
L=d(4,5);A('>',L)
# Coordinates are scaled by 2*sqrt(L). The axial coordinate is a_i.
a={i:define(f'a{i}',add(L,d(4,i),neg(d(5,i)))) for i in range(8)}
W=order;C={}
for i,j in it.combinations_with_replacement(sorted(W),2):
    if i==j or (i,j) in E:
        C[i,j]=define(f'g{i}{j}',sub(mul('2',L,add(d(4,i),d(4,j),neg(d(i,j)))),mul(a[i],a[j])))
def g(i,j):return C[tuple(sorted((i,j)))]
G=(g(0,0),g(0,1),g(1,1));A('>',G[0]);A('>',sub(mul(G[0],G[2]),sq(G[1])))
b={0:('1','0'),1:('0','1'),4:('0','0'),5:('0','0')}
for i in (2,3,6,7):b[i]=(var(f'u{i}'),var(f'v{i}'))
def inner(x,y):return add(mul(G[0],x[0],y[0]),mul(G[1],add(mul(x[0],y[1]),mul(x[1],y[0]))),mul(G[2],x[1],y[1]))
for (i,j),v in C.items():
    if i in (0,1) and j in (0,1):continue
    A('=',inner(b[i],b[j]),v)
# Weak ordered wedge: strict exactly when the corresponding quadruple is a clique.
for i,j in it.combinations(order,2):A('>' if tuple(sorted((4,5,i,j))) in cliques else '>=',det2(b[i],b[j]))
# Intrinsic constraints: strict nearest lifts and consistently negative oriented faces.
for i,j in E:
    x,y=shift(i,j)
    for z in (add(mul('2',x),y),add(x,mul('2',y)),sub(x,y)):
        A('<',z,'1');A('>',z,'(- 1)')
for i,j,k in F:A('<',det2(shift(i,j),shift(i,k)))
# Full H13 signs, with weak signs on noncliques.
r={i:(*b[i],a[i]) for i in range(8)}
for q in Q:
    i,j,k,l=q
    v=det3(diff(r[j],r[i]),diff(r[k],r[i]),diff(r[l],r[i]))
    A('>' if q in cliques else '>=',v if S[q]=='+' else neg(v))
# Necessary nonedge upper bounds (finite sample of lattice translates).
for i,j in it.combinations(range(8),2):
    if (i,j) in E:continue
    u=diff(b[j],b[i]);dd=add(inner(u,u),sq(sub(a[j],a[i])))
    for k in it.product(range(-2,3),repeat=2):A('<=',dd,mul('4',L,norm(shift(i,j,k))))
print('variables',nvar,'assertions',nassert,flush=True)
assert nvar==22
smt='\n'.join(lines)+'\n'
if len(sys.argv)>1 and sys.argv[1]=='--write':
    print(smt+'(check-sat)');sys.exit()
z=ct.CDLL(ctypes.util.find_library('z3'));p=ct.c_void_p
for f,ret,args in [('Z3_mk_config',p,[]),('Z3_set_param_value',None,[p,ct.c_char_p,ct.c_char_p]),('Z3_mk_context',p,[p]),('Z3_del_config',None,[p]),('Z3_mk_solver_for_logic',p,[p,p]),('Z3_mk_string_symbol',p,[p,ct.c_char_p]),('Z3_solver_inc_ref',None,[p,p]),('Z3_solver_from_string',None,[p,p,ct.c_char_p]),('Z3_solver_check',ct.c_int,[p,p]),('Z3_solver_get_reason_unknown',ct.c_char_p,[p,p])]:
    fn=getattr(z,f);fn.restype=ret;fn.argtypes=args
cfg=z.Z3_mk_config();z.Z3_set_param_value(cfg,b'timeout',(sys.argv[1] if len(sys.argv)>1 else '10000').encode());ctx=z.Z3_mk_context(cfg);z.Z3_del_config(cfg)
solver=z.Z3_mk_solver_for_logic(ctx,z.Z3_mk_string_symbol(ctx,b'QF_NRA'));z.Z3_solver_inc_ref(ctx,solver);z.Z3_solver_from_string(ctx,solver,smt.encode());out=z.Z3_solver_check(ctx,solver);print({-1:'UNSAT',0:'UNKNOWN',1:'SAT'}[out],z.Z3_solver_get_reason_unknown(ctx,solver).decode() if out==0 else '',flush=True)
