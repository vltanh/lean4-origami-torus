#!/usr/bin/env python3
"""Necessary five-point metric kernel for B1.1 (vertices 1,2,3,5,7).
No extrinsic variables. Gauge at 5. Fixed strict Radon partition {1,3,7}|{2,5}.
"""
from pathlib import Path
import sys,itertools as it,json
P=Path(__file__).resolve().parent;sys.path.insert(0,str(P.parent.parent))
import focused_system as fs
from satgeom import Q,lit
from generate_base import op,add,mul,sub,neg,rat,num,all_
V=[1,2,3,5,7];A=[1,3,7];B=[2,5];E=list(it.combinations(V,2));assert all(e in fs.E for e in E)
# Check every chamber forces this circuit (all five minors are cliques).
for pat in json.loads((P.parent/'branches.json').read_text())[0]['chambers']:
 s=[(1 if pat[Q.index(tuple(V[:i]+V[i+1:]))]=='+' else -1)*(-1)**i for i in range(5)];assert all(tuple(V[:i]+V[i+1:]) in fs.cl for i in range(5));assert {i for i,z in zip(V,s) if z==s[0]}==set(A)
g={i:fs.K[5,i] if i!=5 else (0,0) for i in V};K={e:tuple(fs.K[e][i]+g[e[0]][i]-g[e[1]][i] for i in range(2)) for e in E};K.update({(j,i):tuple(-x for x in k) for (i,j),k in list(K.items())});assert {e:k for e,k in K.items() if e[0]<e[1] and k!=(0,0)}=={(1,3):(1,-1),(2,3):(1,0),(2,7):(1,0)}
lines=['(set-logic QF_NRA)']
def decl(n):lines.append(f'(declare-fun {n} () Real)');return n
def define(n,e):lines.append(f'(define-fun {n} () Real {e})');return n
def ass(e):lines.append(op('assert',e))
def dot(a,b):return add(mul(a[0],b[0]),mul('3',a[1],b[1]))
def vs(a,b):return [sub(x,y) for x,y in zip(a,b)]
def va(a,b):return [add(x,y) for x,y in zip(a,b)]
def sc(a,b):return [mul(a,x) for x in b]
def shift(a,b):return [rat(2*a+b,2),rat(b,2)]
def cross(a,b):return sub(mul(a[0],b[1]),mul(a[1],b[0]))
p={5:['0','0']};p.update({i:[decl(f'p{i}{k}') for k in range(2)] for i in V if i!=5})
a,b,c,t=map(decl,['a','b','c','t']);v=[decl('vx'),decl('vy')]
for x in (a,b,c,t):ass(op('>',x,'0'))
ass(op('=',add(a,b,c),'1'));ass(op('<',t,'1'))
lam={1:a,2:neg(t),3:b,7:c,5:sub(t,'1')}
for k in range(2):ass(op('=',v[k],add(*(mul(lam[i],p[i][k]) for i in V))))
s={}
for i,j in E:
 k=shift(*K[i,j]);d=vs(p[j],p[i]);u=va(d,k)
 for x,y in [(1,0),(0,1),(-1,1)]:
  q=mul('2',dot(u,shift(x,y)));ass(op('<',q,'1'));ass(op('>',q,'(- 1)'))
 s[i,j]=s[j,i]=define(f's{i}{j}',neg(add(mul('2',dot(k,d)),dot(k,k))))
for i in V:
 if i!=5:ass(op('=',add(mul('2',dot(p[i],v)),*(mul(lam[j],s[i,j]) for j in V if i!=j)),'0'))
# all inherited intrinsic faces are consistently negatively oriented
for i,j,k in fs.F:
 if {i,j,k}<=set(V):ass(op('<',cross(va(vs(p[j],p[i]),shift(*K[i,j])),va(vs(p[k],p[i]),shift(*K[i,k]))),'0'))
# Optional SPD principal minors for the nondegenerate K4s.
if '--psd' in sys.argv:
 from generate_base import determinant
 G={(i,j):add(dot(p[i],p[j]),mul('(/ 1 2)',s[i,j])) if i!=j else dot(p[i],p[i]) for i in V if i!=5 for j in V if j!=5}
 for I in it.combinations([1,2,3,7],3):ass(op('>',determinant([[G[i,j] for j in I] for i in I]),'0'))
lines.append('(check-sat)');out=P/('k5_kernel_psd.smt2' if '--psd' in sys.argv else 'k5_kernel.smt2');out.write_text('\n'.join(lines)+'\n');print('PASS: common strict Radon circuit, exact 14-variable kernel relaxation',out)
