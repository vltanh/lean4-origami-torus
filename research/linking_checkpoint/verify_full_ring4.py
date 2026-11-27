#!/usr/bin/env python3
"""Verify completeness of the 16 full generic sign models for ray_4 in the elongated region."""
from verify_linking import *
import subprocess
c=next(c for c in cases if c['file']=='t7_ray_4.smt2');K,_,_=data(c);n,C,T,E,N=formula(7);a=CNF(n)
for A,B in short_pairs(K):a.unlink(A,B)
s=SAT(a.n,C+a.C);models=json.loads((P/'ring4_full_signs.json').read_text());assert len(set(models))==16
blocks=[]
for m in models:
    assert len(m)==70 and m[0]=='+'
    L=[(i+1)*(1 if v=='+' else -1) for i,v in enumerate(m)]
    s.push()
    for v in L:s.add([v])
    assert s.check()==1;s.pop();blocks.append([-v for v in L])
for b in blocks:s.add(b)
assert s.check()==-1
D=C+a.C+blocks
if len(sys.argv)>1:
    cnf=f'p cnf {a.n} {len(D)}\n'+''.join(' '.join(map(str,b))+' 0\n' for b in D)
    r=subprocess.run([sys.argv[1]],input=cnf,text=True,capture_output=True,check=True).stdout.strip();assert r.startswith('UNSAT');print(r)
print('PASS 16 sign models, blocked formula UNSAT:',a.n,'variables',len(D),'clauses')
