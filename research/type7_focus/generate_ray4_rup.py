#!/usr/bin/env python3
"""Regenerate the blocked ray_4 CNF and a SAT proof for independent replay.
Requires Python 3 and shared libz3. Run in any output directory:
  python /path/to/research/type7_focus/generate_ray4_rup.py
  /path/to/check_ray4_rup ray4_blocked.cnf ray4_ordered.drat
The solver is only a proof producer; check_ray4_rup.cpp checks the trace.
"""
import ctypes as c
from ctypes.util import find_library
from pathlib import Path
import sys,json
sys.path.insert(0,str(Path(__file__).resolve().parent.parent/'linking_checkpoint'))
from verify_linking import formula,CNF,short_pairs,data,cases
P=Path(__file__).resolve().parent.parent/'linking_checkpoint'
case=next(c for c in cases if c['file']=='t7_ray_4.smt2')
K,_,_=data(case);n,C,T,E,N=formula(7);a=CNF(n)
assert short_pairs(K)==[((0,2,4,6),(1,3,5,7))]
for A,B in short_pairs(K):a.unlink(A,B)
models=sorted(json.loads((P/'ring4_full_signs.json').read_text()))
assert len(set(models))==16 and all(len(m)==70 and m[0]=='+' and set(m)<=set('+-') for m in models)
D=C+a.C+[[-(i+1)*(1 if x=='+' else -1) for i,x in enumerate(m)] for m in models]
assert a.n==215 and len(D)==7786
Path('ray4_blocked.cnf').write_text(f'p cnf {a.n} {len(D)}\n'+''.join(' '.join(map(str,row))+' 0\n' for row in D))
z=c.CDLL(find_library('z3'));P=c.c_void_p;S=c.c_char_p
for name,res,args in [('Z3_mk_config',P,[]),('Z3_mk_context',P,[P]),('Z3_del_config',None,[P]),('Z3_eval_smtlib2_string',S,[P,S])]:
 f=getattr(z,name);f.restype=res;f.argtypes=args
cfg=z.Z3_mk_config();ctx=z.Z3_mk_context(cfg);z.Z3_del_config(cfg)
lines=['(set-option :sat.drat.file "ray4_ordered.drat")','(set-option :sat.drat.binary false)']+[f'(declare-const x{i} Bool)' for i in range(1,a.n+1)]
# These redundant clauses make the producer encounter variables in a
# predictable order: internal guard=1, internal x_i=i+1. The checker
# independently starts from the permuted original CNF plus these clauses
# and guard=true, and checks all logged input clauses as well as the proof.
lines.append('(declare-const guard Bool)')
for i in range(1,a.n+1):lines.append(f'(assert (or guard x{i}))')
for row in D:lines.append('(assert (or '+' '.join(f'x{i}' if i>0 else f'(not x{-i})' for i in row)+'))')
lines.append('(assert guard)')
lines.append('(check-sat-using sat)')
print(z.Z3_eval_smtlib2_string(ctx,'\n'.join(lines).encode()).decode())
