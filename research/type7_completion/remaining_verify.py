#!/usr/bin/env python3
"""Check all fourteen full ray-1/2 queries without attempting NRA search."""
import ctypes as ct,ctypes.util,hashlib,json
from itertools import combinations
from pathlib import Path
import remaining_full_metric as f
import remaining_local_metric as local
from remaining_local_witness import verify as verify_witness, witness


def parse_count(text):
 z=ct.CDLL(ctypes.util.find_library('z3'));P=ct.c_void_p
 for name,ret,args in [('Z3_mk_config',P,[]),('Z3_mk_context',P,[P]),('Z3_del_config',None,[P]),('Z3_del_context',None,[P]),('Z3_parse_smtlib2_string',P,[P,ct.c_char_p,ct.c_uint,P,P,ct.c_uint,P,P]),('Z3_ast_vector_size',ct.c_uint,[P,P]),('Z3_get_error_code',ct.c_uint,[P])]:
  fn=getattr(z,name);fn.restype=ret;fn.argtypes=args
 cfg=z.Z3_mk_config();ctx=z.Z3_mk_context(cfg);z.Z3_del_config(cfg)
 try:
  a=z.Z3_parse_smtlib2_string(ctx,text.removesuffix('(check-sat)\n').encode(),0,None,None,0,None,None)
  assert z.Z3_get_error_code(ctx)==0
  n=z.Z3_ast_vector_size(ctx,a);assert n==text.count('(assert ');return n
 finally:z.Z3_del_context(ctx)


def main():
 old,_=f.linked.generate(10**6)
 # Frozen hash from the generator immediately before generalization.
 assert hashlib.sha256(old.encode()).hexdigest()=='b480e6ba966ed0b1127bbcb40356629c06c474be7684a72c1286766818517e12'
 cases=json.loads((f.ROOT/'linking_checkpoint/cases.json').read_text())
 for mark in (1,2):
  case=next(c for c in cases if c['file']==f't7_ray_{mark}.smt2');K,_,_=f.linked.data(case)
  def period(R):return tuple(sum(K[a,b][j] for a,b in zip(R,R[1:]+R[:1])) for j in (0,1))
  assert period((0,2,4,6))==period((1,3,5,7))==((0,1) if mark==1 else (1,1))
  # These disjoint triangles supply |k|<=1; reversing an entire cycle
  # only changes its period and orientation together.
  h=period((0,2,5));g=period((1,3,6))
  assert h==((-1,1) if mark==1 else (0,1))
  assert g==h or g==tuple(-v for v in h)
  assert len(f.linked.short_pairs(K))==12
  values={k+B for k in (-1,0,1) for B in (-1,1) if k+B!=0}
  assert values=={-2,-1,1,2}
  for mask in f.linked.m.MASKS:
   text,meta=f.generate(mark,mask)
   assert (meta['real_variables'],meta['boolean_variables'],meta['cnf_clauses'],meta['circuit_partitions'])==(18,382,8305,524)
   assert text.count('(declare-fun ')==400 and text.count('(check-sat)')==1
   # Seventy weak minor-sign couplings remain, and every nonclique zero
   # is still allowed at this coupling layer.
   assert sum(line.startswith('(assert (ite b') for line in text.splitlines())==70
   count=parse_count(text)
  print(f'PASS ray{mark}: seven complete queries; {count} assertions each')
  print(json.dumps(verify_witness(mark)))
  # Cross-check the emitted shortcut formula on the independently
  # certified metric. With every variable fixed this is evaluation,
  # not an unconstrained nonlinear feasibility search.
  hs,bs=witness(mark)
  fixed='\n'.join(f'(assert (= {name}{i} {local.rat(values[i])}))'
                  for name,values in [('h',hs),('b',bs)] for i in range(7))
  query=local.generate(mark,'04').removesuffix('(check-sat)\n')+fixed+'\n(check-sat)\n'
  assert local.solve(query,2000).startswith('sat ')
 print('PASS legacy ray3 byte identity and exact linking alternatives')
 print('No full mask exclusion is claimed.')

if __name__=='__main__':main()
