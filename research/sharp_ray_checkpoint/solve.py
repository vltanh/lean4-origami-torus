#!/usr/bin/env python3
"""Run an SMT-LIB query using libz3 (no Python package required)."""
import ctypes as c,sys
from ctypes.util import find_library
from pathlib import Path
z=c.CDLL(find_library('z3'));P=c.c_void_p;I=c.c_uint;S=c.c_char_p
for name,restype,args in [('Z3_mk_config',P,[]),('Z3_mk_context',P,[P]),('Z3_del_config',None,[P]),('Z3_del_context',None,[P]),('Z3_eval_smtlib2_string',S,[P,S])]:
 f=getattr(z,name);f.restype=restype;f.argtypes=args
for file in map(Path,sys.argv[2:]):
 cfg=z.Z3_mk_config();ctx=z.Z3_mk_context(cfg);z.Z3_del_config(cfg);s=f'(set-option :timeout {int(sys.argv[1])})\n'+file.read_text()+'\n(get-info :reason-unknown)\n';print(file.name,z.Z3_eval_smtlib2_string(ctx,s.encode()).decode(),flush=True);z.Z3_del_context(ctx)
