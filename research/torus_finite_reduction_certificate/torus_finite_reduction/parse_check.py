"""Optional syntax check using system libz3 (no Python z3 package required)."""
import ctypes as c
from ctypes.util import find_library
from pathlib import Path
z=c.CDLL(find_library('z3'));P=c.c_void_p;I=c.c_uint;S=c.c_char_p
for name,restype,args in [('Z3_mk_config',P,[]),('Z3_mk_context',P,[P]),('Z3_del_config',None,[P]),('Z3_del_context',None,[P]),('Z3_parse_smtlib2_string',P,[P,S,I,P,P,I,P,P]),('Z3_ast_vector_size',I,[P,P])]:
 f=getattr(z,name);f.restype=restype;f.argtypes=args
for file in sorted(Path(__file__).with_name('systems').glob('*.smt2')):
 config=z.Z3_mk_config();ctx=z.Z3_mk_context(config);z.Z3_del_config(config)
 script=file.read_text().replace('(check-sat)','');v=z.Z3_parse_smtlib2_string(ctx,script.encode(),0,None,None,0,None,None);assert v
 print(file.name,'parsed',z.Z3_ast_vector_size(ctx,v),'assertions',flush=True);z.Z3_del_context(ctx)
