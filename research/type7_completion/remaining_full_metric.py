#!/usr/bin/env python3
"""Generate full necessary metric/embedding systems for all ray-1/2 masks.

Includes actual degeneracy-complete affine circuits, weak generic signs,
all shortest horizontal triangle unlinkings, and mandatory alternating-ring
linking of magnitude one or two. No marking or mask is declared excluded.
"""
from pathlib import Path
import importlib.util,json,argparse
ROOT=Path(__file__).resolve().parents[1]
spec=importlib.util.spec_from_file_location('type7_remaining_linked',ROOT/'type7_closure/linked_metric.py')
linked=importlib.util.module_from_spec(spec);spec.loader.exec_module(linked)

def generate(mark,mask,y=10**6):
 text,meta=linked.generate(y,mark,mask)
 # Horizontal periods (-1,0) on every consecutive triangle force all
 # three oriented horizontal displacements to be negative: each is
 # strictly greater than -1/2 and their sum is -1.
 extra=[]
 for i in range(8):
  j=(i+1)%8;X=f'X{min(i,j)}{max(i,j)}'
  extra.append(f'(assert ({"<" if i<j else ">"} {X} 0))')
 text=text.removesuffix('(check-sat)\n')+'\n'.join(extra)+'\n(check-sat)\n'
 meta=dict(meta,marking=mark,mask=mask,horizontal_unlinkings=12,long_link_magnitudes=[1,2])
 return text,meta

if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('output',type=Path);p.add_argument('--mark',type=int,choices=(1,2));p.add_argument('--mask',choices=linked.m.MASKS);p.add_argument('--y',type=int,default=10**6);p.add_argument('--timeout',type=int,default=0);a=p.parse_args();a.output.mkdir(parents=True,exist_ok=True)
 for mark in (a.mark,) if a.mark else (1,2):
  for mask in (a.mask,) if a.mask else linked.m.MASKS:
   text,meta=generate(mark,mask,a.y);name=f'ray{mark}_{mask}';(a.output/(name+'.smt2')).write_text(text);print(json.dumps(dict(meta,bytes=len(text))),flush=True)
   if a.timeout:print(linked.m.solve(text,a.timeout),flush=True)
