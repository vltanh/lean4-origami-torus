#!/usr/bin/env python3
"""Generate exact closed-sign systems for one clique branch, including degeneracy."""
from pathlib import Path
import json,sys
from itertools import combinations
P=Path(__file__).resolve().parent
sys.path.insert(0,str(P.parent))
import focused_system as fs
from satgeom import Q,ids,lit
from generate_base import sub,determinant
from fractions import Fraction
# Area sum fixed by cocycle; verify the polynomial symbolically.
import sympy as S
p={1:S.zeros(2,1)};p.update({i:S.Matrix(S.symbols(f'x{i} y{i}')) for i in range(8) if i!=1})
def dr(i,j):
 a,b=fs.K[i,j];return p[j]-p[i]+S.Matrix([S.Rational(2*a+b,2),S.Rational(b,2)])
assert S.expand(sum(S.det(S.Matrix.hstack(dr(i,j),dr(i,k))) for i,j,k in fs.F))==-1
# Face 152 is negative in the development, hence area(125)>0.
# z3>0 fixes ambient reflection. Reorient every generic chamber accordingly.
anchor=lit((1,2,5,3));branch_id=sys.argv[1] if len(sys.argv)>1 else 'B1.1'
b=next(b for b in json.loads((P/'branches.json').read_text()) if b['id']==branch_id)
full=bool(int(sys.argv[2])) if len(sys.argv)>2 else True
base,_=fs.generate((1,1,-1,-1,-1),full=full,projection=True)
base=base.replace('(check-sat)','');out=P/'systems';out.mkdir(exist_ok=True)
r={i:[f'p{i}0',f'p{i}1','0'] if i in fs.A else [f'r{i}{j}' for j in range(3)] for i in range(8)};r[1]=['0','0','0']
for ix,pat in enumerate(b['chambers']):
 sign=[1 if c=='+' else -1 for c in pat];sg=sign[abs(anchor)-1]*(1 if anchor>0 else -1);sign=[z*sg for z in sign]
 body=[]
 for q,z in zip(Q,sign):
  a,*rest=q;det=determinant([[sub(r[i][k],r[a][k]) for k in range(3)] for i in rest]);name='ch'+''.join(map(str,q));body.append(f'(define-fun {name} () Real {det})')
  # For noncliques weak signs are necessary for limits of generic chambers;
  # strict clique signs follow from the K4 nondegeneracy lemma.
  op=('>' if z==1 else '<') if q in fs.cl else ('>=' if z==1 else '<=')
  body.append(f'(assert ({op} {name} 0))')
 (out/f'{branch_id}_{ix+1:02}_{int(full)}.smt2').write_text(base+'\n'+'\n'.join(body)+'\n(check-sat)\n')
print(branch_id,len(b['chambers']),'systems, full embedding:',full)
