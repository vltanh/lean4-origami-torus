#!/usr/bin/env python3
"""Certify the dyadic-grid Type 5 family using the one-scale interval engine."""
from fractions import Fraction as Q
from verify_one_scale import J, EXCEPT, audit_source, points, separate, cover
import sys

def core(a,x,y,s):
    e=s*s;X=Q(1,2)-3*a
    p={1:[J(0),J(0)],
       2:[X,((e-Q(1,2))*(x*x+y*y)-x*X)/y],
       3:[Q(1,2)-e,5*a*y],
       4:[-4*a,(Q(1,2)-5*a)*y],
       5:[-2*a,-12*a*y]}
    return x,y,s,p

def free_scale(a,y,s):return core(a,J(0),y,s)
def fixed_scale(x,y,s):return core(J(Q(1,64)),x,y,s)

def main():
    audit_source();zero=Q(0);one=Q(1);scale=Q(1,64)
    areas,v=points(((scale,scale),(one,one),(zero,zero)),free_scale)
    assert all(z.sign()==1 for z in areas)
    ref={q:(z.d[2].sign() if q in EXCEPT else z.sign()) for q,z in v.items()}
    separate(ref)
    print('PASS boundary reference, 68 ordinary brackets and two exceptional derivatives',[(q,ref[q],v[q].d[2]) for q in sorted(EXCEPT)],flush=True)
    boxes={
        'square':(((scale,scale),(one,one),(zero,Q(1,512))),free_scale,64),
        'scale':(((Q(127,8192),Q(129,8192)),(one,one),(zero,zero)),free_scale,39),
        'rect':(((scale,scale),(one,Q(41,40)),(zero,zero)),free_scale,285),
        'oblique':(((zero,Q(1,4096)),(one,Q(4097,4096)),(zero,zero)),fixed_scale,8),
    }
    for label in sys.argv[1:] or boxes:
        box,chart,count=boxes[label];n=cover(box,ref,core=chart)
        if count is not None:assert n==count
if __name__=='__main__':main()
