"""Exact rational interval certificate for prescribed neighborhoods of lattice shapes.
Run from this directory with python3 (not -O). No external packages for verification.
"""
import json
from pathlib import Path
from itertools import combinations
from certify_positive import I,Q,FACES,SEEDS,evaluate,verify_embedding
from periods import modulus,combinatorics

class D:
    """Forward automatic differentiation on outward-rounded intervals."""
    n=9
    def __init__(self,x,g=None):
        if isinstance(x,D):self.x,self.g=x.x,x.g;return
        self.x=I(x);self.g=[I(0)]*self.n if g is None else g
    def __add__(a,b):
        b=D(b);return D(a.x+b.x,[x+y for x,y in zip(a.g,b.g)])
    __radd__=__add__
    def __neg__(a):return D(-a.x,[-x for x in a.g])
    def __sub__(a,b):return a+-D(b)
    def __rsub__(a,b):return D(b)+-a
    def __mul__(a,b):
        b=D(b);return D(a.x*b.x,[x*b.x+a.x*y for x,y in zip(a.g,b.g)])
    __rmul__=__mul__
    def __truediv__(a,b):
        b=D(b);c=a.x/b.x;return D(c,[(x-c*y)/b.x for x,y in zip(a.g,b.g)])
    def sqrt(a):
        c=a.x.sqrt();return D(c,[x/(2*c) for x in a.g])

def fun(p,f,U,cols):
    ff,J,upper,cc=evaluate(p,f)
    dd=[D(v,[I(int(i==c)) for c in cols]) for i,v in enumerate(p)]
    mm=modulus(dd,f,U)
    return ff[:7]+[x.x for x in mm],[[r[j] for j in cols] for r in J[:7]]+[x.g for x in mm],upper,cc

def verify(c):
    t=c['type'];f=[tuple(map(int,x)) for x in FACES[t].split()];p=[I(x) for x in c['p']];U=c['U'];cols=c['cols'];A=[[I(x) for x in row] for row in c['A']];R=I(c['R']);rho=I(c['rho']);target=[I(x) if x!='sqrt3/2' else I(3).sqrt()/2 for x in c['target']]
    assert abs(U[0][0]*U[1][1]-U[0][1]*U[1][0])==1
    assert len(set(cols))==9 and all(0<=j<24 for j in cols)
    assert R.l>0 and rho.l>0 and target[1].l>rho.h
    ff,_,_,_=fun(p,f,U,cols)
    box=[x+I(-R.h,R.h) if i in cols else x for i,x in enumerate(p)]
    _,JJ,upper,cc=fun(box,f,U,cols)
    assert all(x<16 for x in upper) and all(x.l>0 for x in cc)
    residual=ff[:7]+[a-b for a,b in zip(ff[7:],target)]
    beta=max(sum(a*b for a,b in zip(row,residual)).absmax() for row in A)
    L=max(sum(x.absmax() for x in row[7:]) for row in A)
    B=[[I(int(i==j))-sum(A[i][k]*JJ[k][j] for k in range(9)) for j in range(9)] for i in range(9)]
    q=max(sum(x.absmax() for x in row) for row in B)
    # beta + q*R + L*rho < R, all exactly certified.
    assert q<Q and beta*Q+q*R.h+L*rho.h<R.l*Q,(q/Q,beta/Q,L/Q,R.l/Q,rho.l/Q)
    margin,pairs=verify_embedding(box,f)
    print('PASS',t,'target',c['target'],'rho',c['rho'],'q',q/Q,'beta',beta/Q,'L',L/Q,'det margin',margin,flush=True)
    return q/Q

if __name__=='__main__':
    for c in json.loads(Path(__file__).with_name('moduli_certificates.json').read_text()):verify(c)
