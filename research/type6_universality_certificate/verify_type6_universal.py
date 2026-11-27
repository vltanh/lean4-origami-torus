#!/usr/bin/env python3
"""Exact sign certificate for a second universal eight-vertex torus.
Requires SymPy; no floating-point arithmetic or numerical optimization.
Run with assertions enabled. Uses the planar families and flatness submersion
of Doyle--Lander--Schwartz--Trettel, arXiv:2611.21909, as published lemmas.
"""
from itertools import combinations
import sympy as s

Q = s.Rational
x, w, t = s.symbols('x w t')  # w=y^2; t=Bernstein interval parameter

def faces(st):
    return [tuple(map(int, f)) for f in st.split()]

def canonical(F):
    return {tuple(sorted(f)) for f in F}

F3 = faces('012 031 024 043 152 136 145 174 167 264 257 276 347 356 375 465')
LUTZ6 = faces('012 031 024 053 045 152 136 164 147 175 274 256 267 357 376 465')
F = [f for f in F3 if f not in [(0,1,2),(1,5,2)]] + [(0,1,5),(0,5,2)]
# Explicit isomorphism from our new triangulation to Lutz type 6.
perm = [3,7,0,6,1,5,2,4]
assert sorted(perm) == list(range(8))
assert canonical(tuple(perm[v] for v in f) for f in F) == canonical(LUTZ6)
E = {tuple(sorted(e)) for f in F for e in combinations(f,2)}
assert len(F) == 16 and len(E) == 24
assert sorted(sum(i in e for e in E) for i in range(8)) == [5,5,6,6,6,6,7,7]

DOMAINS = [(Q(0),Q(1,6)),(Q(1,6),Q(1,2))]
ORIGINAL_HEIGHTS = [(0,0,-11,-1,-3,-15,0,977),(0,-2017,0,-2,-1,-3,0,1430)]
NEW_HEIGHTS = [(0,0,-11,-1,-3,-15,0,977),(0,-361,2527,2525,5105,2527,1,19639)]

# Published planar vertex coordinates, with their second coordinate multiplied
# by y>0. Hence all signed areas and lifted volumes are scaled by y>0.
def planar(d):
    u,k,l = (Q(3,128),Q(11,32),Q(13,32)) if d==0 else (x/2-Q(1,2048),Q(1,16),Q(1,2))
    b=1-x-2*k
    p=[(0,0),(u,u*(b+2*k/l)),(u-Q(1,2),(1-2*u)*x/2),
       (-k-b*l,(l*(w-b*b)-2*b*k)/2),
       (x+k-Q(1,2),(w+b*x)/2),
       (u-Q(1,2),(w+b*(b+2*u-1))/2),
       (u-k,b*(u-k)),
       (u,(w+b*b+2*b*u)/2-(2*u-2*x-2*k+1)/(2*(1-l)))]
    return [tuple(map(s.expand,v)) for v in p]

def area(p,a,b,c):
    A,B,C=p[a],p[b],p[c]
    return s.expand((B[0]-A[0])*(C[1]-A[1])-(B[1]-A[1])*(C[0]-A[0]))

def vol(p,z,q):
    # determinant of the four rows (1, x_i, y*y_i, z_i).
    return s.expand(sum((-1)**(i+1)*z[a]*area(p,*(b for b in q if b!=a)) for i,a in enumerate(q)))

def bernstein(poly,lo,hi):
    p=s.Poly(s.expand(poly.subs(x,lo+(hi-lo)*t)),t,domain=s.QQ)
    n=0 if p.is_zero else p.degree()
    return [sum(p.nth(j)*s.binomial(i,j)/s.binomial(n,j) for j in range(i+1)) for i in range(n+1)]

def certified_sign(poly,lo,hi):
    poly=s.expand(poly)
    A=poly.subs(w,0); B=poly.coeff(w)
    assert s.expand(poly-A-B*w)==0
    # w>=1-x^2, so P=A+B(1-x^2)+B h, h>=0.
    a=bernstein(A+B*(1-x*x),lo,hi); b=bernstein(B,lo,hi)
    if all(v>0 for v in a) and all(v>=0 for v in b): return 1
    if all(v<0 for v in a) and all(v<=0 for v in b): return -1
    return 0 # no conclusion; not a claim that the volume is zero

def parity(q):
    return (-1)**sum(a>b for i,a in enumerate(q) for b in q[i+1:])

def verify(d):
    p=planar(d);lo,hi=DOMAINS[d]
    # Both diagonals of 0,1,5,2 have their opposite vertices on opposite sides.
    S=[certified_sign(area(p,*f),lo,hi) for f in [(1,2,0),(1,2,5),(0,5,1),(0,5,2)]]
    assert S == [1,-1,-1,1], S
    # A generic lift exists for each fixed point of the strip: independently
    # check the original paper's 70 strict volumes. This proves that none of
    # the 70 affine linear functionals of the heights is identically zero.
    quadruples=list(combinations(range(8),4))
    assert all(certified_sign(vol(p,ORIGINAL_HEIGHTS[d],q),lo,hi) for q in quadruples)
    V={q:certified_sign(vol(p,NEW_HEIGHTS[d],q),lo,hi) for q in quadruples}
    def S(q):return parity(q)*V[tuple(sorted(q))]
    pairs=0; witness_counts=[0]*4
    for a,b in sorted(E):
        for c,e,f in sorted(canonical(F)):
            if len({a,b,c,e,f})!=5:continue
            # The five minors of the ordered 5-tuple (a,b,c,e,f).
            v=[S(q) for q in [(b,c,e,f),(a,c,e,f),(a,b,e,f),(a,b,c,f),(a,b,c,e)]]
            tests=[v[0]*v[1],v[2]*v[3],v[3]*v[4],-v[2]*v[4]]
            assert max(tests)>0,(d,(a,b),(c,e,f),v)
            witness_counts[next(i for i,test in enumerate(tests) if test>0)]+=1
            pairs+=1
    assert pairs==140
    expected=70 if d==0 else 67
    assert sum(bool(v) for v in V.values())==expected
    print('PASS family',d+1,'x interval',[str(lo),str(hi)],'all y^2>=1-x^2')
    print('  new lift certified volumes:',expected,'/70')
    print('  uncertified:', [''.join(map(str,q)) for q,v in V.items() if not v])
    print('  disjoint edge-face pairs:',pairs,'witness counts:',witness_counts)

if __name__=='__main__':
    for d in range(2):verify(d)
    print('PASS type 6, full modular fundamental domain (assuming the published planar family and submersion lemmas).')
