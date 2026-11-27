#!/usr/bin/env python3
"""Exact rejection of the two-flip family at the hexagon on the stated open domain.
No numerical solver or sampled order type is used. See planar_flip.md.
"""
import sympy as s
from math import comb
from itertools import combinations, permutations, product
from collections import deque, Counter

u,k,l,K,R,T=s.symbols('u k l K R T')
b=s.Rational(1,2)-2*k;c=s.Rational(1,2)-k+2*k*k
p=[(0,0),(u,2*k*u/l),(u-s.Rational(1,2),(s.Rational(1,2)-u)*(1-2*k)),
   (-k-b*l,l*c),(k,c),(u-s.Rational(1,2),c),(u-k,0),(u,c-(u-k)/(1-l))]
FACES=[tuple(map(int,v)) for v in '015 052 031 024 043 136 145 174 126 264 257 127 347 356 375 465'.split()]
EDGES=sorted({tuple(sorted(e)) for f in FACES for e in combinations(f,2)})
TRIS=list(combinations(range(8),3))
VARIABLE=[(0,2,3),(1,2,3),(2,3,4),(2,3,5),(2,3,6),(2,3,7)]
FIXED=dict((tuple(map(int,v[1:])),1 if v[0]=='+' else -1) for v in '''+012 +013 +014 +015 -016 +017 -024 -025 -026 -027 -034 -035 -036 -037 +045 -046 -047 -056 -057 +067 -124 -125 +126 -127 -134 -135 +136 -137 +145 +146 -147 +156 -157 -167 +245 -246 -247 -256 -257 +267 +345 -346 -347 -356 -357 +367 +456 +457 +467 +567'''.split())
assert set(FIXED)|set(VARIABLE)==set(TRIS) and len(FIXED)==50

def area(t):
    i,j,h=t
    return s.factor((p[j][0]-p[i][0])*(p[h][1]-p[i][1])-(p[j][1]-p[i][1])*(p[h][0]-p[i][0]))
A={t:area(t) for t in TRIS}

# Every admissible parameter has this representation on the open unit cube.
kk=K/2;cc=c.subs(k,kk); LN=2*kk**2+(s.Rational(1,2)-kk)*R; LD=cc
UD=LN+2*kk*(LD-LN); UN=kk*UD+T*(LD-LN)*(LN-2*kk**2)
variables=(K,R,T)
pLN,pLD,pUN,pUD=(s.Poly(v,*variables) for v in (LN,LD,UN,UD))
def substitute(expr):
    P=s.Poly(expr,u,k,l);du,dl=P.degree(u),P.degree(l);ret=s.Poly(0,*variables)
    for (i,j,h),v in P.terms():
        ret+=v*s.Poly(kk**j,*variables)*pUN**i*pUD**(du-i)*pLN**h*pLD**(dl-h)
    return ret

def bernstein_sign(P):
    cs=P.as_dict()
    for axis,v in enumerate(variables):
        n=P.degree(v);ret={}
        for exp,coef in cs.items():
            j=exp[axis]
            for i in range(j,n+1):
                new=exp[:axis]+(i,)+exp[axis+1:]
                ret[new]=ret.get(new,0)+coef*s.Rational(comb(i,j),comb(n,j))
        cs=ret
    vals=list(cs.values())
    if min(vals)>=0 and max(vals)>0:return 1
    if max(vals)<=0 and min(vals)<0:return -1
    return 0

cache={}
def strict_sign(expr, extra=None):
    extra=extra or {}
    n,d=s.fraction(s.factor(expr));cn,fs=s.factor_list(n);cd,gs=s.factor_list(d)
    sign=int(s.sign(cn*cd))
    assert sign!=0
    for f,e in fs+gs:
        if f in extra:sg=extra[f]
        else:
            if f not in cache:cache[f]=bernstein_sign(substitute(f))
            sg=cache[f]
        assert sg in (-1,1),f
        if e%2:sign*=sg
    return sign

for t,sg in FIXED.items():assert strict_sign(A[t])==sg,t
assert all(A[t]!=0 for t in VARIABLE)
print('PASS: 50 fixed strict orientation signs by rational Bernstein coefficients; six nonzero variable polynomials')

# Check domain necessity directly from the source's positively oriented
# intrinsic faces. The source uses scaled vertical coordinate Y=y*y_coord.
P=[s.Matrix([X,Y+b*X]) for X,Y in p]; Q=P.copy()
Q[3]=s.Matrix([k,-(2*b*k+l*(b*b+s.Rational(3,4)))/2])
Q[6]=s.Matrix([u+k,b*(u-k)])
e=s.Matrix([1,0]); tau=s.Matrix([s.Rational(1,2),s.Rational(3,4)])
sh=[s.zeros(2,1),e,tau,e-tau,-tau]
source=[('012',[0,0,0]),('031',[0,0,0]),('024',[0,0,4]),('043',[0,4,0]),
        ('152',[0,0,0]),('136',[0,0,0]),('145',[0,0,0]),('174',[0,0,0]),
        ('167',[0,0,0]),('264',[1,0,3]),('257',[1,1,0]),('276',[1,0,0]),
        ('347',[2,0,0]),('356',[0,3,0]),('375',[2,0,1]),('465',[3,0,3])]
IA={}
for f,ss in source:
    v=[Q[int(i)]+sh[j] for i,j in zip(f,ss)]
    IA[f]=s.factor(s.det(s.Matrix.hstack(v[1]-v[0],v[2]-v[0])))
    for i,j in combinations(range(3),2):
        df=v[j]-v[i]; dp=P[int(f[j])]-P[int(f[i])]
        assert s.cancel(s.Rational(3,4)*(df[0]**2-dp[0]**2)+df[1]**2-dp[1]**2)==0
    assert strict_sign(IA[f])==1,f
D=l+2*k*(1-l); g=c*l*(1-l)-(u-k)*l-2*k*u*(1-l)
F=(4*k*k-2*k+1)*(l-1)**2+(1-4*k)*(l-1)+1
identities={'024':(1-2*u)/4,'043':(4*k*k-2*k+1)*D/4,
    '012':u*(1-2*u)*D/(2*l),'167':k*g/(l*(1-l)),
    '174':(u-k)*g/(l*(1-l)),
    '264':(1-2*k)*(4*(u-k)**2-2*(u-k)+1)/4,
    '347':(u-k)*F/(2*(1-l))}
for f,expr in identities.items():assert s.cancel(IA[f]-expr)==0,f
assert s.expand((1-4*k)**2-4*(4*k*k-2*k+1))==-3
print('PASS: source edge isometries, all intrinsic orientations, and necessary open-domain identities')

# Verify the order of rays at vertex 2 and exclude reversed mixed sequences.
def parity(t):return (-1)**sum(a>b for a,b in combinations(t,2))
def ori(sign,*t):return sign[tuple(sorted(t))]*parity(t)
ORDER=[0,6,1,7,4,5]; BASE=[0,1,4,5,6,7]
assert all(ori(FIXED,2,a,b)==1 for a,b in combinations(ORDER,2))
E=2*k*l-2*k-2*l+1; J=(1-4*k)*l+2*k+2*u-1
assert s.cancel(A[(0,2,3)]+k*(2*u-1)*E/2)==0
assert s.cancel(A[(2,3,5)]-(-2*k*k+2*k*u-u)*J/2)==0
U=k+(1-l)*(l*c-2*k*k)/(l+2*k*(1-l))
assert s.cancel(J.subs(u,U)+2*k*(1-l)*E/(l+2*k*(1-l)))==0
print('PASS: angular order and endpoint implication give seven exhaustive generic patterns')

# Exact sign-only graph for all projected intersections of disjoint edge/face.
def links(sgs):
    sign=FIXED|dict(zip(VARIABLE,sgs));assert len(sign)==56
    def o(*t):return ori(sign,*t)
    def cofactor(q,i):return (-1)**q.index(i)*sign[tuple(v for v in q if v!=i)]
    adj={}
    for i,j in EDGES:
        for f in FACES:
            if i in f or j in f:continue
            a,b,c=f;sg=o(a,b,c);ends=[]
            for v in (i,j):
                if o(a,b,v)==o(b,c,v)==o(c,a,v)==sg:
                    q=tuple(sorted((*f,v)));ends.append((q,cofactor(q,v)))
            for v,w in combinations(f,2):
                if o(i,j,v)!=o(i,j,w) and o(v,w,i)!=o(v,w,j):
                    q=tuple(sorted((i,j,v,w)));ends.append((q,cofactor(q,i)))
            if ends:
                assert len(ends)==2
                (q,s1),(r,s2)=ends;d=s1*s2
                adj.setdefault(q,[]).append((r,d,((i,j),f)))
                adj.setdefault(r,[]).append((q,d,((i,j),f)))
    return adj

def path(adj,q,r,sign):
    todo=deque([(q,1,[])]);seen={(q,1)}
    while todo:
        v,sg,ps=todo.popleft()
        if (v,sg)==(r,sign):return ps
        for w,d,pair in adj[v]:
            node=(w,sg*d)
            if node not in seen:seen.add(node);todo.append((*node,ps+[(v,w,d,pair)]))
    return None

def negative_cycle(adj):
    paths=[pp for v in adj if (pp:=path(adj,v,v,-1)) is not None]
    return min(paths,key=len) if paths else None

def fmt(ps):
    return ' '.join(''.join(map(str,e[0]))+('+' if e[2]>0 else '-') for e in ps)+' '+''.join(map(str,ps[-1][1]))

# At each generic order pattern exhaust all strictly convex projected flips.
START=tuple(sorted(tuple(sorted(map(int,f))) for f,_ in source))
GOAL=tuple(sorted(tuple(sorted(f)) for f in FACES))
LUTZ5={frozenset(map(int,f)) for f in '031 053 045 136 164 465 012 024 152 147 175 263 237 274 256 357'.split()}
perm=(0,1,4,3,5,2,6,7)
assert {frozenset(perm[v] for v in f) for f in GOAL}==LUTZ5

def flip_cover(sgs):
    sign=FIXED|dict(zip(VARIABLE,sgs));o=lambda *t:ori(sign,*t)
    seen={START:[]};todo=deque([START])
    while todo:
        fs=todo.popleft();edges={e for f in fs for e in combinations(f,2)}
        for a,b in sorted(edges):
            pair=[f for f in fs if a in f and b in f];assert len(pair)==2
            c,d=sorted(next(v for v in f if v not in (a,b)) for f in pair)
            if (c,d) in edges:continue
            if o(a,b,c)==o(a,b,d) or o(c,d,a)==o(c,d,b):continue
            new=tuple(sorted((set(fs)-set(pair))|{tuple(sorted((a,c,d))),tuple(sorted((b,c,d)))}))
            if new not in seen:seen[new]=seen[fs]+[((a,b),(c,d))];todo.append(new)
    assert len(seen)==3
    assert seen[GOAL]==[((1,2),(0,5)),((6,7),(1,2))]
    for fs in seen:
        edges={e for f in fs for e in combinations(f,2)};degree=Counter(v for e in edges for v in e)
        assert (sorted(degree.values())==[5,5,5,6,6,7,7,7])==(fs==GOAL)

qs=[((0,1,2,4),1),((0,1,2,6),-1),((0,2,3,5),-1),((0,3,4,6),-1),((1,3,5,6),1)]
cycles=0;certs=0
for i in range(7):
    ss=[-1 if j<i else 1 for j in range(6)]
    sgs=tuple(ss[ORDER.index(v)] for v in BASE);pattern=''.join('+' if v>0 else '-' for v in sgs)
    flip_cover(sgs)
    adj=links(sgs);cyc=negative_cycle(adj)
    if cyc is not None:
        cycles+=1;print(pattern,'PASS negative cycle:',fmt(cyc));continue
    assert pattern=='---+--'
    for q,sg in qs[1:]:
        pp=path(adj,qs[0][0],q,sg);assert pp is not None
        print(pattern,'PASS sign propagation:',fmt(pp))
    # Gauge z0=z1=z2=0 (A012 is strict), leaving z3,z4,z5,z6 in these five forms.
    M=s.Matrix([[sg*(-1)**q.index(j)*A[tuple(v for v in q if v!=j)] if j in q else 0 for j in (3,4,5,6)] for q,sg in qs])
    # Alternating maximal minors are a left null vector by Laplace expansion.
    # A023<0 implies E<0 in this chamber. All other signs are Bernstein checks.
    for j in range(5):
        cof=s.factor((-1)**j*M[:j,:].col_join(M[j+1:,:]).det(method='domain-ge'))
        assert strict_sign(cof,{E:-1})==-1,j
    certs+=1;print(pattern,'PASS five strictly positive weights in exact null relation')
assert (cycles,certs)==(6,1)
print("PASS: all seven convex-flip graphs have three states and exactly one Type 5 state")
print('PASS: no embedded vertical lift anywhere in the open two-flip hexagonal family; nongeneric points covered by openness')
