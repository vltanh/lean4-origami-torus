#!/usr/bin/env python3
"""Close six complete regular-planar orientation classes at the hexagon.
See planar_patterns.md for coverage arguments and the geometric circuit lemma.
The only numerical step proposes linear dual certificates, checked exactly.
"""
from verify_planar_patterns import *
from collections import deque
from math import comb
A,B,T=sp.symbols('A B T'); cube=(A,B,T)
h,l,w=sp.symbols('h l w')
CLOSED={3021:6,3052:6,4017:6,10919:3,18289:6,18353:6}

def bsign(poly):
    P=sp.Poly(sp.expand(poly),*cube);cs=P.as_dict()
    if not cs:return 0
    for axis,v in enumerate(cube):
        n=P.degree(v);ret={}
        for exp,coef in cs.items():
            j=exp[axis]
            for i in range(j,n+1):
                new=exp[:axis]+(i,)+exp[axis+1:];ret[new]=ret.get(new,0)+coef*sp.Rational(comb(i,j),comb(n,j))
        cs=ret
    vals=list(cs.values())
    return 1 if min(vals)>=0 and max(vals)>0 else -1 if max(vals)<=0 and min(vals)<0 else None

def sign(expr):
    poly=sp.cancel(expr)
    if poly==0:return 0
    n,d=sp.fraction(poly);cn,fn=sp.factor_list(n);cd,fd=sp.factor_list(d);sg=int(sp.sign(cn*cd))
    for f,e in fn+fd:
        a=bsign(f)
        if a is None:return None
        if e%2:sg*=a
    return sg

def zero(expr):assert sp.cancel(expr)==0,sp.factor(expr)
def model(p):
    ds={e:sp.cancel(inner(delta(p,*e),delta(p,*e))/2) for e in E}
    d=lambda i,j:ds[tuple(sorted((i,j)))];AA=sp.Matrix([delta(p,1,5),delta(p,1,2)])*sp.Matrix([[2,1],[1,2]])
    r={1:(0,0),5:delta(p,1,5),2:delta(p,1,2)};inv=AA.inv().applyfunc(sp.cancel)
    for j in [0,3,4,6,7]:r[j]=tuple(sp.cancel(x) for x in inv*sp.Matrix([d(1,5)+d(1,j)-d(5,j),d(1,2)+d(1,j)-d(2,j)]))
    def residual(i,j):
        q=tuple(r[j][k]-r[i][k] for k in range(2));return sp.cancel(inner(q,q)/2-d(i,j))
    return r,residual

def subpoints(p,sub):return [tuple(sp.cancel(sp.sympify(x).subs(sub,simultaneous=True)) for x in q) for q in p]

def exact_family(m):
    s=[(m>>i)&1 for i in range(16)];rows,_=restrictions(s);v,f=exact_hull(rows);v,f,reason=reduce_eq(v,f,s);assert not reason;v,f,reason=metric_reduce(v,f,s);assert not reason
    p=points(v);r,res=model(p)
    def ar(text):
        i,j,k=map(int,text);return -determinant(delta(p,i,j),delta(p,i,k))
    def eq(a,b):zero(a-b)
    if m==10919:
        x9,x11,x13=f;d=x11-x13+1
        for face,expr in [('012',d),('053',-(3*x11+1)/3),('045',(3*x13-1)/3),('465',x11-x9),('357',x9-x13+1)]:eq(ar(face),expr)
        a=A;b=(1-A)*B;t=(1-A)*(1-B)*T/3;sub={x11:-(a+1)/3,x13:(b+1)/3,x9:-(a+1)/3-t};sub2={}
    elif m==18353:
        x1,x11,x13=f
        for face,expr in [('031',-x1),('024',(3*x11+1)/3),('256',-x11),('136',x1-x11),('237',(1-3*x13)/6),('274',(3*x13-6*x11-1)/6)]:eq(ar(face),expr)
        sub={x11:-A/3,x1:-A*B/3,x13:(1-2*A*T)/3};sub2={}
    elif m==3021:
        x3,x11,x12,x13=f;H=x13-x12-1;L=x12-x13+3*x3;k=x12+1
        g=(H+3*k)*L-3*k
        eq(res(1,7),(-2*x12-x13+3*x3-3)*g/L**2);eq(res(3,7),-3*k*g/L**2)
        eq((-2*x12-x13+3*x3-3).subs(x12,-1),L.subs(x12,-1))
        for face,expr in [('012',L/3),('024',H/3),('053',(1-H)/3),('136',(3*x11+1-2*H)/3),('164',(H-3*x11)/3),('263',(3*x11+1-2*H)*(1-L)/3),('357',(1-3*k-H)/3)]:eq(ar(face),expr)
        kk=h*l/(3*(1-l));sub={x3:(1+h+l)/3,x11:w,x12:kk-1,x13:kk+h};sub2={h:A,l:(1-A)*B,w:(2*A-1+(1-A)*T)/3}
    elif m==3052:
        x0,x1,x11,x13=f;H=x13;L=H-x0-2*x1;g=x0*H-2*x0+2*x1*H-x1-H**2+H-1
        eq(res(0,1),-(x0-x1+1)*g/L**2);eq(res(0,3),-(2*x0+x1-H+1)*g/L**2)
        eq(ar('012').subs({x0:(H-2)/3,x1:(H+1)/3},simultaneous=True),0)
        for face,expr in [('024',H/3),('053',(1-H)/3),('152',H*L/3),('263',(3*x11-2*H+1)/3),('465',(H-3*x11)/3),('136',(3*x11-2*H+1)*(1-L)/3)]:eq(ar(face),expr)
        b=(1+h+l*h-2*l)/3;sub={x13:h,x1:b,x0:h-2*b-l,x11:w};sub2={h:A,l:B,w:(2*A-1+(1-A)*T)/3}
    elif m==4017:
        x1,x4,x5,x11=f;g=3*x11*x4-3*x11*x5-3*x11+2*x4+x5
        eq(res(0,3)-res(1,3),-x1*g/(x11*(3*x1-3*x11-1)))
        for face,expr in [('024',(3*x11+1)/3),('274',-x11),('164',(x1-x11)*(3*x11+1)),('012',-x1*(3*x11+1)),('031',-x1*(x4-x5)),('357',(3*x11+1)*(1-x4+x5)/3),('152',x11*(3*x1-3*x11-1))]:eq(ar(face),expr)
        sub={x11:-h/3,x1:-h*l/3,x4:((h+1)*w-h)/3,x5:((h-2)*w-h)/3};sub2={h:A,l:B,w:T}
    elif m==18289:
        x9,x10,x11,x13=f;H=3*x9+2;L=x10+2*x11-3*x9
        eq(res(3,6),-3*x9*L-3*x11+6*x9+1)
        for face,expr in [('031',(1-H)/3),('024',H/3),('164',H*(1-L)/3),('256',(1-H)*L/3),('237',(1-3*x13)/6),('274',(x13-2*x9-1)/2)]:eq(ar(face),expr)
        a=(h-2)/3;b=-a*l+2*a+sp.Rational(1,3);sub={x9:a,x11:b,x10:3*a+l-2*b,x13:2*a+1+2*(1-h)*w/3};sub2={h:A,l:B,w:T}
    else:raise AssertionError(m)
    # Reconstruct after the first substitution, then certify the open cube.
    pp=subpoints(p,sub);rr,res=model(pp)
    for e in E:zero(res(*e))
    pp=subpoints(pp,sub2);rr={i:tuple(sp.cancel(sp.sympify(x).subs(sub2,simultaneous=True)) for x in q) for i,q in rr.items()}
    for i,j,k in F:assert sign(-determinant(delta(pp,i,j),delta(pp,i,k)))==1,(m,i,j,k)
    triples={t:sign(determinant(tuple(rr[t[1]][k]-rr[t[0]][k] for k in range(2)),tuple(rr[t[2]][k]-rr[t[0]][k] for k in range(2)))) for t in combinations(range(8),3)}
    if m==3052:assert all(sp.cancel(rr[0][i]-rr[7][i])==0 for i in range(2))
    print('PASS',m,'full-domain identities, all 24 metric equations, strict intrinsic faces; projected signs',Counter(triples.values()))
    return triples

def circuit_graph(triples):
    def ori(t):
        a=triples[tuple(sorted(t))];return None if a is None else a*(-1)**sum(i>j for i,j in combinations(t,2))
    cs=[];distinct=set()
    for e in combinations(range(8),2):
        vals=[ori((*e,v)) for v in range(8) if v not in e]
        if any(x in (-1,1) for x in vals):distinct.add(e)
        elif all(x==0 for x in vals):cs.append((e[:1],e[1:]))
    for t in combinations(range(8),3):
        if ori(t)!=0 or not all(e in distinct for e in combinations(t,2)):continue
        for h in range(8):
            if h in t:continue
            coeff=[ori(t[:i]+t[i+1:]+(h,)) for i in range(3)]
            if all(a in (-1,1) for a in coeff):
                coeff=[a*(-1)**i for i,a in enumerate(coeff)];coeff=[a*coeff[0] for a in coeff]
                cs.append((tuple(t[i] for i,a in enumerate(coeff) if a>0),tuple(t[i] for i,a in enumerate(coeff) if a<0)));break
    for q in combinations(range(8),4):
        coeff=[ori(q[:i]+q[i+1:]) for i in range(4)]
        if not all(a in (-1,1) for a in coeff):continue
        coeff=[a*(-1)**i for i,a in enumerate(coeff)];coeff=[a*coeff[0] for a in coeff]
        cs.append((tuple(q[i] for i,a in enumerate(coeff) if a>0),tuple(q[i] for i,a in enumerate(coeff) if a<0)))
    adj=defaultdict(list)
    for f,g in combinations(F,2):
        xs=[]
        for n,(a,b) in enumerate(cs):
            if set(a)<=set(f) and set(b)<=set(g):xs.append((n,1))
            if set(b)<=set(f) and set(a)<=set(g):xs.append((n,-1))
        for (a,sa),(b,sb) in combinations(xs,2):adj[a].append((b,sa*sb,(f,g)));adj[b].append((a,sa*sb,(f,g)))
    best=None
    for a in adj:
        q=deque([(a,1,[])]);seen={(a,1)}
        while q:
            b,s,p=q.popleft()
            if (b,s)==(a,-1):
                if best is None or len(p)<len(best):best=p
                break
            for c,d,pair in adj[b]:
                if (c,s*d) not in seen:seen.add((c,s*d));q.append((c,s*d,p+[(b,c,d,pair)]))
    assert best is not None
    print('PASS negative cycle:',[(cs[a],cs[b],s,pair) for a,b,s,pair in best])

if __name__=='__main__':
    from pathlib import Path
    import sys
    audit_archive(Path(sys.argv[1]) if len(sys.argv)>1 else Path(__file__).resolve().parent.parent/'type5_focus')
    remaining=screen();ledger={m:(n,d) for m,n,d in remaining}
    for m,n in CLOSED.items():
        assert ledger[m][0]==n;circuit_graph(exact_family(m));del ledger[m]
    assert len(ledger)==76 and sum(n for n,d in ledger.values())==415
    print('PASS: six complete classes (33 masks) have no vertical lift; 76 classes / 415 masks open')
    print(json.dumps(sorted((m,n,d) for m,(n,d) in ledger.items())))
