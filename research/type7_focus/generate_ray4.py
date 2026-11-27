#!/usr/bin/env python3
"""Exact Gram-completion systems for the two elongated Type 7 ray_4 orbits.
Usage: python generate_ray4.py OUTPUT_DIR [Y_SQUARED]
Omit Y_SQUARED for the whole range y^2 >= 35/4; give a positive rational
(e.g. 16) to specialize. Requires Python 3 only. Generated files not versioned.
"""
import json, sys
from fractions import Fraction
from itertools import combinations, permutations
from pathlib import Path
P = Path(__file__).resolve().parent
D = P.parent / 'linking_checkpoint'
V = tuple(range(8)); A = (0,1,2,7); B = (4,5,6,3)

def op(f,*a): return '('+f+' '+' '.join(a)+')'
def add(*a): return '0' if not a else a[0] if len(a)==1 else op('+',*a)
def mul(*a): return '1' if not a else a[0] if len(a)==1 else op('*',*a)
def neg(a): return op('-',a)
def sub(a,b): return op('-',a,b)
def rat(a):
    a=Fraction(a); n,d=a.numerator,a.denominator
    n=str(n) if n>=0 else neg(str(-n))
    return n if d==1 else op('/',n,str(d))
def all_(a): return 'true' if not a else a[0] if len(a)==1 else op('and',*a)
def any_(a): return 'false' if not a else a[0] if len(a)==1 else op('or',*a)
def det(M):
    n=len(M)
    return add(*(neg(mul(*(M[i][p[i]] for i in range(n)))) if sum(p[i]>p[j] for i in range(n) for j in range(i+1,n))%2 else mul(*(M[i][p[i]] for i in range(n))) for p in permutations(range(n))))

def generate(case,faces,model,w):
    F=[tuple(map(int,f)) for f in faces.split()]; E={e for f in F for e in combinations(sorted(f),2)}
    K={tuple(z['edge']):tuple(z['shift']) for z in case['edge_shifts']}
    K.update({(j,i):(-m,-n) for (i,j),(m,n) in list(K.items())})
    q=(-1,-1,-1,-1,0,-2,-1,-2)
    K={(i,j):(m,n+q[j]-q[i]) for (i,j),(m,n) in K.items()}
    assert all((i,j) in K for i,j in E)
    assert all(sum(K[e][k] for e in ((a,b),(b,c),(c,a)))==0 for a,b,c in F for k in range(2))
    L=['(set-logic QF_NRA)']; nvars=0
    def decl(a):
        nonlocal nvars
        nvars+=1;L.append(f'(declare-fun {a} () Real)');return a
    def define(a,b): L.append(f'(define-fun {a} () Real {b})');return a
    def require(a): L.append(op('assert',a))
    def abslt(a,b): return all_([op('<',a,b),op('>',a,neg(b))])
    t=decl('t') if w is None else define('t',rat(1/w))
    require(all_([op('>',t,'0'),op('<=',t,rat(Fraction(4,35)))]))
    x=['0']+[decl(f'x{i}') for i in V[1:]]
    c=['0']+[decl(f'c{i}') for i in V[1:]]
    for v in x[1:]: require(abslt(v,'3'))
    for i,j in combinations(V,2): require(abslt(sub(c[j],c[i]),rat(Fraction(3,8))))
    y=[define(f'y{i}',add(rat(Fraction(i%2,2)),mul(t,c[i]))) for i in V]
    def direction(i,j,m,n): return (add(sub(x[j],x[i]),rat(Fraction(2*m+n,2))),add(sub(y[j],y[i]),rat(n)))
    def norm(X,Y): return add(mul(t,X,X),mul(Y,Y)) # t times physical squared length
    dist={}; uv={}
    for i,j in combinations(V,2):
        if (i,j) in E:
            u,v=direction(i,j,*K[i,j]);u=define(f'X{i}{j}',u);v=define(f'Y{i}{j}',v)
            uv[i,j]=(u,v);uv[j,i]=(neg(u),neg(v))
            d=define(f'D{i}{j}',norm(u,v)); require(op('>',d,'0'))
            require(abslt(mul('2',u),'1'))
            for s in (u,neg(u)): require(abslt(add(mul(t,s),mul('2',v)),add('1',mul(rat(Fraction(1,4)),t))))
        else:
            d=decl(f'z{i}{j}'); require(op('>',d,'0'))
            for m in range(-6,7): require(op('<=',d,norm(*direction(i,j,m,0))))
        dist[i,j]=dist[j,i]=d
    for i in V: dist[i,i]='0'
    areas=[]
    for k,(a,b,c0) in enumerate(F):
        u,v=uv[a,b],uv[a,c0]
        areas.append(define(f'area{k}',sub(mul(u[0],v[1]),mul(u[1],v[0]))))
    require(any_([all_([op('>',a,'0') for a in areas]+[op('=',add(*areas),'2')]),all_([op('<',a,'0') for a in areas]+[op('=',add(*areas),'(- 2)')])]))
    half=lambda a:mul(rat(Fraction(1,2)),a)
    G=[[define(f'G{i}{j}',half(sub(add(dist[A[0],A[i+1]],dist[A[0],A[j+1]]),dist[A[i+1],A[j+1]]))) for j in range(3)] for i in range(3)]
    g=define('g',det(G));require(op('>',G[0][0],'0'));require(op('>',det([r[:2] for r in G[:2]]),'0'));require(op('>',g,'0'))
    H=[[define(f'H{i}{j}',(neg if (i+j)%2 else lambda a:a)(det([[G[k][l] for l in range(3) if l!=i] for k in range(3) if k!=j]))) for j in range(3)] for i in range(3)]
    U={A[0]:['0']*3}; R={}
    for i in range(1,4): U[A[i]]=[G[j][i-1] for j in range(3)]
    for b in B:
        U[b]=[define(f'U{b}{i}',half(sub(add(dist[A[0],A[i+1]],dist[A[0],b]),dist[A[i+1],b]))) for i in range(3)]
        R[b]=[define(f'R{b}{i}',add(*(mul(H[i][j],U[b][j]) for j in range(3)))) for i in range(3)]
        require(op('=',add(*(mul(U[b][j],R[b][j]) for j in range(3))),mul(g,dist[A[0],b])))
    for a,b in combinations(B,2):
        require(op('=',mul('2',add(*(mul(U[a][j],R[b][j]) for j in range(3)))),mul(g,sub(add(dist[A[0],a],dist[A[0],b]),dist[a,b]))))
    # Inner-product coordinates U are obtained by an invertible linear
    # map with positive determinant relative to the anchor basis (G>0).
    # Use U, not H*U, for affine minors to keep their degree low.
    Q=list(combinations(V,4)); sA=model[Q.index(A)]; minors={}
    def minor(S,axes):
        key=(S,axes)
        if key not in minors:
            a,*rest=S
            minors[key]=define('m'+''.join(map(str,S))+'c'+''.join(map(str,axes)),det([[sub(U[b][k],U[a][k]) for k in axes] for b in rest]))
        return minors[key]
    for S,s in zip(Q,model):
        clique=all(e in E for e in combinations(S,2));positive=s==sA
        require(op(('>' if clique else '>=') if positive else ('<' if clique else '<='),minor(S,(0,1,2)),'0'))
    simplex={ (i,) for i in V }|E|{tuple(sorted(f)) for f in F}
    for n in range(3,6):
        for S in combinations(V,n):
            parts=[a for k in range(1,min(3,n-1)+1) for a in combinations(S,k) if S[0] in a and a in simplex and tuple(v for v in S if v not in a) in simplex]
            if not parts:continue
            rank=all_([op('=',minor(S,axes),'0') for axes in combinations(range(3),n-1)]) if n<=4 else 'true'
            for a in parts:
                tests=[]
                for axes in combinations(range(3),n-2):
                    vals=[minor(S[:i]+S[i+1:],axes) for i in range(n)]
                    signed=[v if ((i%2==0)==(j in a)) else neg(v) for i,(v,j) in enumerate(zip(vals,S))]
                    tests.append(any_([all_([op('>',v,'0') for v in signed]),all_([op('<',v,'0') for v in signed])]))
                require(op('not',all_([rank,any_(tests)])))
    assert nvars==(19 if w is None else 18)
    L.append('(check-sat)');return '\n'.join(L)+'\n',nvars

def main():
    out=Path(sys.argv[1]);out.mkdir(parents=True,exist_ok=True)
    w=Fraction(sys.argv[2]) if len(sys.argv)>2 else None
    assert w is None or w>=Fraction(35,4)
    cases=json.loads((D/'cases.json').read_text());case=next(c for c in cases if c['file']=='t7_ray_4.smt2')
    faces=json.loads((D/'lutz_faces.json').read_text())['7']
    models=json.loads((D/'ring4_full_signs.json').read_text())
    for branch,ix in enumerate((0,2),1):
        s,n=generate(case,faces,models[ix],w);name=f'R{branch}.smt2';(out/name).write_text(s);print(name,n,'real variables',len(s),'bytes')
if __name__=='__main__':main()
