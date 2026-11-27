#!/usr/bin/env python3
"""Full Type 4 fixed-target domain in 26 affine-anchor variables.

The 14 intrinsic coordinates and 12 affine coordinates have no radical or
Gram-rank auxiliary variables. All embedding circuits use cubic affine
brackets, including lower-support circuits with zero cofactor entries.
"""
import argparse
import ctypes
import ctypes.util
from fractions import Fraction as Q
from hashlib import sha256
from itertools import combinations
from pathlib import Path
import sys
import sympy as S

sys.path.insert(0, str(Path(__file__).resolve().parents[1]/"type4_focus"))
import type4_fixed_cubic as old

V = tuple(range(8))
ANCHOR = (4,5,1,6)
OUTSIDE = (0,2,3,7)
EDGES = old.E
FACES = {tuple(sorted(f)) for f in old.F}
SIMPLICES = {(i,) for i in V} | EDGES | FACES
NONEDGES = tuple(e for e in combinations(V,2) if e not in EDGES)


def smt(polynomial):
    if isinstance(polynomial, S.Symbol):
        return str(polynomial)
    if polynomial.is_Number:
        return old.num(Q(int(S.numer(polynomial)),int(S.denom(polynomial))))
    if isinstance(polynomial,S.Add):
        return old.add(*(smt(x) for x in polynomial.args))
    if isinstance(polynomial,S.Mul):
        return old.mul(*(smt(x) for x in polynomial.args))
    if isinstance(polynomial,S.Pow):
        base, exponent = polynomial.args
        assert exponent.is_Integer and exponent>=0
        return old.mul(*(smt(base) for _ in range(int(exponent))))
    raise ValueError(polynomial)


def coordinates():
    z={4:S.zeros(3,1),5:S.Matrix([1,0,0]),
       1:S.Matrix([0,1,0]),6:S.Matrix([0,0,1])}
    for i in OUTSIDE:
        z[i]=S.Matrix(S.symbols(f'z{i}_0 z{i}_1 z{i}_2'))
    return z


def brackets(z):
    answer={}
    for q in combinations(V,4):
        i,*rest=q
        answer[q]=S.expand(S.Matrix.hstack(*(z[j]-z[i] for j in rest)).det())
    return answer


def five_partitions(five):
    available=sorted(s for s in SIMPLICES if set(s)<=set(five))
    for a,b in combinations(available,2):
        # A fixed affine basis can extend every lower-rank circuit support
        # to rank four. Extra vertices therefore need only come from it.
        if set(a).isdisjoint(b) and set(five)-set(a)-set(b)<=set(ANCHOR):
            yield a,b


def support_partitions(five):
    """Minimal singleton/neighbor circuits not already simplex crossings."""
    for vertex in five:
        neighbors=tuple(i for i in five if tuple(sorted((i,vertex))) in EDGES)
        for size in range(2,5):
            for support in combinations(neighbors,size):
                if support in SIMPLICES:
                    continue
                if set(five)-{vertex}-set(support)<=set(ANCHOR):
                    yield (vertex,),support


def baseline_prefix(K,cell):
    """Reuse every baseline constraint preceding its signed-Gram pivot.

    Exact structural assertions make a changed baseline fail explicitly.
    Four unknown nonedge slacks are replaced later by derived expressions.
    """
    source,_,_=old.build(K,cell,False)
    lines=source.splitlines()
    markers=[i for i,line in enumerate(lines) if line.startswith('(define-fun AC () Real ')]
    assert len(markers)==1
    prefix=lines[:markers[0]]
    declarations=[line for line in prefix if line.startswith('(declare-const ')]
    assert len(declarations)==18
    expected={f'(declare-const s{i}{j} Real)' for i,j in NONEDGES}
    assert expected<set(declarations)
    return prefix


def build(K,cell,full=True,support_cuts=True,mixed_faces=False):
    z=coordinates()
    p={i:(f'x{i}',f'b{i}') if i!=4 else ('0','0') for i in V}
    prefix=baseline_prefix(K,cell)
    intrinsic=[line for line in prefix if line.startswith('(declare-const ')
               and not line.startswith('(declare-const s')]
    assert len(intrinsic)==14
    lines=['(set-logic QF_NRA)']+intrinsic
    for i in OUTSIDE:
        lines.extend(f'(declare-const {coordinate} Real)' for coordinate in z[i])
    def define(name,expression):
        lines.append(f'(define-fun {name} () Real {expression})')
        return name
    def assertion(expression):
        lines.append(f'(assert {expression})')
    def difference(i,j,shift=(0,0)):
        m,n=shift
        return (old.add(old.sub(p[j][0],p[i][0]),old.num(Q(m)+Q(n,2))),
                old.add(old.sub(p[j][1],p[i][1]),old.num(n)))
    def norm(vector):
        return old.add(old.sq(vector[0]),old.mul(str(old.W),old.sq(vector[1])))
    def distance(i,j):
        if i==j:
            return '0'
        if i>j:
            i,j=j,i
        return norm(difference(i,j,K[i,j]))
    basis=ANCHOR[1:]
    G=[]
    for i in range(3):
        row=[]
        for j in range(3):
            if j<i:
                row.append(G[j][i])
            elif i==j:
                row.append(define(f'gA{i}{j}',distance(4,basis[i])))
            else:
                row.append(define(f'gA{i}{j}',old.mul(old.num(Q(1,2)),
                           old.sub(old.add(distance(4,basis[i]),distance(4,basis[j])),
                                   distance(basis[i],basis[j])))))
        G.append(row)
    gram_symbols=S.Matrix(3,3,lambda i,j:S.Symbol(G[i][j]))
    spatial={}
    for i,j in combinations(V,2):
        dz=z[j]-z[i]
        spatial[i,j]=define(f'eD{i}{j}',smt(S.expand((dz.T*gram_symbols*dz)[0])))
    # Keep the baseline prefix byte-for-byte except for declarations whose
    # unknowns have now become derived nonedge metric quantities.
    expected_replacements=0
    for line in prefix[1:]:
        if line in intrinsic:
            continue
        replaced=False
        for i,j in NONEDGES:
            if line==f'(declare-const s{i}{j} Real)':
                define(f's{i}{j}',old.mul(old.num(Q(1,2)),
                       old.sub(norm(difference(i,j)),spatial[i,j])))
                expected_replacements+=1;replaced=True;break
            if line.startswith(f'(define-fun d{i}{j} () Real '):
                define(f'd{i}{j}',spatial[i,j])
                expected_replacements+=1;replaced=True;break
        if not replaced:
            lines.append(line)
    assert expected_replacements==8
    # The six anchor edges are identities by polarization. Keep four radial
    # equations, then subtract them from the other edge equations. Ten of
    # the resulting dot-product equations are cubic (one fixed anchor);
    # four radial and four outside/outside equations are quartic.
    cubic_metric_equations=0
    quartic_metric_equations=0
    for i,j in sorted(EDGES):
        if not {i,j}<=set(ANCHOR):
            if 4 in (i,j):
                assertion(old.expr('=',spatial[i,j],f'd{i}{j}'))
                quartic_metric_equations+=1
            else:
                spatial_dot=define(f'eG{i}{j}',smt(S.expand((z[i].T*gram_symbols*z[j])[0])))
                radial_i=f'd{min(i,4)}{max(i,4)}'
                radial_j=f'd{min(j,4)}{max(j,4)}'
                intrinsic_dot=old.mul(old.num(Q(1,2)),old.sub(old.add(radial_i,radial_j),f'd{i}{j}'))
                assertion(old.expr('=',spatial_dot,intrinsic_dot))
                if i in ANCHOR or j in ANCHOR:
                    cubic_metric_equations+=1
                else:
                    quartic_metric_equations+=1
    assert (cubic_metric_equations,quartic_metric_equations)==(10,8)
    assertion(old.expr('>',G[0][0],'0'))
    assertion(old.expr('>',old.det([row[:2] for row in G[:2]]),'0'))
    # det(G)=C*Q. The positive factor C is the strict radial nearest-lift
    # deficit for the competitor p5+shift(1,5). Removing it leaves Q quartic
    # rather than the naive degree-six determinant expansion (whose actual
    # degree is five after cancellation).
    m,n=K[1,5]
    k=Q(m)+Q(n,2)
    x5,b5=p[5];x1,b1=p[1];x6,b6=p[6]
    C=define('anchorC',old.add(old.mul(old.num(k),x5),old.mul(old.num(old.W*n),b5),
                             old.num((k*k+old.W*n*n)/2)))
    delta=define('anchorDelta',old.sub(old.mul(x1,b6),old.mul(x6,b1)))
    e=define('anchorE',old.add(old.mul(old.add(x5,old.num(k)),old.sub(b6,b1)),
                             old.mul(old.add(b5,old.num(n)),old.sub(x1,x6))))
    f=define('anchorF',old.add(old.mul(str(old.W),old.sq(old.sub(b6,b1))),
                             old.sq(old.sub(x1,x6))))
    quartic=define('anchorQ',old.sub(old.add(old.mul(old.num(-2*old.W),old.sq(delta)),
                                           old.mul(old.num(2*old.W),delta,e)),old.mul(C,f)))
    assertion(old.expr('>',C,'0'))
    assertion(old.expr('>',quartic,'0'))
    raw_brackets=brackets(z)
    bracket={q:(smt(polynomial) if polynomial.is_Number else
               define('B'+''.join(map(str,q)),smt(polynomial)))
             for q,polynomial in raw_brackets.items()}
    for q in combinations(V,4):
        if all(e in EDGES for e in combinations(q,2)):
            if raw_brackets[q].is_Number:
                assert raw_brackets[q]!=0
            else:
                assertion(old.expr('not',old.expr('=',bracket[q],'0')))
    circuit_assertions=0
    support_assertions=0
    if full or support_cuts:
        for five in combinations(V,5):
            cofactors=[((-1)**j,bracket[five[:j]+five[j+1:]],
                        (-1)**j*raw_brackets[five[:j]+five[j+1:]])
                       for j in range(5)]
            partitions=([(a,b,'embedding') for a,b in five_partitions(five)] if full else [])
            if support_cuts:
                partitions.extend((a,b,'support') for a,b in support_partitions(five))
            for a,b,kind in partitions:
                for orientation in (-1,1):
                    conditions=[];possible=True
                    for i,(coefficient,expression,polynomial) in zip(five,cofactors):
                        target=orientation if i in a else -orientation if i in b else 0
                        if polynomial.is_Number:
                            if int(S.sign(polynomial))!=target:
                                possible=False;break
                            continue
                        signed=expression if coefficient==1 else old.neg(expression)
                        conditions.append(old.expr('>' if target==1 else '<' if target==-1 else '=',signed,'0'))
                    if possible:
                        assert conditions  # the fixed strict anchor is not an obstruction itself
                        assertion(old.expr('not',old.expr('and',*conditions)))
                        if kind=='embedding':
                            circuit_assertions+=1
                        else:
                            support_assertions+=1
    mixed_assertions=0
    if mixed_faces:
        for vertex in V:
            neighbors={j for j in V if tuple(sorted((vertex,j))) in EDGES}
            options=[]
            for face in sorted(FACES):
                if vertex not in face:
                    continue
                side=[]
                for j in sorted(neighbors-set(face)):
                    ordered=face+(j,)
                    inversions=sum(ordered[k]>ordered[l] for k in range(4) for l in range(k+1,4))
                    expression=bracket[tuple(sorted(ordered))]
                    side.append(old.neg(expression) if inversions%2 else expression)
                assert len(side)>=2
                options.append(old.expr('and',
                               old.expr('or',*(old.expr('>',value,'0') for value in side)),
                               old.expr('or',*(old.expr('<',value,'0') for value in side))))
            assertion(old.expr('or',*options))
            mixed_assertions+=1
    result='\n'.join(lines)+'\n'
    nvar=sum(line.startswith('(declare-const ') for line in lines)
    assert nvar==26
    metadata={'variables':nvar,
              'assertions':sum(line.startswith('(assert ') for line in lines),
              'metric_equations':18,'circuit_assertions':circuit_assertions,
              'cubic_metric_equations':10,'quartic_metric_equations':8,
              'support_assertions':support_assertions,'mixed_face_assertions':mixed_assertions,
              'bytes':len(result.encode()),'full':full}
    return result,metadata


def cases():
    for marking,shifts in enumerate(old.SH,1):
        K,raw=old.enumerate_cells(shifts)
        representatives=old.orbits(K,old.maximal(raw))
        for number,cell in enumerate(representatives,1):
            yield f'ray{marking}_{number}',K,cell


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('output',type=Path)
    parser.add_argument('--case',default='ray2_2',choices=[f'ray1_{i}' for i in range(1,7)]+['ray2_1','ray2_2'])
    parser.add_argument('--relaxation',action='store_true',help='omit embedding circuits; not a full-domain decision')
    parser.add_argument('--no-support-cuts',action='store_true',help='omit the proved strict-neighbor-support cuts')
    parser.add_argument('--mixed-faces',action='store_true',help='add the necessary mixed-side incident-face disjunctions')
    parser.add_argument('--solve-ms',type=int,default=0,help='one bounded libz3 attempt in milliseconds')
    args=parser.parse_args()
    for name,K,cell in cases():
        if name==args.case:
            formula,metadata=build(K,cell,not args.relaxation,not args.no_support_cuts,args.mixed_faces)
            args.output.parent.mkdir(parents=True,exist_ok=True)
            payload=formula+'(check-sat)\n'
            args.output.write_text(payload)
            print(name,metadata,flush=True)
            print('input_sha256',sha256(payload.encode()).hexdigest(),flush=True)
            if args.solve_ms:
                library_path=ctypes.util.find_library('z3')
                library=ctypes.CDLL(library_path)
                library.Z3_get_full_version.restype=ctypes.c_char_p
                print('solver_version',library.Z3_get_full_version().decode(),
                      'library',library_path,'timeout_ms',args.solve_ms,flush=True)
                decision,reason=old.solve(formula,args.solve_ms)
                print('solver', {1:'SAT',-1:'UNSAT',0:'UNKNOWN'}[decision],reason,flush=True)
            break
