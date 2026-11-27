#!/usr/bin/env python3
"""Independent exact identities and degeneracy checks for direct_metric.py."""
from collections import Counter
from itertools import combinations
import re
import sympy as S
import direct_metric as D


def parse_smt(source):
    tokens=iter(re.findall(r'\(|\)|[^\s()]+',source))
    def parse(token):
        if token!='(':
            return token
        result=[]
        for following in tokens:
            if following==')':
                return result
            result.append(parse(following))
        raise AssertionError('unclosed expression')
    return [parse(token) for token in tokens]


def evaluate(expression,environment):
    if isinstance(expression,str):
        return environment[expression] if expression in environment else S.Rational(expression)
    op,*arguments=expression
    values=[evaluate(a,environment) for a in arguments]
    if op=='+':return sum(values)
    if op=='*':return S.prod(values)
    if op=='-':return -values[0] if len(values)==1 else values[0]-values[1]
    if op=='/':return values[0]/values[1]
    raise AssertionError(op)


def partition_key(a,b):
    return tuple(sorted((tuple(sorted(a)),tuple(sorted(b)))))


def exact_minimal_circuits(z,with_support=False):
    """Independent oracle: nullspaces on the minimal support itself.

    It does not use four-brackets, five-point extensions, or the encoder's
    list of extension partitions. A 1D kernel with no zero coefficient is
    exactly a minimal affine circuit; its signs give barycentric overlap.
    """
    violations=set()
    for size in range(2,6):
        for support in combinations(D.V,size):
            matrix=S.Matrix.hstack(*(S.Matrix([1,*z[i]]) for i in support))
            kernel=matrix.nullspace()
            if len(kernel)!=1 or any(value==0 for value in kernel[0]):
                continue
            plus=tuple(i for i,value in zip(support,kernel[0]) if value>0)
            minus=tuple(i for i,value in zip(support,kernel[0]) if value<0)
            forbidden=plus in D.SIMPLICES and minus in D.SIMPLICES
            if with_support:
                for singleton,other in ((plus,minus),(minus,plus)):
                    if len(singleton)==1 and all(tuple(sorted((singleton[0],j))) in D.EDGES for j in other):
                        forbidden=True
            if forbidden:
                violations.add(partition_key(plus,minus))
    return violations


def encoded_circuits(z,with_support=False):
    bracket=D.brackets(z)
    violations=set()
    for five in combinations(D.V,5):
        coefficients=[(-1)**j*bracket[five[:j]+five[j+1:]] for j in range(5)]
        plus=tuple(i for i,value in zip(five,coefficients) if value>0)
        minus=tuple(i for i,value in zip(five,coefficients) if value<0)
        partitions=list(D.five_partitions(five))
        if with_support:partitions+=list(D.support_partitions(five))
        for a,b in partitions:
            if (plus==a and minus==b) or (plus==b and minus==a):
                violations.add(partition_key(a,b))
    return violations


# Generic polynomial metric identity, with no reference to the winding or
# to the formulas used by the generator: Euclidean norm of an actual B*d.
B=S.Matrix(3,3,S.symbols('m0:9'))
d=S.Matrix(S.symbols('t0:3'))
assert S.expand((B*d).dot(B*d)-(d.T*(B.T*B)*d)[0])==0

# Verify the removed positive factor of the anchor determinant for BOTH
# marking shifts. All six intrinsic coordinates and W remain indeterminates.
x5,b5,x1,b1,x6,b6,W=S.symbols('x5 b5 x1 b1 x6 b6 W')
def idot(a,b):return a[0]*b[0]+W*a[1]*b[1]
v5,v1,v6=(x5,b5),(x1,b1),(x6,b6)
for k,n in ((S.Rational(1,2),1),(S.Integer(1),0)):
    C=k*x5+W*n*b5+(k*k+W*n*n)/2
    shifted=(x5+k,b5+n)
    G=S.Matrix([[idot(v5,v5),idot(shifted,v1)-C,idot(shifted,v6)-C],
                [idot(shifted,v1)-C,idot(v1,v1),idot(v1,v6)],
                [idot(shifted,v6)-C,idot(v1,v6),idot(v6,v6)]])
    delta=x1*b6-x6*b1
    e=(x5+k)*(b6-b1)+(b5+n)*(x1-x6)
    f=W*(b6-b1)**2+(x1-x6)**2
    quartic=-2*W*delta**2+2*W*delta*e-C*f
    assert S.expand(G.det()-C*quartic)==0

# Obtain the active checked cell from the original finite enumeration.
for name,K,cell in D.cases():
    if name=='ray2_2':break
formula,metadata=D.build(K,cell,True,True,True)
baseline=D.baseline_prefix(K,cell)
old_assertions=Counter(line for line in baseline if line.startswith('(assert '))
new_assertions=Counter(line for line in formula.splitlines() if line.startswith('(assert '))
assert not (old_assertions-new_assertions)
assert len([f for f in parse_smt(formula) if f[0]=='declare-const'])==26
definitions={f[1]:f[4] for f in parse_smt(formula) if f[0]=='define-fun'}
degree_environment={f[1]:1 for f in parse_smt(formula) if f[0]=='declare-const'}
def degree(expression):
    if isinstance(expression,str):return degree_environment.get(expression,0)
    op,*arguments=expression
    values=[degree(a) for a in arguments]
    if op=='*':return sum(values)
    if op=='/':
        assert values[1]==0
        return values[0]
    return max(values,default=0)
for form in parse_smt(formula):
    if form[0]=='define-fun':degree_environment[form[1]]=degree(form[4])
assert max(degree(form[1]) for form in parse_smt(formula) if form[0]=='assert')==4

# Verify the actual emitted anchor expressions against independently computed
# marked squared lengths, using exact rational intrinsic coordinates.
intrinsic={i:(S.Rational(2*i-7,31),S.Rational(i*i-17,43)) for i in D.V}
intrinsic[4]=(S.Integer(0),S.Integer(0))
environment={name:value for i,(x,b) in intrinsic.items() if i!=4
             for name,value in ((f'x{i}',x),(f'b{i}',b))}
def marked_distance(i,j):
    if i>j:i,j=j,i
    m,n=K[i,j]
    return (intrinsic[j][0]-intrinsic[i][0]+m+S.Rational(n,2))**2+D.old.W*(intrinsic[j][1]-intrinsic[i][1]+n)**2
for i,a in enumerate(D.ANCHOR[1:]):
    for j,b in enumerate(D.ANCHOR[1:]):
        name=f'gA{min(i,j)}{max(i,j)}'
        expected=marked_distance(4,a) if i==j else (marked_distance(4,a)+marked_distance(4,b)-marked_distance(a,b))/2
        assert evaluate(definitions[name],environment)==expected

# Evaluate every emitted spatial chord and bracket in a separate rational
# physical frame. The comparisons use Euclidean coordinates, not a Gram
# reconstruction, and also check the augmented-Gram clique determinant rule.
z={4:S.Matrix([0,0,0]),5:S.Matrix([1,0,0]),
   1:S.Matrix([0,1,0]),6:S.Matrix([0,0,1]),
   0:S.Matrix([2,3,5]),2:S.Matrix([3,7,11]),
   3:S.Matrix([-2,5,13]),7:S.Matrix([7,-5,17])}
physical_basis=S.Matrix([[2,1,-1],[1,3,2],[0,1,4]])
assert physical_basis.det()!=0
physical={i:physical_basis*z[i] for i in D.V}
gram=physical_basis.T*physical_basis
physical_env={f'z{i}_{j}':z[i][j] for i in D.OUTSIDE for j in range(3)}
physical_env.update({f'gA{i}{j}':gram[i,j] for i in range(3) for j in range(i,3)})
for i,j in combinations(D.V,2):
    expected=(physical[j]-physical[i]).dot(physical[j]-physical[i])
    assert evaluate(definitions[f'eD{i}{j}'],physical_env)==expected
    if f'eG{i}{j}' in definitions:
        assert evaluate(definitions[f'eG{i}{j}'],physical_env)==physical[i].dot(physical[j])
for q in combinations(D.V,4):
    i,*rest=q
    affine=S.Matrix.hstack(*(z[j]-z[i] for j in rest)).det()
    direct=S.Matrix.hstack(*(physical[j]-physical[i] for j in rest)).det()
    assert direct==physical_basis.det()*affine
    expression=definitions.get('B'+''.join(map(str,q)))
    if expression is not None:
        assert evaluate(expression,physical_env)==affine
    H=S.Matrix([[1+physical[i].dot(physical[j]) for j in q] for i in q])
    assert H.det()==gram.det()*affine**2

# Test every emitted polarized edge equation on nontrivial independent
# rational intrinsic/spatial inputs. This frame realizes the six anchor
# edges exactly (a rational 3-4-5 cap), while the other edge residuals may
# be nonzero. The identity R_ij=R_4i+R_4j-2*Q_ij must hold even then.
intrinsic.update({4:(S.Integer(0),S.Integer(0)),5:(-S.Rational(5,12),S.Integer(0)),
                  1:(S.Rational(1,3),S.Integer(0)),6:(S.Rational(1,3),S.Rational(1,D.old.Y))})
compatible_basis=S.Matrix([[S.Rational(5,12),S.Rational(4,15),S.Rational(4,15)],
                           [0,S.Rational(1,5),S.Rational(1,5)],[0,0,1]])
physical={i:compatible_basis*z[i] for i in D.V}
environment={name:value for i,(x,b) in intrinsic.items() if i!=4
             for name,value in ((f'x{i}',x),(f'b{i}',b))}
environment.update({f'z{i}_{j}':z[i][j] for i in D.OUTSIDE for j in range(3)})
for form in parse_smt(formula):
    if form[0]=='define-fun':environment[form[1]]=evaluate(form[4],environment)
assert environment['anchorC']>0
assert environment['anchorQ']>0
assert environment['anchorC']*environment['anchorQ']==(compatible_basis.T*compatible_basis).det()
for i,j in combinations(D.ANCHOR,2):
    assert (physical[j]-physical[i]).dot(physical[j]-physical[i])==marked_distance(i,j)
metric_assertions={form[1][1]:form[1] for form in parse_smt(formula)
                   if form[0]=='assert' and isinstance(form[1],list) and form[1][0]=='='
                   and isinstance(form[1][1],str) and form[1][1].startswith(('eD','eG'))}
assert len(metric_assertions)==18
assert Counter(degree(assertion) for assertion in metric_assertions.values())=={3:10,4:8}
for i,j in sorted(D.EDGES):
    if {i,j}<=set(D.ANCHOR):continue
    edge_residual=(physical[j]-physical[i]).dot(physical[j]-physical[i])-marked_distance(i,j)
    name=f'eD{i}{j}' if 4 in (i,j) else f'eG{i}{j}'
    _,left,right=metric_assertions[name]
    emitted_residual=evaluate(left,environment)-evaluate(right,environment)
    if 4 in (i,j):
        assert emitted_residual==edge_residual
    else:
        radial_i=physical[i].dot(physical[i])-marked_distance(4,i)
        radial_j=physical[j].dot(physical[j])-marked_distance(4,j)
        assert edge_residual==radial_i+radial_j-2*emitted_residual
        expected=physical[i].dot(physical[j])-(marked_distance(4,i)+marked_distance(4,j)-marked_distance(i,j))/2
        assert emitted_residual==expected

# Oriented face-side expressions use the parity of (sorted face,j). Verify
# that convention against actual physical determinants for every choice.
for face in D.FACES:
    i,j,k=face
    for vertex in D.V:
        if vertex in face:continue
        ordered=face+(vertex,)
        inversions=sum(ordered[a]>ordered[b] for a in range(4) for b in range(a+1,4))
        q=tuple(sorted(ordered));base,*others=q
        ordered_value=S.Matrix.hstack(physical[j]-physical[i],physical[k]-physical[i],physical[vertex]-physical[i]).det()
        sorted_value=S.Matrix.hstack(*(physical[t]-physical[base] for t in others)).det()
        assert ordered_value==(-1)**inversions*sorted_value

examples={
    'ordinary':z,
    'coincident':z|{0:z[1]},
    'collinear':z|{0:S.Matrix([S.Rational(1,2),0,0])},
    'coplanar':z|{0:S.Matrix([S.Rational(1,3),S.Rational(1,3),0])},
    'simultaneous':z|{0:S.Matrix([S.Rational(1,2),0,0]),
                       2:S.Matrix([S.Rational(1,2),S.Rational(1,2),0]),
                       3:S.Matrix([S.Rational(1,2),-S.Rational(1,2),0]),
                       7:S.Matrix([0,0,0])},
}
support_sizes=set()
for name,configuration in examples.items():
    direct=exact_minimal_circuits(configuration)
    encoded=encoded_circuits(configuration)
    assert direct==encoded,(name,direct-encoded,encoded-direct)
    supported_direct=exact_minimal_circuits(configuration,True)
    supported_encoded=encoded_circuits(configuration,True)
    assert supported_direct==supported_encoded,(name,supported_direct-supported_encoded,supported_encoded-supported_direct)
    sizes={len(a)+len(b) for a,b in direct}
    support_sizes|=sizes
    print('PASS',name,'exact intersecting partitions',len(direct),'support sizes',sorted(sizes))
assert support_sizes=={2,3,4,5}
print('PASS symbolic physical metric identity; all emitted rational anchor/chord/bracket identities')
print('PASS det(G)=C*Q for both markings; C is the strict radial nearest-lift deficit')
print('PASS every emitted polynomial constraint has degree at most four')
print('PASS all 18 emitted polarized metric equations; rational physical residual identities')
print('PASS strict-neighbor support circuits and all mixed-face orientation signs')
print('PASS baseline assertions preserved; lower-support circuits agree with independent nullspace oracle')
print('PASS',metadata)
