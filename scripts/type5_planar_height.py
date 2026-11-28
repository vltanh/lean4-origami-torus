"""Exact height obstruction on the three-parameter planar family of mask 11116."""

from itertools import combinations
import sympy as sp


PROJECTED_WORD = 0x93CFF3F81E4CE6
HEIGHT_SIGNS = (((0, 1, 3, 5), 1), ((0, 2, 3, 7), -1), ((1, 3, 4, 7), -1),
                ((1, 3, 5, 7), 1), ((2, 4, 5, 7), 1))


def verify_chart(faces, edges, shift):
    x, y, z, k = sp.symbols("x y z k")
    metric = sp.diag(1, 3)
    turn = sp.Matrix([[0, -3], [1, 0]])
    period = sp.Matrix([1, 1])/2

    def rotation(a, b):
        return ((b*a.T + (turn*b)*(turn*a).T/3)*metric/(a.T*metric*a)[0]).applyfunc(sp.factor)

    def area(points, i, j, k):
        v, w = points[j]-points[i], points[k]-points[i]
        if points is p:
            v += sp.Matrix(shift(i, j))
            w += sp.Matrix(shift(i, k))
        return sp.factor(v.row_join(w).det())

    def edge(i, j):
        v = p[j]-p[i]+sp.Matrix(shift(i, j))
        w = r[j]-r[i]
        return sp.factor((w.T*metric*w-v.T*metric*v)[0])

    p = {0: sp.Matrix([(1-y)/2, -(1+y)/6]), 1: sp.zeros(2, 1),
         2: sp.Matrix([(x-1)*y/2, (x-1)*(2-y)/6]), 3: sp.Matrix([x-3*k, k]),
         4: sp.Matrix([3, -1])*(x*y-x-y)/6, 5: sp.Matrix([(x*z-1)/2, -(x*z+1)/6])}
    r = dict(p)
    reflect = 2*p[2]*p[2].T*metric/(p[2].T*metric*p[2])[0]-sp.eye(2)
    r[0], r[3] = (reflect*p[0]).applyfunc(sp.factor), (reflect*p[3]).applyfunc(sp.factor)
    residual = edge(5, 3)
    assert sp.cancel(residual.diff(k)+6*(y*y+x*z)/(y*y-y+1)) == 0
    k_value = -residual.subs(k, 0)/residual.diff(k)
    p[3], r[3] = (v.subs(k, k_value).applyfunc(sp.factor) for v in (p[3], r[3]))

    # Face 136 rotates about 1. Face 237 rotates about 2 in its marked lift.
    rot = rotation(p[3], r[3])
    p[6] = ((sp.eye(2)-rot).inv()*period).applyfunc(sp.factor)
    r[6] = p[6]-period
    rot = rotation(p[3]-p[2]+sp.Matrix(shift(2, 3)), r[3]-r[2])
    p[7] = (p[2]+(sp.eye(2)-rot).inv()*rot*sp.Matrix(shift(2, 7))).applyfunc(sp.factor)
    r[7] = p[7]

    for i, j in edges:
        assert edge(i, j) == 0
    intrinsic = [area(p, *f) for f in faces]
    for i, f in enumerate(faces):
        assert sp.cancel(area(r, *f)-(1 if (11116 >> i) & 1 else -1)*intrinsic[i]) == 0
    projected = {t: area(r, *t) for t in combinations(range(8), 3)}
    by_face = dict(zip(faces, intrinsic))
    assert sp.cancel(by_face[2, 5, 6]-x*by_face[4, 6, 5]) == 0
    assert sp.cancel(by_face[0, 2, 4]-(1-y)*(x*x-x+1)/6) == 0
    assert sp.cancel(by_face[2, 7, 4]-(1-x-y)/6) == 0
    assert sp.cancel(projected[0, 4, 7]-x*(1-y)*(1-x-y)/6) == 0
    assert sp.cancel(projected[0, 5, 7]-x*(x*z+y*y)/6) == 0
    return (x, y, z), intrinsic, projected


def check_height_obstruction(faces, edges, shift):
    (x, y, z), intrinsic, projected = verify_chart(faces, edges, shift)
    factors, basis = {}, {}

    def parity(expr):
        # Bit zero records the constant sign. The others are the signs of
        # irreducible factors at generic real parameters.
        result = 0
        for part in sp.fraction(sp.factor(expr)):
            coefficient, powers = sp.factor_list(part)
            assert coefficient != 0
            result ^= int(bool(coefficient < 0))
            for factor, power in powers:
                if power % 2:
                    bit = factors.setdefault(factor, len(factors)+1)
                    result ^= 1 << bit
        return result

    def reduce_row(row):
        for pivot in sorted(basis, reverse=True):
            if (row >> pivot) & 1:
                row ^= basis[pivot]
        return row

    def impose(row):
        row = reduce_row(row)
        assert row != 1
        if row:
            basis[row.bit_length()-1] = row

    for a in intrinsic:
        impose(parity(a))
    for i, a in enumerate(projected.values()):
        impose(parity(a) ^ (1-((PROJECTED_WORD >> i) & 1)))

    # Every factor in these seven products is positive under the stipulated
    # planar signs. Their positive sum fixes the remaining cofactor sign.
    f = -x*y**2+x*y*z+2*x*y-x*z+y**2
    g = x*y*z-x*z**2-x*z-y*z-y+z
    h = -x*y+x*z+x+y
    products = [(3, [y, f]), (3, [z, x, x*x*z-x*y*y+2*x*y*z+x*y+y*y]),
                (1, [z, h, -x*y**3+x*y*y*z+x*y*y-x*y+x*z+y**3]),
                (1, [1-y, g, x*x*y*y-x*x*y*z-x*x*y-2*x*y*y+x*y*z+x*z+y*y]),
                (1, [1-y, g, f]), (1, [z-y, x*z+y*y, h]),
                (1, [-x*y*z+x*z+y, h, x*y*y-x*y*z-x*y-y*y-y+z])]
    for _, terms in products:
        assert all(reduce_row(parity(term)) == 0 for term in terms)
    impose(parity(sum(weight*sp.prod(terms) for weight, terms in products)))

    rows, denominators = [], []
    for q, sign in HEIGHT_SIGNS:
        entries = []
        for v in (0, 3, 4, 7):
            if v in q:
                face = tuple(i for i in q if i != v)
                entries.append(sign*(-1)**(q.index(v)+1)*projected[face])
            else:
                entries.append(sp.Integer(0))
        den = sp.lcm([sp.denom(a) for a in entries])
        denominators.append(den)
        rows.append([sp.cancel(den*a) for a in entries])

    matrix = sp.Matrix(rows)
    signed_minors, cofactor_signs = [], []
    for i, den in enumerate(denominators):
        # Up to one common multiplier these are the signed maximal minors
        # of the original five height forms.
        minor = matrix[[j for j in range(5) if j != i], :]
        cofactor = (-1)**i*minor.det(method="domain-ge")
        signed_minors.append(cofactor)
        cofactor_signs.append(parity(den*cofactor))
    assert all(sp.expand(entry) == 0 for entry in sp.Matrix([signed_minors])*matrix)
    assert all(reduce_row(cofactor_signs[0] ^ row) == 0 for row in cofactor_signs[1:])
