"""Exact first-order certificate for the Type 5 sharp-ray one-edge deformation."""

from itertools import combinations, product

import sympy as sp
from sympy.polys.matrices import DomainMatrix

from .chart import cross


L = sp.Symbol("L")
ANCHORS = (1, 2, 5)
PLANAR = (0, 2, 3, 4, 5, 6, 7)
SPATIAL = (0, 3, 4, 6, 7)
# The intrinsic coordinates x0, y2 and x3 are fixed in the deformation.
FREE = [i for i in range(24) if i not in (0, 3, 4)]
QUARTETS = tuple(combinations(range(8), 4))

POSITIVE = ("0125", "0134", "0136", "0157", "0347", "1347", "1356", "2345", "2346", "3457")
NEGATIVE = ("0146", "0156", "0345", "1346", "1456", "2347", "3456")
OPENING_SIGNS = {tuple(map(int, q)): s for s, group in ((1, POSITIVE), (-1, NEGATIVE)) for q in group}


def point(x, y):
    return sp.Matrix([x, y])


def dot(u, v):
    return L*u[0]*v[0] + u[1]*v[1]


def planar_base():
    half = sp.Rational(1, 2)
    b, s = sp.Rational(9, 20), sp.Rational(1, 10)
    a, T = -(L+2)/8, (L+1)/4
    p = {0: point(s, (1-4*b)*s), 1: point(0, 0), 2: point(0, a),
         3: point(b, T-b), 4: point(-b, T-b), 5: point(-half, half-2*b),
         6: point(0, T), 7: point(-half, (25*L**2-44*L+16)/(4*(25*L-18)))}
    r = {i: p[i] for i in ANCHORS}
    r[0] = point(-s, (1-4*b)*s)
    r[3] = r[4] = p[3] - point(half, L/2)
    r[6] = p[6] - point(half, L/2)
    r[7] = (2*dot(p[7], p[5])/dot(p[5], p[5])*p[5] - p[7]).applyfunc(sp.factor)
    heights = {0: 0, 1: 0, 2: 0, 3: 1, 4: 1, 5: 0,
               6: sp.factor(cross(r[5], r[6])/cross(r[5], r[3])), 7: 3}
    return p, r, heights


def solve(matrix, rhs):
    """Solve over Q(L), then verify the resulting rational identities."""
    augmented = DomainMatrix.from_Matrix(matrix.row_join(rhs))
    integral = augmented.clear_denoms_rowwise(convert=True)[1]
    n = matrix.cols
    numerator, denominator = integral[:, :n].solve_den(integral[:, n:])
    result = (numerator.to_Matrix()/integral.domain.to_sympy(denominator)).applyfunc(sp.factor)
    assert (matrix*result-rhs).applyfunc(sp.cancel).is_zero_matrix
    return result


def planar_velocities(complex_, p, r, heights):
    def ray(i, j):
        m, n = complex_.shift[i, j]
        return p[j]-p[i] + point(m+sp.Rational(n, 2), n*L/2)

    areas = [cross(ray(i, j), ray(i, k)) for i, j, k in complex_.faces]
    assert len(areas) == 16 and len(complex_.disjoint) == 138
    assert {tuple(sorted(e)) for e in combinations(ANCHORS, 2)} <= complex_.edges
    assert all(tuple(sorted((i, j))) in complex_.edges for i in SPATIAL for j in ANCHORS)
    assert sum(7 not in e and not set(e) <= set(ANCHORS) for e in complex_.edges) == 16
    rows, rhs = [], []
    for i, j in sorted(complex_.edges):
        u, v = ray(i, j), r[j]-r[i]
        assert sp.cancel(dot(v, v)-dot(u, u)) == 0
        if i in ANCHORS and j in ANCHORS:
            assert complex_.shift[i, j] == (0, 0)
            continue
        row = [0]*24
        for k, orient in ((i, -1), (j, 1)):
            if k == 1:
                continue
            ip = 2*PLANAR.index(k)
            ir = 14+2*SPATIAL.index(k) if k in SPATIAL else ip
            row[ip] -= 2*orient*L*u[0]
            row[ip+1] -= 2*orient*u[1]
            row[ir] += 2*orient*L*v[0]
            row[ir+1] += 2*orient*v[1]
        rows.append(row)
        rhs.append([-L*(heights[i]-heights[j])**2, L*int((i, j) == (0, 1))])
    matrix = sp.Matrix(rows)[:, FREE]
    assert matrix.shape == (21, 21)
    domain_matrix = DomainMatrix.from_Matrix(matrix.applyfunc(sp.factor))
    determinant = sp.factor(domain_matrix.domain.to_sympy(domain_matrix.det()))
    solution = solve(matrix, sp.Matrix(rhs))
    # Column zero is the velocity at defect coefficient D=0. Column one multiplies D.
    full = sp.zeros(24, 2)
    for i, k in enumerate(FREE):
        full[k, :] = solution[i, :]
    return areas, determinant, full


def spatial_signs(r, heights, velocities):
    def lift(i):
        return r[i].col_join(sp.Matrix([heights[i]]))

    def velocity(i):
        result = sp.zeros(3, 5)
        if i != 1:
            k = 14+2*SPATIAL.index(i) if i in SPATIAL else 2*PLANAR.index(i)
            result[:2, :2] = velocities[k:k+2, :]
        # D and the height corrections at 0, 4 and 6 are the four unknowns.
        if i in (0, 4, 6):
            result[2, 2+(0, 4, 6).index(i)] = 1
        return result

    values, derivatives = {}, {}
    for q in QUARTETS:
        a, *others = q
        u = [lift(i)-lift(a) for i in others]
        values[q] = sp.factor(sp.Matrix.hstack(*u).det())
        if q in OPENING_SIGNS:
            assert values[q] == 0
            row = sp.zeros(1, 5)
            for k, i in enumerate(others):
                normal = u[(k+1) % 3].cross(u[(k+2) % 3])
                row += normal.T*(velocity(i)-velocity(a))
            derivatives[q] = (OPENING_SIGNS[q]*row).applyfunc(sp.factor)
    return values, derivatives


def nonvanishing(poly, lo, hi):
    polynomial = sp.Poly(poly, L)
    assert polynomial.eval(lo) != 0
    if polynomial.degree() > 0:
        assert polynomial.count_roots(lo, hi) == 0


def strict_sign(expr, lo, hi):
    numerator, denominator = sp.fraction(sp.cancel(expr))
    for p in (numerator, denominator):
        nonvanishing(p, lo, hi)
    return int(sp.sign(numerator.subs(L, lo)*denominator.subs(L, lo)))


def verify_area_obstruction(complex_, r, signs, derivatives):
    coefficient = -cross(r[5], r[7])/cross(r[2], r[5])
    expected = 2*(5*L-4)*(25*L+16)/(5*(L+2)*(25*L-18))
    assert sp.cancel(coefficient-expected) == 0 and strict_sign(expected, 3, sp.oo) > 0
    area_row = coefficient*derivatives[0, 1, 2, 5] + derivatives[0, 1, 5, 7]
    target = sp.Matrix([[-60*(L+2)/(75*L+14), -sp.Rational(27, 5), 0, 0, 0]])
    assert (area_row-target).applyfunc(sp.cancel).is_zero_matrix

    pairs = [((0, 4), (1, 5, 2)), ((1, 5), (0, 2, 4)), ((0, 2), (1, 7, 5))]
    assert set(pairs) <= set(complex_.disjoint)
    needed = {q for edge, face in pairs for q in combinations(sorted((*edge, *face)), 4)}
    unknown = sorted(q for q in needed if not signs[q])
    assert unknown == [(0, 1, 2, 5), (0, 1, 4, 5), (0, 1, 5, 7)]
    feasible = []
    for candidate in product((-1, 1), repeat=3):
        signed = signs | dict(zip(unknown, candidate, strict=True))
        for edge, face in pairs:
            q = tuple(sorted((*edge, *face)))
            circuit = [(-1)**k * (1 if v in edge else -1) * signed[q[:k]+q[k+1:]]
                       for k, v in enumerate(q)]
            if min(circuit) == max(circuit):
                break
        else:
            feasible.append(candidate)
    assert feasible and all(a == b == 1 for a, _, b in feasible)


def verify(complex_):
    p, r, heights = planar_base()
    areas, determinant, velocities = planar_velocities(complex_, p, r, heights)
    assert strict_sign(determinant, 3, sp.oo) == 1
    assert all(strict_sign(area, 3, sp.oo) == 1 for area in areas)
    # The base, its heights, and both velocity columns must specialize everywhere.
    for expr in [*velocities, *heights.values(), *(v for a in (*p.values(), *r.values()) for v in a)]:
        nonvanishing(sp.denom(sp.cancel(expr)), 3, sp.oo)
    values, derivatives = spatial_signs(r, heights, velocities)
    signs = {q: strict_sign(v, 3, sp.oo) if v != 0 else 0 for q, v in values.items()}
    assert sum(s != 0 for s in signs.values()) == 44
    verify_area_obstruction(complex_, r, signs, derivatives)
    positive_star = {(0, 3, 1), (0, 5, 3)}
    for f in complex_.faces:
        if 0 in f:
            a, b, c = f
            sign = strict_sign(cross(r[b]-r[a], r[c]-r[a]), 3, sp.oo)
            assert sign == (1 if f in positive_star else -1)
    signs.update(OPENING_SIGNS)
    for lo, hi, fifth in ((3, 6, "1356"), (6, sp.oo, "1347")):
        rows = [derivatives[tuple(map(int, q))] for q in ("0146", "0156", "2345", "2347", fifth)]
        equations = sp.Matrix.vstack(*rows)
        # Make these five signed derivatives equal to one common unknown margin.
        controls = solve(equations[:, 1:].row_join(-sp.ones(5, 1)), -equations[:, :1])
        for expr in controls:
            nonvanishing(sp.denom(expr), lo, hi)
        assert strict_sign(controls[0], lo, hi) == -1
        direction = sp.Matrix([1, *controls[:4]])
        assert all(strict_sign((row*direction)[0], lo, hi) == 1 for row in derivatives.values())
    for edge, face in complex_.disjoint:
        q = tuple(sorted((*edge, *face)))
        circuit = [(-1)**k * (1 if v in edge else -1) * signs[q[:k]+q[k+1:]]
                   for k, v in enumerate(q)]
        assert min(circuit) < 0 < max(circuit)
    print("Certified the sharp-ray one-edge deformation and all 138 separations.", flush=True)
