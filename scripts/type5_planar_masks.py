"""Check the projection and spatial orientation tests for the 62 archived masks.

Run with Python 3, SymPy and CaDiCaL (the Lean toolchain includes a compatible copy).
Each claimed exclusion is verified either by direct enumeration of crease signs
or by checking the individual reverse-unit-propagation steps of the solver proof.
"""
from fractions import Fraction
from itertools import combinations, product
from pathlib import Path
from tempfile import TemporaryDirectory
import shutil
import subprocess

FACES = [tuple(map(int, f)) for f in
         "012 031 024 053 045 152 136 164 147 175 263 237 274 256 357 465".split()]
FACE_SETS = {tuple(sorted(f)) for f in FACES}
VERTICES = tuple(range(8))
EDGES = sorted({e for f in FACES for e in combinations(sorted(f), 2)})
INCIDENT = {e: [i for i, f in enumerate(FACES) if set(e) <= set(f)] for e in EDGES}
assert all(len(s) == 2 for s in INCIDENT.values())
# (representative, orbit size) for the sharp marking ((-1,0),(-1,1)), copied
# from research/type5_completion/verify_saturated_routes.py at fe5a6eee0cf1.
LEDGER = [
    (2550, 6), (2553, 6), (2806, 6), (2809, 6), (3449, 6), (3501, 6), (3502, 6),
    (3513, 3), (3514, 6), (3763, 6), (3766, 6), (3769, 6), (3948, 6), (3953, 6),
    (3981, 6), (3993, 6), (4012, 6), (5779, 6), (5785, 6), (5806, 6), (5810, 6),
    (5817, 6), (5818, 6), (5881, 6), (6905, 3), (7854, 6), (7857, 6), (7858, 6),
    (7865, 6), (7866, 6), (10886, 3), (10887, 3), (10893, 6), (10918, 3), (10925, 6),
    (10950, 6), (10963, 6), (10966, 6), (10969, 6), (10982, 6), (10998, 6), (11001, 6),
    (11116, 6), (11124, 6), (11149, 6), (11161, 6), (11212, 6), (11213, 6), (11225, 6),
    (15065, 1), (15097, 1), (17777, 6), (17785, 6), (17841, 6), (17849, 6), (17905, 6),
    (19635, 6), (19889, 6), (21682, 2), (21683, 6), (21881, 6), (21945, 6),
]
SURVIVORS = {11149}


def literal(q):
    sorted_q = tuple(sorted(q))
    return VARIABLES[sorted_q] * (-1)**sum(a > b for a, b in combinations(q, 2))


VARIABLES = {q: i + 1 for i, q in enumerate((*combinations(VERTICES, 4), *combinations(VERTICES, 3)))}
assert len(VARIABLES) == 126


def both_signs(row):
    return [row, [-q for q in row]]


def grassmann_pluecker(row):
    # For determinants in uniform position, the three signed products cannot
    # all have the same sign, since their sum is zero.
    for assignment in product((-1, 1), repeat=6):
        u, v, w = (assignment[j] * assignment[j+1] for j in (0, 2, 4))
        if u == v == w:
            yield [-a * b for a, b in zip(row, assignment)]


def common_clauses():
    clauses = [[1]]  # Reverse all heights if necessary.
    for p in [*combinations(VERTICES, 2), *combinations(VERTICES, 1)]:
        for a, b, c, d in combinations(sorted(set(VERTICES) - set(p)), 4):
            row = [literal((*p, a, b)), literal((*p, c, d)), -literal((*p, a, c)),
                   literal((*p, b, d)), literal((*p, a, d)), literal((*p, b, c))]
            clauses.extend(grassmann_pluecker(row))
    for a, b in combinations(VERTICES, 2):
        for c, d, e in combinations(sorted(set(VERTICES) - {a, b}), 3):
            # The ninth homogeneous vector is the vertical point at infinity.
            row = [literal((a, b, c, d)), literal((a, b, e)), -literal((a, b, c, e)),
                   literal((a, b, d)), literal((a, b, c)), literal((a, b, d, e))]
            clauses.extend(grassmann_pluecker(row))
    for length in (4, 5):
        for q in combinations(VERTICES, length):
            coefficients = [(-1)**i * literal(q[:i] + q[i + 1:]) for i in range(length)]
            clauses.extend(both_signs(coefficients))
            if length == 5:
                for edge in combinations(q, 2):
                    face = tuple(v for v in q if v not in edge)
                    if edge in EDGES and face in FACE_SETS:
                        clauses.extend(both_signs([b * (1 if v in edge else -1)
                                                   for v, b in zip(q, coefficients)]))
            # Each vertex is strictly supported among its spatial AND projected
            # neighbors after the simultaneous planar perturbation in the proof.
            for a in q:
                if all(tuple(sorted((a, b))) in EDGES for b in q if a != b):
                    clauses.extend(both_signs([c * (1 if b == a else -1)
                                               for b, c in zip(q, coefficients)]))
    return clauses


def creases(mask):
    return [e for e, (i, j) in INCIDENT.items() if ((mask >> i) ^ (mask >> j)) & 1]


def hinge(edge):
    v, w = edge
    edge = tuple(sorted(edge))
    prev = next(a for i in INCIDENT[edge] for a in FACES[i]
                if a not in edge and (FACES[i].index(v) - FACES[i].index(w)) % 3 == 1)
    nxt = next(a for i in INCIDENT[edge] for a in FACES[i]
               if a not in edge and (FACES[i].index(w) - FACES[i].index(v)) % 3 == 1)
    return literal((v, w, prev, nxt))


def maekawa_possible(mask):
    folds = creases(mask)
    stars = sorted(([i for i, e in enumerate(folds) if v in e] for v in VERTICES), key=len)

    def extend(k, known):
        if k == len(stars):
            return True
        ids = [i for i in stars[k] if i not in known]
        subtotal = sum(known.get(i, 0) for i in stars[k])
        for signs in product((-1, 1), repeat=len(ids)):
            if abs(subtotal + sum(signs)) == 2 and extend(k + 1, {**known, **dict(zip(ids, signs))}):
                return True
        return False
    return extend(0, {})


# Nonzero shifts on ascending edges of the pinned sharp marking.
SHIFTS = {
    (1, 4): (-1, 0), (1, 5): (-1, 1), (2, 3): (0, 1), (2, 5): (-1, 1),
    (2, 6): (0, 1), (2, 7): (1, 0), (3, 7): (1, -1), (4, 6): (1, 0),
    (4, 7): (1, 0), (5, 6): (1, 0), (5, 7): (1, -1),
}


def shift(i, j):
    x, y = SHIFTS.get(tuple(sorted((i, j))), (0, 0))
    return (x, y) if i < j else (-x, -y)


def period(a, b, c):
    return tuple(map(sum, zip(shift(a, b), shift(b, c), shift(c, a))))


def component_lifts(mask):
    """Relative shifts developed by each edge-connected island of one sign."""
    shifts = {}
    pending = set(range(len(FACES)))
    while pending:
        stack = [pending.pop()]
        offsets = {}
        while stack:
            index = stack.pop()
            face = FACES[index]
            # A new island starts at arbitrary offset. Every later face
            # shares an edge with one whose offsets have already been assigned.
            origin = next((v for v in face if v in offsets), face[0])
            offsets.setdefault(origin, (0, 0))
            for v in face:
                value = tuple(map(sum, zip(offsets[origin], shift(origin, v))))
                assert offsets.setdefault(v, value) == value
            for edge in combinations(sorted(face), 2):
                for other in INCIDENT[edge]:
                    if other in pending and ((mask >> index) ^ (mask >> other)) & 1 == 0:
                        pending.remove(other)
                        stack.append(other)
        for a, b in combinations(sorted(offsets), 2):
            lift = tuple(j-i for i, j in zip(offsets[a], offsets[b]))
            shifts.setdefault((a, b), set()).add(lift)
    return shifts


def check_equal_radii(mask, targets):
    """Reduce the specified affine forms against the equal squared radii of developed pairs."""
    # Unknowns are p1x,p1y,...,p7x,p7y,1; p0=0. The norm is x²+xy+y².
    def norm(x, y):
        return x*x + x*y + y*y

    def residual(row, basis):
        for pivot in sorted(basis):
            multiple = row[pivot]
            if multiple:
                row = [x - multiple*y for x, y in zip(row, basis[pivot])]
        return row

    basis = {}
    for (a, b), shifts in component_lifts(mask).items():
        for (kx, ky), (lx, ly) in combinations(sorted(shifts), 2):
            dx, dy = kx-lx, ky-ly
            row = [Fraction(0)]*15
            for vertex, sign in ((a, -1), (b, 1)):
                if vertex != 0:
                    row[2*vertex-2] += sign*(2*dx+dy)
                    row[2*vertex-1] += sign*(dx+2*dy)
            row[-1] += norm(kx, ky)-norm(lx, ly)
            row = residual(row, basis)
            if any(row):
                pivot = next(i for i, x in enumerate(row) if x)
                basis[pivot] = [x/row[pivot] for x in row]

    for row in targets:
        assert len(row) == 15 and not any(residual(row, basis))


def check_affine_consequences(mask, differences):
    origin = differences([Fraction(0)]*14)
    columns = [differences([Fraction(i == j) for i in range(14)]) for j in range(14)]
    check_equal_radii(mask, [[col[i]-v for col in columns]+[v] for i, v in enumerate(origin)])


def check_triangle_346():
    """For mask 11124 the projected triangle 346 has orientation opposite to 152."""
    def coordinates(a, b, t):
        # Three times the intrinsic coordinates, translated to put vertex 1 at zero.
        p = {1: (0, 0), 2: (a, a), 3: (a+1-6*t, a+3*t-2),
             4: (2*a+1, 1-a), 5: (2, -1), 6: (2*b-1, -b-1)}
        # Match the marked anchor face by a plane isometry.
        r = {1: (0, 0), 2: p[2], 5: (-1, 2), 3: p[3][::-1],
             4: (2*a-2, 1-a), 6: (2*b-1, 2-b)}
        return p, r

    def differences(row):
        # Express the claimed parametrization as affine equations on the 14 unknowns.
        p = {i: (3*(row[2*i-2]-row[0]), 3*(row[2*i-1]-row[1])) for i in range(1, 7)}
        a = p[2][0]
        b = (p[6][0]+1)/2
        t = (a+1-p[3][0])/6
        expected, _ = coordinates(a, b, t)
        return [q-e for i in p for q, e in zip(p[i], expected[i])]

    check_affine_consequences(11124, differences)

    def displacement(points, i, j, marked):
        m, n = shift(i, j) if marked else (0, 0)
        return points[j][0]-points[i][0]+3*m, points[j][1]-points[i][1]+3*n

    def length(points, i, j, marked):
        x, y = displacement(points, i, j, marked)
        return x*x+x*y+y*y

    def area(points, face, marked):
        i, j, k = face
        x, y = displacement(points, i, j, marked)
        z, w = displacement(points, i, k, marked)
        return x*w-y*z

    # Every identity has degree at most two in each of a,b,t. Evaluation at
    # three distinct values of each variable proves the polynomial identity.
    for a, b, t in product(range(3), repeat=3):
        p, r = coordinates(a, b, t)
        for i in (1, 2, 5):
            for j in (1, 2, 3, 4, 5, 6):
                assert length(p, i, j, True) == length(r, i, j, False)
        assert length(r, 3, 6, False)-length(p, 3, 6, True) == 9*(3*t-a+b*(1-3*t))
        for face, expected in [((1, 5, 2), a), ((1, 6, 4), 1-a), ((4, 6, 5), b),
                               ((1, 3, 6), 1-3*t-(1-a)*b)]:
            assert -area(p, face, True) == 3*expected
        assert area(r, (1, 5, 2), False) == -3*a
        assert area(r, (3, 4, 6), False) == 3*(3*t-a)*(a-b-1)


def aligned_basis(u, v):
    # (x,y) represents the Euclidean point (x,sqrt(3)*y).
    return (u-v)*Fraction(1, 2), -(u+v)*Fraction(1, 2)


def aligned_points(row):
    old = [(0, 0), *zip(row[::2], row[1::2])]
    p = {}
    for i, (x, y) in enumerate(old):
        m, n = shift(1, i)
        p[i] = aligned_basis(x+m-old[1][0], y+n-old[1][1])
    return p


def aligned_shift(i, j):
    u, v = shift(i, j)
    a, b = shift(1, i)
    c, d = shift(1, j)
    return aligned_basis(u+a-c, v+b-d)


def check_triangle_067():
    """For mask 3981 the marked edge 27 fixes the projected sign of 067."""
    half = Fraction(1, 2)

    def coordinates(b, d, t, y):
        return {0: (half, t), 1: (0, 0), 2: (0, b), 4: (0, Fraction(1, 3)),
                5: (-3*d, d), 6: ((1-6*t)/4, (1+2*t)/4), 7: (-(6*t+1)/4, y)}

    def differences(row):
        p = aligned_points(row)
        expected = coordinates(p[2][1], p[5][1], p[0][1], p[7][1])
        return [actual-want for i in expected for actual, want in zip(p[i], expected[i])]

    check_affine_consequences(3981, differences)

    def displacement(points, i, j, marked):
        m, n = aligned_shift(i, j) if marked else (0, 0)
        return points[j][0]-points[i][0]+m, points[j][1]-points[i][1]+n

    def length(points, i, j, marked):
        x, y = displacement(points, i, j, marked)
        return x*x+3*y*y

    def area(points, i, j, k, marked):
        x, y = displacement(points, i, j, marked)
        u, v = displacement(points, i, k, marked)
        return x*v-y*u

    # All coordinates are affine. The final identity has degree at most
    # three in b (067 is independent of b), and at most two in each other variable.
    grid = tuple(map(Fraction, range(3)))
    for b, d, t, y in product(map(Fraction, range(4)), grid, grid, grid):
        p = coordinates(b, d, t, y)
        r = dict(p)
        r[0] = p[0][0]-1, t
        for i in (4, 6):
            r[i] = p[i][0]-half, p[i][1]-half
        x, y = p[7]
        r[7] = (x-3*y)*half, -(x+y)*half
        for i in (0, 4, 6):
            for a in (1, 2, 5):
                assert length(p, a, i, True) == length(r, a, i, False)
        # The mask puts face 175 on the reflected side after aligning 152.
        # Its distances to the two ends of edge 15 select the reflected point.
        for a in (1, 5):
            assert length(p, a, 7, True) == length(r, a, 7, False)
        assert area(r, 1, 7, 5, False) == -area(p, 1, 7, 5, True)
        assert -area(r, 0, 6, 7, False) == (2*t+4*y-1)/8
        assert area(p, 2, 7, 4, True) == (36*b*t+6*b+6*t-12*y+5)/24
        assert area(p, 0, 1, 2, True) == -b/2
        assert area(r, 1, 5, 2, False) == area(p, 1, 5, 2, True)
        diff = length(r, 2, 7, False)-length(p, 2, 7, True)
        assert diff == 3*(-6*b*t+12*b*y-5*b+2*t+4*y-1)/4
        assert (9*b*b+3*b+1)*(-area(r, 0, 6, 7, False)) == (
            3*b*area(p, 2, 7, 4, True)+(3*b+1)*diff/6)


def check_turns_3501():
    """Verify the metric identities excluding the joint turns [034] <= 0 <= [347]."""
    import sympy as sp

    half = Fraction(1, 2)

    def coordinates(b, c, d, h, k, x, y):
        return {0: (c+half, h), 1: (0, 0), 2: (c, b), 3: (half, k),
                4: (c, (c+1)/3), 5: (c, d), 6: (x+half, (x-c+1)/3+h), 7: (x, y)}

    def differences(row):
        p = aligned_points(row)
        predicted = coordinates(p[2][1], *p[5], p[0][1], p[3][1], *p[7])
        return [actual-want for i in predicted for actual, want in zip(p[i], predicted[i])]

    check_affine_consequences(3501, differences)
    b, c, d, h, k, x, y = sp.symbols("b c d h k x y")
    p = {i: sp.Matrix(pt) for i, pt in coordinates(b, c, d, h, k, x, y).items()}
    norm = c*c+3*d*d
    metric = sp.diag(1, 3)
    reflect = 2*p[5]*p[5].T*metric/norm-sp.eye(2)
    r = dict(p)
    r[3] = reflect*(p[3]-sp.Matrix([1, 0]))
    r[4] = p[4]+sp.Matrix([half, -half])
    r[6] = sp.Matrix([2*c-x, p[6][1]-half])
    r[7] = reflect*p[7]

    def displacement(points, i, j):
        delta = points[j]-points[i]
        return delta+sp.Matrix(aligned_shift(i, j)) if points is p else delta

    def residual(i, j):
        u, v = displacement(p, i, j), displacement(r, i, j)
        return sp.factor((v.T*metric*v-u.T*metric*u)[0])

    def area(points, i, j, k):
        return sp.factor(displacement(points, i, j).row_join(displacement(points, i, k)).det())

    def equal(lhs, rhs):
        assert sp.cancel(lhs-rhs) == 0

    # Shortestness constrains the displayed marked vectors to the closed Voronoi cell.
    equal(area(p, 1, 5, 2), c*(b-d))
    generic = {i: sp.Matrix(sp.symbols(f"x{i} y{i}")) for i in VERTICES}
    total_area = 0
    for start, second, third in FACES:
        a = generic[second]-generic[start]+sp.Matrix(aligned_shift(start, second))
        z = generic[third]-generic[start]+sp.Matrix(aligned_shift(start, third))
        total_area += a.row_join(z).det()
    equal(total_area, 1)
    assert displacement(p, 5, 4) == sp.Matrix([-half, (c-3*d)/3-Fraction(1, 6)])
    v = c-3*d
    lower = 3*(b-d)+1
    edge16, edge23, edge27 = residual(1, 6), residual(2, 3), residual(2, 7)
    # Exceptional perpendicular bisector v=0.
    equal(edge23.subs(c, 3*d), (6*k-1)*lower/2)
    equal(edge27.subs(c, 3*d), -(x-3*y+1)*lower)
    equal(residual(0, 3).subs({c: 3*d, k: sp.Rational(1, 6)}), (6*h+6*d+1)/2)
    equal(edge16.subs({c: 3*d, h: -d-sp.Rational(1, 6)}), -2*(6*d+1)*(x-3*d))
    # In the other case the four scalar pivot equations determine k, y, x and h.
    L, M = 4*c*c+v, 4*c*d+c+d
    D, E = 6*b*c-2*c*c+c+3*d, 4*(b-d)*c*c+norm
    equal(edge23.diff(k), 3*E/norm)
    equal(residual(4, 7), v*(L*y-M*x)/norm)
    equal(edge27.subs(y, M*x/L), (2*D*x-(3*b-c+1)*L)/L)
    equal(edge16.diff(h), -3)
    sx = (3*b-c+1)*L/(2*D)
    subs = {x: sx, y: M*sx/L, k: -edge23.subs(k, 0)*norm/(3*E),
            h: edge16.subs({h: 0, x: sx})/3}
    f = 4*b*c*c+b*c-3*b*d-4*c*c*d+c*c+c*d+c-d
    g = f+3*(b-d)*(c-d)
    equal((6*D*area(p, 2, 7, 4)).subs(subs), -v*(9*b*b-6*b*c+3*b+c*c-c+1))
    equal((E*area(r, 0, 3, 4)-2*c*g*area(p, 0, 2, 4)).subs(subs), 0)
    equal((norm*lower*area(r, 3, 4, 7)+v*f*area(p, 3, 5, 7)).subs(subs), 0)
    u, v = sp.symbols("u v")
    transform = {c: -u, d: (-u-v)/3}
    gu = g.subs(transform, simultaneous=True)
    boundary = -(2*u*u+2*u+v)/(6*u)
    equal(D.subs(transform, simultaneous=True), -6*u*(b-boundary))
    equal(gu.subs(b, (-u-v)/3), (2*u-v)*(2*u+v-1)/3)
    equal(gu.subs(b, boundary), -v*(1-u)*(4*u*u+v)/(3*u))
    assert sp.degree(gu, b) == 1


def check_turns_21683():
    """Check the signed area identities on a dense chart of mask 21683."""
    import sympy as sp

    half, third = Fraction(1, 2), Fraction(1, 3)

    def core(a, b, c, d, h):
        u = a-c
        return {0: (c+half, h), 1: (0, 0), 2: (a, b), 3: (c+half, u/3+b+half*third),
                4: (a, d+(1-u)/3), 5: (c, d)}

    def differences(row):
        p = aligned_points(row)
        predicted = core(*p[2], *p[5], p[0][1])
        return [q-v for i in predicted for q, v in zip(p[i], predicted[i])]

    check_affine_consequences(21683, differences)
    a, b, c, d, h, x, y = sp.symbols("a b c d h x y")
    p = {i: sp.Matrix(v) for i, v in core(a, b, c, d, h).items()}
    metric = sp.diag(1, 3)

    def reflection(v):
        return 2*v*v.T*metric/(v.T*metric*v)[0]-sp.eye(2)

    def edge(i, j):
        v = p[j]-p[i]+sp.Matrix(aligned_shift(i, j))
        w = r[j]-r[i]
        return sp.factor((w.T*metric*w-v.T*metric*v)[0])

    def area(points, i, j, k):
        v, w = points[j]-points[i], points[k]-points[i]
        if points is p:
            v += sp.Matrix(aligned_shift(i, j))
            w += sp.Matrix(aligned_shift(i, k))
        return sp.factor(v.row_join(w).det())

    def equal(lhs, rhs):
        assert sp.cancel(lhs-rhs) == 0

    r = dict(p)
    r[4] = reflection(p[5])*p[4]
    n = c*c+3*d*d
    u0, s0 = a-c, c+3*d
    H = 2*s0*(h-d)+c-d
    J, K = (4*u0-1)*c+3*d, (4*u0-1)*d-c
    equal(J*J+3*K*K, ((4*u0-1)**2+3)*n)
    equal(2*n*edge(0, 4), -J*H)
    equal(4*n*(area(r, 0, 4, 5)-area(p, 0, 4, 5)), K*H)
    s, t, u = sp.symbols("s t u")
    D, T, U = 4*t*u-2*t+1, 4*t*t-2*t+1, 4*u*u-2*u+1
    change = {a: s*t+u, c: s*t, d: s*(1-t)/3, h: s*(1-t)/3+(1-4*t)/6}
    equal(area(p, 0, 4, 5).subs(change, simultaneous=True), D/6)
    eq24 = sp.factor(edge(2, 4).subs(change, simultaneous=True))
    equal(eq24.diff(b), -3*D/T)
    change[b] = sp.factor(eq24.subs(b, 0)*T/(3*D))
    p = {i: v.subs(change, simultaneous=True).applyfunc(sp.factor) for i, v in p.items()}
    r = {i: v.subs(change, simultaneous=True).applyfunc(sp.factor) for i, v in r.items()}

    # Each pair gives a linear system because the displayed reflection has
    # already matched the quadratic parts of the corresponding norm equations.
    for j, pair in ((6, (1, 3)), (7, (2, 3))):
        p[j] = sp.Matrix([x, y])
        if j == 6:
            r[j] = p[5]+reflection(p[2]-p[5])*(p[j]-sp.Matrix([half, half])-p[5])
        else:
            r[j] = reflection(p[5])*p[j]
        matrix, rhs = sp.linear_eq_to_matrix([edge(i, j) for i in pair], (x, y))
        determinant = sp.factor(matrix.det())
        assert determinant != 0
        intrinsic = (matrix.adjugate()*rhs/determinant).applyfunc(sp.factor)
        r[j] = r[j].subs({x: intrinsic[0], y: intrinsic[1]}).applyfunc(sp.factor)
        p[j] = intrinsic

    for i, j in EDGES:
        equal(edge(i, j), 0)
    for index, face in enumerate(FACES):
        orientation = 1 if (21683 >> index) & 1 else -1
        equal(area(r, *face), orientation*area(p, *face))

    F, P = 4*t*u-4*t+2*u+1, s*T+U
    C = (1-2*t)**2+4*t*u*(1-2*u)
    equal(area(p, 1, 7, 5), -s*T/6)
    equal(area(p, 1, 5, 2), -s*u*T/(3*D))
    equal(area(p, 2, 3, 7), -t*(2*t-1)*U/(3*D))
    equal(u*T*area(p, 2, 6, 3), (t-u)*D*area(p, 2, 5, 6))
    equal(area(r, 2, 6, 7), (2*t-1)*area(p, 2, 5, 6))
    equal(T*area(r, 0, 3, 4), -(2*t-1)*F*area(p, 0, 5, 3))
    equal(T*area(r, 3, 4, 7), 2*t*F*area(p, 2, 7, 4))
    equal(6*T*D*area(r, 1, 3, 4), -(2*t-1)*F*P)
    equal(D*P**2*area(r, 3, 4, 6), 2*(t-u)*U*C*area(r, 1, 3, 4))


def height_clauses_11116():
    if __package__:
        from .type5_planar_height import PROJECTED_WORD, HEIGHT_SIGNS, check_height_obstruction
    else:
        from type5_planar_height import PROJECTED_WORD, HEIGHT_SIGNS, check_height_obstruction
    import sympy as sp

    def differences(row):
        p = aligned_points(row)
        a, b = p[2]
        d, h, k, j, l = (p[i][1] for i in (5, 0, 3, 6, 7))
        expected = {0: (3*h+1, h), 3: (a+3*b-3*k+1, k),
                    4: ((a-3*b-1)/2, -(a-3*b-1)/6), 5: (-3*d-1, d),
                    6: (1-3*j, j), 7: (a-3*b+3*l-1, l)}
        return [q-v for i in expected for q, v in zip(p[i], expected[i])]

    check_affine_consequences(11116, differences)
    a, b, h, d = sp.symbols("a b h d")
    metric = sp.diag(1, 3)
    B = sp.Matrix([1, 1])/2
    p0, p2, p5 = sp.Matrix([3*h+1, h]), sp.Matrix([a, b]), sp.Matrix([-3*d-1, d])
    normal_reflection = sp.eye(2)-2*B*B.T*metric
    anchor_reflection = 2*p2*p2.T*metric/(a*a+3*b*b)-sp.eye(2)
    assert (normal_reflection*(p5+B)-p5).applyfunc(sp.expand) == sp.zeros(2, 1)
    error = anchor_reflection*p0-normal_reflection*(p0+sp.Matrix([-1, 1])/2)
    w = a+3*b
    assert sp.cancel(2*(a*a+3*b*b)*error[1]-w*(2*w*h+a+b)) == 0
    assert (anchor_reflection.subs(a, -3*b)-normal_reflection).applyfunc(sp.cancel) == sp.zeros(2)
    check_height_obstruction(FACES, EDGES, aligned_shift)
    yield [literal((0, 4, 7))]
    yield [literal((0, 5, 7))]
    planar = [literal(t)*(1 if (PROJECTED_WORD >> i) & 1 else -1)
              for i, t in enumerate(combinations(VERTICES, 3))]
    spatial = [sign*literal(q) for q, sign in HEIGHT_SIGNS]
    for orientation in (1, -1):
        yield [-lit for lit in planar]+[-orientation*lit for lit in spatial]


def coincident_leaf_clauses(mask, strict):
    # p7x+1=0, p2x+2*p2y-p7y=0, p5x+2*p5y-p7y+1=0.
    targets = ({12: 1, 14: 1}, {2: 1, 3: 2, 13: -1}, {8: 1, 9: 2, 13: -1, 14: 1})
    check_equal_radii(mask, [[Fraction(target.get(i, 0)) for i in range(15)] for target in targets])
    assert shift(0, 2) == shift(0, 5) == (0, 0)
    assert shift(2, 7) == (1, 0) and shift(5, 7) == (1, -1)
    # Equal distances to vertices 2 and 5 and the same strictly signed side
    # of their line force the exact projections of 0 and 7 to coincide.
    sides = [literal((2, 5, v)) for v in (0, 7)]
    assert all(q in strict for q in sides) or all(-q in strict for q in sides)

    common_sign = []
    for a, b in combinations(sorted(set(VERTICES)-{0, 7}), 2):
        x, y = literal((0, a, b)), literal((7, a, b))
        for sign in (-1, 1):
            if sign*x in strict or sign*y in strict:
                yield [sign*x]
                yield [sign*y]
                common_sign.append(sign*literal((0, 7, a, b)))
    # Each oriented volume is the vertical separation 07 times the
    # oriented projected area 0ab, up to one common sign convention.
    for other in common_sign[1:]:
        first = common_sign[0]
        yield [-first, other]
        yield [first, -other]


def mask_clauses(mask):
    folds = creases(mask)
    strict = set()
    betweens = set()
    for v in VERTICES:
        succ, direction = {}, {}
        for i, f in enumerate(FACES):
            if v not in f:
                continue
            j = f.index(v)
            a, b = f[(j + 1) % 3], f[(j + 2) % 3]
            succ[a] = b
            direction[a] = 1 if (mask >> i) & 1 else -1
        extremes = {succ[a] for a in succ if direction[a] != direction[succ[a]]}
        assert len(extremes) >= 2
        for a in succ:
            b = succ[a]
            while b != a:
                if len(extremes) == 2 and {a, b} == extremes:
                    betweens.add((a, v, b))
                else:
                    strict.add(direction[a] * literal((v, a, b)))
                if direction[b] != direction[a]:
                    break
                b = succ[b]
        incident = [hinge(e) for e in folds if v in e]
        for signs in product((-1, 1), repeat=len(incident)):
            if abs(sum(signs)) != 2:
                yield [-a * b for a, b in zip(incident, signs)]
    while True:
        old = strict.copy()
        for a, v, b in betweens:
            for w in set(VERTICES) - {a, v, b}:
                row = [literal((a, v, w)), literal((v, b, w)), literal((a, b, w))]
                for sign in (-1, 1):
                    signed = {sign * i for i in row}
                    if strict & signed:
                        strict.update(signed)
        if strict == old:
            break
    for k in sorted(strict):
        yield [k]
    if mask in (3948, 4012):
        yield from coincident_leaf_clauses(mask, strict)
    if mask == 3501:
        check_turns_3501()
        assert literal((1, 5, 2)) in strict
        yield [literal((0, 3, 4)), -literal((3, 4, 7))]
    if mask == 3981:
        check_triangle_067()
        assert -literal((1, 5, 2)) in strict and literal((1, 7, 5)) in strict
        yield [-literal((0, 6, 7))]
    if mask == 11116:
        yield from height_clauses_11116()
    if mask == 21683:
        check_turns_21683()
        assert literal((4, 5, 7)) in strict and -literal((1, 3, 6)) in strict
        yield [-literal((2, 6, 7))]
        for first, second in [((0, 3, 4), (3, 4, 7)), ((1, 3, 4), (3, 4, 6))]:
            left, right = literal(first), literal(second)
            yield [-left, right]
            yield [left, -right]
    if mask == 11124:
        check_triangle_346()
        assert literal((1, 5, 2)) in strict
        yield [-literal((3, 4, 6))]


def check_rup(clauses, path):
    db = {i + 1: tuple(row) for i, row in enumerate(clauses)}
    previous = len(clauses)
    with path.open() as proof:
        for line in proof:
            pieces = line.split()
            if pieces[1] == "d":
                continue
            data = list(map(int, pieces))
            clause_id = data[0]
            cut = data.index(0)
            new, hints = data[1:cut], data[cut + 1:-1]
            assert clause_id > previous and data[-1] == 0 and hints and min(hints) > 0
            previous = clause_id
            assumed = {-literal for literal in new}
            for hint in hints:
                old = db[hint]
                assert not any(l in assumed for l in old)
                unset = [l for l in old if -l not in assumed]
                if not unset:
                    break
                assert len(unset) == 1
                assumed.add(unset[0])
            else:
                raise AssertionError("no unit-propagation conflict")
            if not new:
                return
            db[clause_id] = tuple(new)
    raise AssertionError("no empty clause")


def main():
    solver = shutil.which("cadical") or str(Path(subprocess.check_output(
        ["lean", "--print-prefix"], text=True).strip()) / "bin" / "cadical")
    if not __debug__:
        raise SystemExit("Run without Python optimization so proof checks remain active.")
    assert len(LEDGER) == 62 and sum(n for _, n in LEDGER) == 343
    assert all(hinge((v, w)) == hinge((w, v)) for v, w in EDGES)
    assert all(period(*face) == (0, 0) for face in FACES)
    assert (period(0, 1, 4), period(0, 1, 5)) == ((-1, 0), (-1, 1))
    common = common_clauses()
    excluded_m, excluded_g, survivors = [], [], []
    with TemporaryDirectory() as folder:
        for mask, size in LEDGER:
            if not maekawa_possible(mask):
                excluded_m.append((mask, size))
                continue
            clauses = common + list(mask_clauses(mask))
            cnf = Path(folder) / "mask.cnf"
            proof = Path(folder) / "mask.lrat"
            with cnf.open("w") as out:
                print("p cnf", 126, len(clauses), file=out)
                for row in clauses:
                    print(*row, 0, file=out)
            res = subprocess.run([solver, "--quiet", "--lrat", "--no-binary", str(cnf), str(proof)],
                                 stdout=subprocess.PIPE, text=True)
            if res.returncode == 20:
                check_rup(clauses, proof)
                excluded_g.append((mask, size))
            else:
                assert res.returncode == 10
                assignment = {int(w) for line in res.stdout.splitlines() if line.startswith("v ")
                              for w in line.split()[1:] if int(w)}
                assert {abs(lit) for lit in assignment} == set(VARIABLES.values())
                assert not any(-lit in assignment for lit in assignment)
                assert all(any(lit in assignment for lit in row) for row in clauses)
                survivors.append((mask, size))
    assert {m for m, s in survivors} == SURVIVORS
    assert [(len(group), sum(s for m, s in group)) for group in
            (excluded_m, excluded_g, survivors)] == [(22, 114), (39, 223), (1, 6)]
    print("Checked 22 Maekawa exclusions, 39 RUP refutations and one surviving Boolean model.")
    print("Surviving representatives:", sorted(SURVIVORS))


if __name__ == "__main__":
    main()
