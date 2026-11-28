"""Exact hexagonal Type 5 reconstruction in the two face planes meeting at edge 16."""

from functools import lru_cache
from itertools import combinations, permutations
import json
from pathlib import Path

from flint import fmpq as Q, fmpq_mat

from .chart import add, cross, scale, subtract, volume

# The physical point (x,sqrt(3)*y,z) is stored as (x,y,z).
B = (Q(1, 2), Q(1, 2))
HINGE_LEAVES = (0, 7)


def inner(u, v):
    result = u[0]*v[0]+3*u[1]*v[1]
    return result if len(u) == 2 else result+u[2]*v[2]


def turn(u):
    return -3*u[1], u[0]


def circle(t):
    den = 1+3*t*t
    return (1-3*t*t)/den, 2*t/den


def period(complex_, i, j):
    m, n = complex_.shift[i, j]
    return m+Q(n, 2), Q(n, 2)


def core(complex_, parameters):
    """Six rational intrinsic and spatial points from eight rational parameters."""
    length, heading, u, v, angle3, angle4, side2, side5 = map(Q, parameters)
    e = circle(heading)
    den = 1+3*u*u+v*v
    w = ((2-den)/den, 2*u/den, 2*v/den)
    bisector = add((1, 0, 0), w)

    def rotate(q):
        return subtract(scale(2*inner(q, bisector)/inner(bisector, bisector), bisector), q)

    axis_y, axis_z = rotate((0, 1, 0)), rotate((0, 0, 1))
    p = {1: (0, 0), 6: scale(length, e)}
    r = {1: (0, 0, 0), 6: scale(length, w)}
    normal = add(B, scale(length, subtract(w[:2], e)))
    offset = length*inner(B, e)-Q(1, 2)
    for j, side in ((2, side2), (5, side5)):
        p[j] = add(scale(offset/inner(normal, normal), normal), scale(side, turn(normal)))
        r[j] = (*p[j], 0)

    f = turn(e)
    for i, t in ((3, angle3), (4, angle4)):
        a, b = circle(t)
        n = add(scale(a, axis_y), scale(3*b, axis_z))
        rows, rhs = [], []
        for j in (2, 5):
            s = subtract(p[j], period(complex_, j, i))
            rows.append((inner(r[j], w)-inner(s, e), inner(r[j], n)-inner(s, f)))
            rhs.append((inner(r[j], r[j])-inner(s, s))/2)
        determinant = cross(*rows)
        h = (rhs[0]*rows[1][1]-rows[0][1]*rhs[1])/determinant
        k = (rows[0][0]*rhs[1]-rhs[0]*rows[1][0])/determinant
        p[i], r[i] = add(scale(h, e), scale(k, f)), add(scale(h, w), scale(k, n))
    return p, r


def leaf_pencil(complex_, p, r, j):
    """Return the center, direction and rational squared radical for one leaf."""
    rows = []
    for i in (2, 5, 3, 4):
        s = subtract(p[i], period(complex_, i, j))
        rows.append([r[i][0], 3*r[i][1], r[i][2], -s[0], -3*s[1],
                     (inner(r[i], r[i])-inner(s, s))/2])
    matrix, rank = fmpq_mat(rows).rref()
    pivots = [next((j for j in range(5) if matrix[i, j]), None) for i in range(4)]
    if rank != 4 or None in pivots:
        raise ValueError("the four subtracted leaf equations do not determine a line")
    free, = set(range(5))-set(pivots)
    base, direction = [Q(0)]*5, [Q(0)]*5
    direction[free] = Q(1)
    for i, k in enumerate(pivots):
        base[k], direction[k] = matrix[i, 5], -matrix[i, free]

    def form(x, y):
        return inner(x[:3], y[:3])-inner(x[3:], y[3:])

    a, b, c = form(direction, direction), 2*form(base, direction), form(base, base)
    if not a:
        if not b:
            raise ValueError("the final leaf equation has no isolated solution")
        return add(base, scale(-c/b, direction)), (0,)*5, Q(0)
    disc = b*b-4*a*c
    if disc < 0:
        raise ValueError("the leaf has no real completion")
    return add(base, scale(-b/(2*a), direction)), scale(1/(2*a), direction), disc


def sign(x):
    return int(x > 0)-int(x < 0)


def quadratic_sign(a, b, d):
    """Exact sign of a+b*sqrt(d), including a zero or square radicand."""
    if not b or not d:
        return sign(a)
    if not a or sign(a) == sign(b):
        return sign(b)
    return sign(a)*sign(a*a-d*b*b)


def biquadratic_sign(a, b, c, f, d, e):
    """Sign of (a+b*sqrt(d))+(c+f*sqrt(d))*sqrt(e)."""
    x, y = quadratic_sign(a, b, d), quadratic_sign(c, f, d)
    if not y or not e:
        return x
    if not x or x == y:
        return y
    norm0 = a*a+d*b*b-e*(c*c+d*f*f)
    norm1 = 2*(a*b-e*c*f)
    return x*quadratic_sign(norm0, norm1, d)


@lru_cache
def symmetries(faces):
    return [p for p in permutations(range(8))
            if all(frozenset(p[i] for i in f) in faces for f in faces)]


def verify_branch(complex_, parameters, branch, *, separation=None):
    """Check all distances exactly and return the sign class and crossing pairs."""
    assert len(parameters) == 8 and Q(parameters[0]) > 0
    assert len(branch) == 2 and all(i in (-1, 1) for i in branch)
    p, r = core(complex_, parameters)
    pencils = [leaf_pencil(complex_, p, r, j) for j in HINGE_LEAVES]
    d, e = (pencil[2] for pencil in pencils)

    def at(t, u):
        pi, ri = p.copy(), r.copy()
        for j, (base, direction, _), value in zip(HINGE_LEAVES, pencils, (t, u), strict=True):
            v = add(base, scale(value, direction))
            ri[j], pi[j] = v[:3], v[3:]
        return pi, ri

    def edge(pi, i, j):
        return add(subtract(pi[j], pi[i]), period(complex_, i, j))

    # No edge joins 0 and 7. Each squared residual is quadratic in at
    # most one scalar. Reduce it exactly modulo that scalar's square.
    probes = [at(0, 0), at(1, 1), at(-1, -1)]
    for i, j in complex_.edges:
        values = []
        for pi, ri in probes:
            dv, rv = edge(pi, i, j), subtract(ri[j], ri[i])
            values.append(inner(rv, rv)-inner(dv, dv))
        radicand = d if 0 in (i, j) else e if 7 in (i, j) else 0
        c, plus, minus = values
        assert c+radicand*((plus+minus)/Q(2)-c) == 0 and (not radicand or plus == minus)

    # Every oriented area and volume is affine in each leaf separately.
    samples = [at(t, u) for t, u in ((0, 0), (1, 0), (0, 1), (1, 1))]

    def orientation(values):
        a, h, k, l = values
        i, j = branch
        return biquadratic_sign(a, i*(h-a), j*(k-a), i*j*(l-k-h+a), d, e)

    assert all(orientation([ri[j][2] for _, ri in samples]) > 0 for j in (0, 3, 4, 6, 7))
    for i, j, k in complex_.faces:
        assert orientation([cross(edge(pi, i, j), edge(pi, i, k)) for pi, _ in samples]) > 0
    for i, j in complex_.edges:
        for h in ((1, 0), B, subtract(B, (1, 0))):
            values = [2*inner(edge(pi, i, j), h) for pi, _ in samples]
            assert orientation([1-z for z in values]) > 0 and orientation([1+z for z in values]) > 0
    signs = {}
    for q in combinations(range(8), 4):
        signs[q] = orientation([volume(*(subtract(ri[j], ri[q[0]]) for j in q[1:]))
                                for _, ri in samples])
        assert signs[q] != 0
    crossings = []
    for edge_, face in sorted(complex_.disjoint):
        labels = sorted((*edge_, *face))
        circuit = [signs[tuple(labels[:i]+labels[i+1:])]*(-1)**i*(1 if j in edge_ else -1)
                   for i, j in enumerate(labels)]
        if min(circuit) == max(circuit):
            crossings.append((edge_, face))

    cliques = [q for q in signs if all(e in complex_.edges for e in combinations(q, 2))]
    quartets = list(signs)
    candidates = []
    for perm in symmetries(frozenset(map(frozenset, complex_.faces))):
        def relabeled(q):
            image = tuple(perm[i] for i in q)
            return signs[tuple(sorted(image))]*(-1)**sum(i > j for i, j in combinations(image, 2))

        first = relabeled(cliques[0])
        word = sum(1 << i for i, q in enumerate(cliques) if relabeled(q) == first)
        failed = tuple(k for k in (separation or {}).get(format(word, "x"), [])
                       if relabeled(quartets[abs(k)-1]) != first*sign(k))
        candidates.append((word, len(failed), failed))
    word, _, failed = min(candidates)
    if separation is not None:
        return word, crossings, failed
    return word, crossings


def verify(complex_):
    directory = Path(__file__).parent
    data = json.loads((directory/"hex_hinge_witnesses.json").read_text())
    cert = json.loads((directory/"hex_angle_certificates.json").read_text())
    assert set(data) == set(cert["clique_classes"])-{"2e051"}
    for label, record in data.items():
        word, crossings, failed = verify_branch(complex_, record["parameters"], record["branch"],
                                                separation=cert["separation"])
        assert format(word, "x") == label
        assert len(crossings) == record["crossings"] and list(failed) == record["failed_signs"]
        print(f"Class {label} has {len(crossings)} crossing pairs. "
              f"Failed separation signs: {list(failed)}.")
