"""Radical placement and tests on the labeled Type 5 complex."""

from fractions import Fraction
from itertools import combinations
import json
from pathlib import Path
import subprocess


def subtract(a, b):
    return tuple(x - y for x, y in zip(a, b, strict=True))


def add(a, b):
    return tuple(x + y for x, y in zip(a, b, strict=True))


def scale(k, a):
    return tuple(k * x for x in a)


def dot(a, b):
    return sum(x * y for x, y in zip(a, b, strict=True))


def norm_sq(a):
    return dot(a, a)


def cross(a, b):
    return a[0] * b[1] - a[1] * b[0]


def volume(a, b, c):
    return a[0]*cross(b[1:], c[1:]) - b[0]*cross(a[1:], c[1:]) + c[0]*cross(a[1:], b[1:])


def core(t, x, parameters):
    """Physical core coordinates for periods (1,0), (x,1/t)."""
    b, d, k, ell, cx, alpha, beta, e2, e3 = parameters
    unit = t**0
    length = unit + (x*t)**2
    u = t**2 / length
    q = -b + 2*b*d*u - k*u**2
    p = q + unit/2 - ell*u**2
    x3 = unit/2 - e3*u**5

    def point(horizontal, fraction, offset):
        return horizontal, fraction*length/t + t*(offset - x*horizontal)

    return {
        1: (0, 0),
        2: point(p, -unit/2 + e2*u**6, 0),
        3: (x3, t*(b - x*x3)),
        4: point(cx, alpha, beta),
        5: point(q, -unit/2, d),
    }


TAIL_PARAMETERS = (Fraction(3, 32), Fraction(15, 64), Fraction(3, 256), Fraction(1, 65),
                   Fraction(-11, 89), Fraction(7, 32), Fraction(1, 16),
                   Fraction(1, 2**17), Fraction(1, 2**16))

# t = index/64. The six entries interpolate linearly with denominator 10^6.
KNOTS = {
    2:  (95875, 232607, 12172, 16044, -126775, 219823),
    6:  (95973, 233296, 11928, 15988, -126698, 221061),
    17: (96417, 240903, 10566, 16400, -125395, 235007),
    33: (99033, 266339, 7106, 17623, -122513, 277804),
    49: (107926, 301670, 3394, 18325, -121085, 339931),
    62: (121403, 291750, 1336, 13150, -122116, 375977),
    64: (122993, 285185, 1146, 11945, -121602, 379005),
}


def finite_parameters(t, lo, hi, constant):
    z = (64*t - lo)/(hi-lo)
    values = [(a + z*(b-a))/10**6 for a, b in zip(KNOTS[lo], KNOTS[hi], strict=True)]
    return values + [constant(0), constant(Fraction(1, 2**19)), constant(Fraction(1, 2**18))]


class Complex:
    def __init__(self):
        script = Path(__file__).with_name("Inputs.lean").resolve()
        data = json.loads(subprocess.check_output(["lake", "env", "lean", "--run", str(script)],
                                                  cwd=script.parents[2], text=True))
        self.faces = [tuple(face) for face in data["faces"]]
        self.edges = set()
        self.shift = {}
        for a, b, m, n in data["shifts"]:
            self.edges.add((a, b))
            self.shift[a, b] = (m, n)
            self.shift[b, a] = (-m, -n)
        actual_edges = {tuple(sorted(e)) for f in self.faces for e in combinations(f, 2)}
        core_edges = {tuple(sorted((a, b))) for a in (1, 2, 5) for b in range(8) if a != b}
        leaf_edges = {tuple(sorted((a, b))) for a in (3, 4) for b in (0, 6, 7)}
        assert self.edges == actual_edges == core_edges | leaf_edges
        assert len(self.faces) == 16 and len(self.edges) == 24
        assert all(self.shift[1, b] == (0, 0) for b in range(8) if b != 1)
        assert self.shift[2, 5] == (0, 0)
        for a, b, c in self.faces:
            assert add(self.shift[a, b], self.shift[b, c]) == self.shift[a, c]
        self.disjoint = [(e, f) for e in self.edges for f in self.faces if set(e).isdisjoint(f)]
        assert len(self.disjoint) == 138
        subfaces = {frozenset(s) for f in self.faces for k in (1, 2, 3) for s in combinations(f, k)}
        for a, b in combinations(subfaces, 2):
            if a.isdisjoint(b) and len(a) + len(b) <= 5:
                assert any((a.issubset(e) and b.issubset(f)) or (b.issubset(e) and a.issubset(f))
                           for e, f in self.disjoint)

    def anchor_geometry(self, p, x, y):
        """Period shifts and horizontal projections determined by the three anchors."""
        a, b = p[2], p[5]
        determinant = cross(a, b)

        def period(i, j):
            m, n = self.shift[i, j]
            return m + n*x, n*y

        def offset(i, j):
            return subtract(p[i], period(i, j))

        def solve(u, v):
            return ((u*b[1] - a[1]*v)/determinant, (a[0]*v - u*b[0])/determinant)

        def project(j, u):
            def rhs(i):
                s = offset(i, j)
                return dot(s, u) + (norm_sq(p[i]) - norm_sq(s))/2
            return solve(rhs(2), rhs(5))

        return period, offset, project

    def reconstruct(self, p, x, y, sqrt, *, root4=-1, leaf_signs=(1, -1, 1)):
        """Solve the 24 squared length equations with the specified radical signs."""
        p = dict(p)
        period, offset, project = self.anchor_geometry(p, x, y)
        r = {i: (*p[i], 0) for i in (1, 2, 5)}
        for j, sign in ((3, 1), (4, root4)):
            v = project(j, p[j])
            r[j] = (*v, sign*sqrt(norm_sq(p[j]) - norm_sq(v)))

        for j, sign in zip((0, 6, 7), leaf_signs, strict=True):
            c = project(j, (0, 0))
            columns = [subtract(project(j, e), c) for e in ((1, 0), (0, 1))]

            def linear(v):
                return add(scale(v[0], columns[0]), scale(v[1], columns[1]))

            rows, constants = [], []
            for i in (3, 4):
                s = offset(i, j)
                rows.append(subtract(s, tuple(dot(r[i][:2], v) for v in columns)))
                constants.append((norm_sq(r[i]) - norm_sq(s))/2 - dot(r[i][:2], c))

            normal = subtract(scale(r[4][2], rows[0]), scale(r[3][2], rows[1]))
            intercept = r[4][2]*constants[0] - r[3][2]*constants[1]
            u = scale(-intercept/norm_sq(normal), normal)
            du = (-normal[1], normal[0])
            v = (*add(c, linear(u)), (dot(rows[0], u) + constants[0])/r[3][2])
            dv = (*linear(du), dot(rows[0], du)/r[3][2])
            qa = norm_sq(dv) - norm_sq(du)
            qb = 2*(dot(v, dv) - dot(u, du))
            qc = norm_sq(v) - norm_sq(u)
            root = (-qb + sign*sqrt(qb*qb - 4*qa*qc))/(2*qa)
            p[j], r[j] = add(u, scale(root, du)), add(v, scale(root, dv))
        return p, r, period

    def positive_faces(self, p, period, sign):
        for a, b, c in self.faces:
            u = add(subtract(p[b], p[a]), period(a, b))
            v = add(subtract(p[c], p[a]), period(a, c))
            if sign(cross(u, v)) != 1:
                return False
        return True

    def certifies_embedding(self, p, r, period, sign):
        if not self.positive_faces(p, period, sign):
            return False
        signs = {}
        for q in combinations(range(8), 4):
            signs[q] = sign(volume(*(subtract(r[i], r[q[0]]) for i in q[1:])))
        for edge, face in self.disjoint:
            q = tuple(sorted((*edge, *face)))
            circuit = [(-1)**i * (1 if v in edge else -1) * signs[q[:i] + q[i+1:]]
                       for i, v in enumerate(q)]
            if not min(circuit) < 0 < max(circuit):
                return False
        return True
