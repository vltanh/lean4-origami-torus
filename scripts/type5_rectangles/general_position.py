"""Rule out a forced spatial coplanarity at any fixed sharp modulus.

For each quartet of labels, two integer test cores give coprime polynomials
in the period height y. Thus, at every fixed y, at least one specialization
of the coplanarity polynomial is nonzero. Test cores are algebraic probes;
they need not themselves develop into embedded tori.
"""

from itertools import combinations, product

from flint import fmpq, fmpq_poly

from .chart import dot, norm_sq, subtract, volume
from .two_leaves import PolynomialPair


ZERO, ONE, Y = fmpq_poly(), fmpq_poly([1]), fmpq_poly([0, 1])
CORES = (
    ((1, 2), (3, 5), (7, 11), (2, -1)),
    ((-5, -6), (1, 3), (-3, -6), (6, 3)),
)


def field_norm(value):
    return value.a**2 - value.radicand*value.b**2


def determinant(columns):
    a, b, c, d = columns
    return (a[0]*volume(b[1:], c[1:], d[1:]) - b[0]*volume(a[1:], c[1:], d[1:])
            + c[0]*volume(a[1:], b[1:], d[1:]) - d[0]*volume(a[1:], b[1:], c[1:]))


def add_product(out, first, second, coefficient, zero):
    for i, a in first.items():
        for j, b in second.items():
            powers = tuple(x+y for x, y in zip(i, j, strict=True))
            out[powers] = out.get(powers, zero) + coefficient*a*b


def eliminate(polynomial, quadratic, zero):
    """Eliminate the first leaf variable by polynomial remainder and a quadratic norm."""
    a, b, c = quadratic
    by_degree = {}
    for powers, value in polynomial.items():
        by_degree.setdefault(powers[0], {})[powers[1:]] = value
    # At a root of a*s²+b*s+c, replace a*D by a*D-leading(D)*s^(degree-2)*(a*s²+b*s+c).
    for degree in range(max(by_degree), 1, -1):
        leading = by_degree.pop(degree, {})
        for k, terms in by_degree.items():
            by_degree[k] = {powers: a*value for powers, value in terms.items()}
        for k, coefficient in ((degree-1, b), (degree-2, c)):
            terms = by_degree.setdefault(k, {})
            for powers, value in leading.items():
                terms[powers] = terms.get(powers, zero) - coefficient*value
    constant, linear = by_degree.get(0, {}), by_degree.get(1, {})
    # a times the product of constant+s*linear over the two roots.
    out = {}
    add_product(out, constant, constant, a, zero)
    add_product(out, constant, linear, -b, zero)
    add_product(out, linear, linear, c, zero)
    return out


class TestCore:
    def __init__(self, complex_, coordinates):
        self.complex = complex_
        self.p = {i: tuple(fmpq_poly([v]) for v in pair)
                  for i, pair in enumerate(((0, 0), *coordinates), 1)}
        self.anchor_det = (self.p[2][0]*self.p[5][1]-self.p[2][1]*self.p[5][0])[0]
        assert self.anchor_det != 0
        self.horizontal = {i: self.project(i, self.p[i]) for i in (3, 4)}
        height = {i: norm_sq(self.p[i])-norm_sq(self.horizontal[i]) for i in (3, 4)}
        self.h3 = height[3]
        self.radicand = height[3]*height[4]
        # z is the product of the signed physical heights at 3 and 4.
        def scalar(p):
            return PolynomialPair(self.radicand, p, ZERO)
        self.zero = scalar(ZERO)
        self.columns = {i: [[scalar(ONE), *map(scalar, self.p[i]), self.zero]] for i in (1, 2, 5)}
        self.columns[3] = [[scalar(ONE), *map(scalar, self.horizontal[3]), scalar(height[3])]]
        self.columns[4] = [[scalar(ONE), *map(scalar, self.horizontal[4]),
                            PolynomialPair(self.radicand, ZERO, ONE)]]
        self.quadratics = {}
        self.guards = {}
        for leaf in (0, 6, 7):
            self.parameterize_leaf(leaf)

    def lifted(self, i, j):
        m, n = self.complex.shift[i, j]
        return subtract(self.p[i], (fmpq_poly([m+fmpq(n, 2)]), n*Y))

    def rhs(self, i, j, intrinsic):
        s = self.lifted(i, j)
        return dot(s, intrinsic) + (norm_sq(self.p[i])-norm_sq(s))/2

    def project(self, j, intrinsic):
        a, b = self.p[2], self.p[5]
        h, k = (self.rhs(i, j, intrinsic) for i in (2, 5))
        return ((h*b[1]-k*a[1])/self.anchor_det, (k*a[0]-h*b[0])/self.anchor_det)

    def parameterize_leaf(self, leaf):
        origin, ex, ey = (ZERO, ZERO), (ONE, ZERO), (ZERO, ONE)

        def height_rhs(root, intrinsic):
            return self.rhs(root, leaf, intrinsic) - dot(self.horizontal[root], self.project(leaf, intrinsic))

        def axis(v):
            # h3 is the squared root-3 height. This equation eliminates the leaf height.
            return PolynomialPair(self.radicand, self.h3*height_rhs(4, v), -height_rhs(3, v))

        c = axis(origin)
        a, b = axis(ex)-c, axis(ey)-c
        base = self.project(leaf, origin)
        dx, dy = (subtract(self.project(leaf, e), base) for e in (ex, ey))
        z0 = height_rhs(3, origin)
        zx, zy = (height_rhs(3, e)-z0 for e in (ex, ey))

        def column(w, u, v):
            horizontal = [w.scale(k)+u.scale(i)+v.scale(j) for k, i, j in zip(base, dx, dy, strict=True)]
            return [w, *horizontal, w.scale(z0)+u.scale(zx)+v.scale(zy)]

        # For intrinsic coordinates (s,(-a*s-c)/b), X+s*D is the homogeneous
        # spatial column, with its physical height multiplied by the root-3 height.
        p0, p1 = (self.zero, -c), (b, -a)
        x, d = column(b, *p0), column(self.zero, *p1)

        def metric(u, v, p, q):
            horizontal = u[1]*v[1]+u[2]*v[2]-p[0]*q[0]-p[1]*q[1]
            return horizontal.scale(self.h3)+u[3]*v[3]

        quadratic = (metric(d, d, p1, p1), metric(x, d, p0, p1).scale(2), metric(x, x, p0, p0))
        self.columns[leaf] = [x, d]
        self.quadratics[leaf] = quadratic
        self.guards[leaf] = field_norm(b)*field_norm(quadratic[0])

    def obstruction(self, labels):
        leaves = [i for i in labels if i in self.quadratics]
        coefficients = {}
        for powers in product((0, 1), repeat=len(leaves)):
            selection = dict(zip(leaves, powers, strict=True))
            coefficients[powers] = determinant([self.columns[i][selection.get(i, 0)] for i in labels])
        for leaf in leaves:
            coefficients = eliminate(coefficients, self.quadratics[leaf], self.zero)
        result = self.radicand*field_norm(coefficients[()])
        for leaf in leaves:
            result *= self.guards[leaf]
        return result


def verify(complex_):
    first, second = (TestCore(complex_, core) for core in CORES)
    for labels in combinations(range(8), 4):
        if first.obstruction(labels).gcd(second.obstruction(labels)).degree() != 0:
            raise ArithmeticError(f"coplanarity test polynomials have a common root for {labels}")
    print("Certified fixed-modulus general-position density for all 70 quartets on the sharp ray.", flush=True)
