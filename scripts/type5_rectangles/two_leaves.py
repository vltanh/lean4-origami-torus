"""Exclude a common plane through two leaves and a core edge over the reduced domain.

If a leaf Z is in the plane through r_a with normal n, put v_i = n·(r_i-r_a).
These are the inner products of the spatial covector (n,0) with the five signed
rays from Z. Their Gram matrix S is invertible, so vᵀ adj(S) v = det(S) ||n||².
For planes containing the core edge (a,b), this equation is a homogeneous binary
quadratic in the components of n along its normal pencil. Two coplanar leaves
would supply a common real projective root of their quadratics.
"""

from functools import reduce
from math import lcm
from operator import mul

from flint import fmpz_poly

from .bernstein import RING, Rational, polynomial_sign
from .reduced import CYCLES


ONE = RING.constant(1)
ZERO = RING.constant(0)


class PolynomialPair:
    """a+b*z with polynomial coefficients and z² equal to a fixed polynomial."""

    def __init__(self, radicand, a=ZERO, b=ZERO):
        self.radicand, self.a, self.b = radicand, a, b

    def new(self, a, b):
        return PolynomialPair(self.radicand, a, b)

    def __add__(self, other):
        return self.new(self.a+other.a, self.b+other.b)

    def __neg__(self):
        return self.new(-self.a, -self.b)

    def __sub__(self, other):
        return self.new(self.a-other.a, self.b-other.b)

    def __mul__(self, other):
        return self.new(self.a*other.a+self.radicand*(self.b*other.b),
                        self.a*other.b+self.b*other.a)

    def scale(self, scalar):
        return self.new(self.a*scalar, self.b*scalar)

    def square(self):
        return self.new(self.a**2+self.radicand*self.b**2, 2*self.a*self.b)


def primitive(values, check_factor):
    """Divide a polynomial vector by a common, everywhere nonzero scalar."""
    parts = sorted((p for v in values for p in (v.a, v.b) if p), key=lambda p: sum(p.degrees()))
    if not parts:
        raise ArithmeticError("zero polynomial vector")
    divisor = parts[0]
    for part in parts[1:]:
        divisor = divisor.gcd(part)
        if divisor.degrees() == (0, 0):
            return values, ONE
    check_factor(divisor)
    return [v.new(v.a/divisor, v.b/divisor) for v in values], divisor


def square_parts(p):
    scalar, factors = p.factor_squarefree()
    square, rest = ONE, ONE
    for f, e in factors:
        square *= f**(e//2)
        if e % 2:
            rest *= f
    return scalar, square, rest


class PencilField:
    def __init__(self, volumes, check_factor):
        self.volumes = volumes
        self.check_factor = check_factor
        radicand = volumes.generator.radicand
        top, a, b = square_parts(radicand.numerator)
        bottom, c, d = square_parts(radicand.denominator)
        # sqrt(radicand) = scale*z for one of the two roots of z² = b*d.
        # The polynomial norm below checks both choices. Clearing scale is valid
        # on the whole domain including each half-open rectangle's right edges.
        self.scale, self.square = Rational(a, c*d), b*d*(top/bottom)
        check_factor(self.scale.numerator)
        check_factor(self.scale.denominator)
        residual = self.scale**2 * Rational(self.square) - radicand
        if not residual.numerator.is_zero():
            raise ArithmeticError("incorrect square extraction")
        self.zero = PolynomialPair(self.square)

    def clear(self, values):
        """Return integral pairs and the common rational multiplier used on every entry."""
        coeffs = [(v.a, v.b*self.scale) for v in values]
        denominator = ONE
        for pair in coeffs:
            for value in pair:
                other = value.denominator
                denominator = (denominator/denominator.gcd(other))*other
        self.check_factor(denominator)
        pairs = [self.zero.new(a.numerator*(denominator/a.denominator),
                               b.numerator*(denominator/b.denominator)) for a, b in coeffs]
        reduced, divisor = primitive(pairs, self.check_factor)
        return reduced, Rational(denominator, divisor)


def fast_polynomial_sign(p):
    """Use the Bernstein sign test via two univariate integer Taylor shifts.

    For degrees m,n, clear positive denominators in
      [2(1+r)]^m (1+s)^n p(1/(2(1+r)),1/(1+s)).
    Its positive orthant r,s >= 0 maps onto the whole half-open rectangle.
    A strict constant term and coefficients of one weak sign prove strictness.
    """
    if not p:
        raise ArithmeticError("zero resultant norm")
    m, n = p.degrees()
    multiplier = lcm(*(int(v.q) for _, v in p.terms()))
    rows = {}
    for (i, j), c in p.terms():
        if j not in rows:
            rows[j] = [0]*(m+1)
        rows[j][m-i] = c.p*(multiplier//c.q)*2**(m-i)
    shift = fmpz_poly([1, 1])
    columns = [[0]*(n+1) for _ in range(m+1)]
    for j, row in rows.items():
        for i, value in enumerate(fmpz_poly(row)(shift)):
            columns[i][n-j] = value
    del rows
    sign = 0
    for i, column in enumerate(columns):
        shifted = fmpz_poly(column)(shift)
        if i == 0:
            sign = int(shifted[0] > 0) - int(shifted[0] < 0)
            if sign == 0:
                raise ArithmeticError("resultant norm vanishes at the upper corner")
        if any(sign*c < 0 for c in shifted):
            raise ArithmeticError("mixed Bernstein signs in the resultant norm")
    return sign


def subtract3(a, b):
    return tuple(x-y for x, y in zip(a, b, strict=True))


def dot3(a, b):
    return a[0]*b[0]+a[1]*b[1]+a[2]*b[2]


def binary_pencil(field, points, point_scale, edge, leaf):
    volumes, core = field.volumes, field.volumes.core
    a, b = edge
    e = subtract3(points[b], points[a])
    # Each covector pair spans the edge's normal plane, with the same basis
    # for both leaves. The anchor triangle is nondegenerate and each root has
    # nonzero height. A horizontal anchor edge uses a vertical second normal.
    roots = {a, b} & {3, 4}
    if not roots:
        basis = [(-e[1], e[0], field.zero), (field.zero, field.zero, field.zero.new(ONE, ZERO))]
    elif len(roots) == 1:
        basis = [(e[2], field.zero, -e[0]), (field.zero, e[2], -e[1])]
    else:
        raise ValueError("the plane pencil requires an anchor endpoint")
    normals = [primitive(v, field.check_factor)[0] for v in basis]
    weights, weight_scale = field.clear(volumes.weights[leaf])
    determinant = reduce(mul, weights).scale(2)
    cycle = CYCLES[leaf]
    indices = [i for i, v in enumerate(cycle) if v not in edge]
    entries = [dot3(normal, subtract3(points[cycle[i]], points[a]))
               * (weights[(i+1)%5]*weights[(i+3)%5]) for normal in normals for i in indices]
    entries, divisor = primitive(entries, field.check_factor)
    terms = [entries[:3], entries[3:]]
    # The (i,l) adjugate entry is the product of the two alternating weight
    # products above, times +1 at cyclic distance 0 or 1, and -1 at distance 2.
    # For the chosen normals the endpoint entries vanish, leaving three terms.
    def sign(i, j):
        return 1 if (i-j)%5 in (0, 1, 4) else -1

    signed = [[v.scale(sign(indices[0], i)) for v, i in zip(row, indices, strict=True)] for row in terms]
    totals = [sum(row, field.zero) for row in signed]
    correction = sign(indices[0], indices[1])*sign(indices[0], indices[2])*sign(indices[1], indices[2])
    # With points multiplied by t and cycle weights by w, the adjugate term
    # acquires t²w⁴ and det(S) acquires w⁵. Multiplying the adjugate term by w
    # and the norm term by t² makes both scales equal. Restore the common divisor
    # removed from each linear form before comparing their products.
    t2 = point_scale**2
    metric, _ = field.clear([volumes.generator.new(q) for q in
                             [weight_scale*Rational(divisor**2), t2, t2*core.y_sq, t2/core.height_sq[3]]])

    def coefficient(i, j):
        adj = totals[i]*totals[j]
        if correction < 0:
            adj = adj-(signed[i][1]*signed[j][2]+signed[i][2]*signed[j][1]).scale(2)
        norm = sum((k*x*y for k, x, y in zip(metric[1:], normals[i], normals[j], strict=True)), field.zero)
        return metric[0]*adj-determinant*norm

    return primitive([coefficient(0, 0), coefficient(0, 1).scale(2), coefficient(1, 1)], field.check_factor)[0]


def verify(volumes, brackets, *, check_factor=polynomial_sign, check_norm=fast_polynomial_sign):
    """Exclude coplanarity for the three two-leaf brackets in the sparse sign list."""
    field = PencilField(volumes, check_factor)
    vertices = sorted(volumes.points)
    coordinates, scale = field.clear([q for v in vertices for q in volumes.points[v]])
    points = {v: coordinates[3*i:3*i+3] for i, v in enumerate(vertices)}
    for bracket in brackets:
        a, b = (v for v in bracket if v not in CYCLES)
        j, k = (v for v in bracket if v in CYCLES)
        A, B, C = binary_pencil(field, points, scale, (a, b), j)
        D, E, F = binary_pencil(field, points, scale, (a, b), k)
        # Two binary quadratics As²+Bst+Ct², Ds²+Est+Ft² share a projective
        # root only if (AF-CD)² - (AE-BD)(BF-CE) is zero. This includes t=0.
        h, k0, l = primitive([A*E-B*D, A*F-C*D, B*F-C*E], check_factor)[0]
        res = primitive([k0.square()-h*l], check_factor)[0][0]
        check_norm(res.a**2-field.square*res.b**2)
        labels = ''.join(map(str, bracket))
        print(f"Certified the two-leaf bracket {labels} throughout the parameter domain.", flush=True)
