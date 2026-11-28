"""A nonplanar Type 5 facewise isometry for every reduced modulus with x < 1/2."""

from fractions import Fraction as F
from functools import cache
from itertools import combinations

from flint import fmpq

from .bernstein import RING, Rational, polynomial_sign, positive
from .chart import add, cross, scale, subtract
from .taylor import Taylor


CYCLES = {0: (2, 3, 4, 1, 5), 6: (5, 3, 4, 2, 1), 7: (1, 3, 4, 5, 2)}


class Core:
    """Store a planar point (h,k) in scaled Cartesian coordinates (h, y*k)."""

    def __init__(self, complex_):
        self.complex = complex_
        delta, u = map(Rational, RING.gens())
        self.x = x = F(1, 2) - delta
        self.y_sq = 1/u-x*x
        w = delta - F(9, 32)*delta**2
        gap = delta**3*u**2/32
        inset2 = delta**10*u**5/2048
        inset3 = delta**9*u**5/256
        lift5 = 7*delta/16
        slack = delta**5*u**2/64
        q = w - F(1, 2)
        b = (-q-slack)/(1-2*lift5*u)

        def point(horizontal, dot_b):
            return horizontal, dot_b-x*horizontal

        self.p = p = {1: (Rational(0), Rational(0)),
                      2: point(w-gap, -1/(2*u)+inset2),
                      3: point(F(1, 2)-inset3, b),
                      5: point(q, -1/(2*u)+lift5)}

        def reflect(v):
            return subtract(scale(2*self.dot(p[2], v)/self.dot(p[2], p[2]), p[2]), v)

        e = subtract(reflect(p[5]), add(p[5], self.period(0, 5)))
        f = subtract(reflect(self.project(3, p[3])), p[3])
        leaf = scale(-w/cross(e, f), (f[1], -self.y_sq*f[0]))
        reflected = reflect(leaf)
        shift = self.period(4, 0)

        def residual(v):
            return (self.dot(self.project(4, v), reflected) - self.dot(leaf, subtract(v, shift))
                    - self.dot(v, shift) + self.dot(shift, shift)/2)

        intercept = residual((0, 0))
        slope_x = residual((1, 0)) - intercept
        slope_y = residual((0, 1)) - intercept
        horizontal = Rational(F(-3, 32))
        p[4] = (horizontal, -(slope_x*horizontal+intercept)/slope_y + delta**4/1024)
        self.xy = {i: p[i] for i in (1, 2, 5)}
        self.height_sq = {i: Rational(0) for i in (1, 2, 5)}
        for i in (3, 4):
            v = self.project(i, p[i])
            self.xy[i] = v
            self.height_sq[i] = self.dot(p[i], p[i]) - self.dot(v, v)

    def dot(self, a, b):
        return a[0]*b[0]+a[1]*b[1]/self.y_sq

    @cache
    def period(self, i, j):
        m, n = self.complex.shift[i, j]
        return m+n*self.x, n*self.y_sq

    def project(self, j, v):
        a, b = self.p[2], self.p[5]
        determinant = cross(a, b)

        def rhs(i):
            p = self.p[i]
            s = subtract(p, self.period(i, j))
            return self.dot(s, v) + (self.dot(p, p)-self.dot(s, s))/2

        h, k = rhs(2), rhs(5)
        return ((h*b[1]-k*a[1])/determinant, self.y_sq*(a[0]*k-b[0]*h)/determinant)

    def check(self):
        # Values of the reduced rational functions define the placement, including
        # any removable singularities of the intermediate construction formulas.
        for points in (self.p, self.xy):
            for pair in points.values():
                for coordinate in pair:
                    polynomial_sign(coordinate.denominator)
        positive(self.y_sq)
        positive(cross(self.p[5], self.p[2]))  # The core face 152.
        positive(self.height_sq[3])
        positive(self.height_sq[4])
        core_edges = list(combinations(sorted(self.p), 2))
        for i, k in core_edges:
            if (i, k) == (3, 4):
                continue
            direct = add(subtract(self.p[k], self.p[i]), self.period(i, k))
            horizontal = subtract(self.xy[i], self.xy[k])
            assert (self.dot(direct, direct) - self.dot(horizontal, horizontal)
                    - self.height_sq[i] - self.height_sq[k]).numerator.is_zero()

        for leaf, cycle in CYCLES.items():
            missing = {tuple(sorted(edge)) for edge in zip(cycle, cycle[1:]+cycle[:1])}
            link = {tuple(sorted(v for v in f if v != leaf)) for f in self.complex.faces if leaf in f}
            assert set(core_edges)-missing == link
            for i, k in core_edges:
                a = subtract(self.p[i], self.period(i, leaf))
                b = subtract(self.p[k], self.period(k, leaf))
                v = subtract(a, b)
                horizontal = subtract(self.xy[i], self.xy[k])
                h = (self.dot(v, v) - self.dot(horizontal, horizontal)
                     - self.height_sq[i] - self.height_sq[k])/2
                if (i, k) == (3, 4):
                    # Heights at 3 and 4 have opposite signs. The deficit is h-sqrt(G).
                    positive(h)
                    positive(h**2 - self.height_sq[3]*self.height_sq[4])
                elif (i, k) in missing:
                    positive(h)
                else:
                    assert h.numerator.is_zero()
        assert all(f == (1, 5, 2) or sum(i in CYCLES for i in f) == 1 for f in self.complex.faces)

    def placement_at(self, d, u, *, root4=-1, leaf_signs=(1, -1, 1)):
        scalar = Taylor.variable(F(0), F(0), 2).constant
        x, y = scalar(self.x.at(d, u)), scalar(self.y_sq.at(d, u)).sqrt()
        p = {i: (scalar(a.at(d, u)), scalar(b.at(d, u))/y) for i, (a, b) in self.p.items()}
        return self.complex.reconstruct(p, x, y, Taylor.sqrt, root4=root4, leaf_signs=leaf_signs)

    def base_placement(self):
        return self.placement_at(fmpq(1, 4), fmpq(1, 2))


def verify(complex_):
    core = Core(complex_)
    core.check()
    if not complex_.certifies_embedding(*core.base_placement(), Taylor.sign):
        raise ArithmeticError("the base-point embedding check failed")
    print("Certified nonplanar facewise-isometric maps for 0 <= x < 1/2 and x²+y² >= 1.", flush=True)
