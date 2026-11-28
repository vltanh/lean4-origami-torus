"""Global signs of core tetrahedra and tetrahedra with a single leaf."""

from functools import cached_property

from .bernstein import Rational, polynomial_sign
from .chart import subtract, volume
from .reduced import CYCLES, Core
from .separation import check_implication
from .taylor import Taylor
from .two_leaves import verify as verify_two_leaves


PALETTE = tuple(tuple(map(int, word)) for word in
                "0125 0135 0234 0245 0246 0456 1234 1235 1236 1245 1247 1345 1357 2345 2357 2367 2456".split())


def rational_sign(value):
    if value.numerator.is_zero():
        return 0
    return polynomial_sign(value.numerator)*polynomial_sign(value.denominator)


class Element:
    """An element a+b*g where g is the positive root of the specified rational function."""

    def __init__(self, radicand, a=0, b=0):
        self.radicand = radicand
        self.a, self.b = Rational.coerce(a), Rational.coerce(b)

    def new(self, a, b=0):
        return Element(self.radicand, a, b)

    def coerce(self, value):
        return value if isinstance(value, Element) else self.new(value)

    def __add__(self, other):
        other = self.coerce(other)
        return self.new(self.a+other.a, self.b+other.b)

    __radd__ = __add__

    def __neg__(self):
        return self.new(-self.a, -self.b)

    def __sub__(self, other):
        return self + -self.coerce(other)

    def __rsub__(self, other):
        return -self + other

    def __mul__(self, other):
        other = self.coerce(other)
        return self.new(self.a*other.a+self.b*other.b*self.radicand,
                        self.a*other.b+self.b*other.a)

    __rmul__ = __mul__

    def sign(self):
        try:
            a, b = rational_sign(self.a), rational_sign(self.b)
        except ArithmeticError:
            pass
        else:
            if a*b >= 0:
                return a or b
        norm = rational_sign(self.a**2-self.b**2*self.radicand)
        if norm > 0:
            return rational_sign(self.a)
        if norm < 0:
            return rational_sign(self.b)
        raise ArithmeticError("quadratic norm vanished")


def cross3(v, w):
    return tuple(v[(i+1)%3]*w[(i+2)%3]-v[(i+2)%3]*w[(i+1)%3] for i in range(3))


def dot3(v, w):
    return sum(a*b for a, b in zip(v, w, strict=True))


class CoreVolumes:
    def __init__(self, core):
        self.core = core
        # Spatial coordinates (r_x, y*r_y, r_z/h_3) differ by a positive determinant.
        self.generator = Element(core.height_sq[4]/core.height_sq[3], 0, 1)
        constant = self.generator.new
        self.points = {i: (constant(v[0]), constant(v[1]),
                           -self.generator if i == 4 else constant(int(i == 3)))
                       for i, v in core.xy.items()}

    @cached_property
    def weights(self):
        s = self.core
        result = {}
        for leaf, cycle in CYCLES.items():
            result[leaf] = []
            for i, j in zip(cycle, cycle[1:]+cycle[:1]):
                a, b = subtract(s.p[i], s.period(i, leaf)), subtract(s.p[j], s.period(j, leaf))
                v = subtract(a, b)
                horizontal = subtract(s.xy[i], s.xy[j])
                h = (s.dot(v, v)-s.dot(horizontal, horizontal)-s.height_sq[i]-s.height_sq[j])/2
                result[leaf].append(self.generator.new(h, -s.height_sq[3] if {i,j} == {3,4} else 0))
        return result

    def single_leaf(self, leaf, triple):
        a, b, c = triple
        cycle = CYCLES[leaf]
        points = self.points
        weights = self.weights[leaf]
        normal = cross3(subtract(points[b], points[a]), subtract(points[c], points[a]))
        normal_sq = (normal[0]*normal[0]+normal[1]*normal[1]*self.core.y_sq
                     +normal[2]*normal[2]*(1/self.core.height_sq[3]))
        i, j = [k for k in range(5) if cycle[k] not in triple]

        def term(k):
            offset = dot3(normal, subtract(points[cycle[k]], points[a]))
            return offset*weights[(k+1)%5]*weights[(k+3)%5]

        direction = 1 if (i-j)%5 in (1, 4) else -1
        weighted = term(i)+direction*term(j)
        determinant = self.generator.new(2)
        for weight in weights:
            determinant = determinant*weight
        return weighted*weighted-determinant*normal_sq

    def core_bracket(self, vertices):
        a, b, c, d = (self.points[i] for i in vertices)
        return dot3(cross3(subtract(b, a), subtract(c, a)), subtract(d, a))


def verify(complex_):
    core = Core(complex_)
    core.check()
    placement = core.base_placement()
    if not complex_.certifies_embedding(*placement, Taylor.sign):
        raise ArithmeticError("the base-point faces or spatial separation failed")
    _, points, _ = placement
    signs = {q: Taylor.sign(volume(*(subtract(points[i], points[q[0]]) for i in q[1:])))
             for q in PALETTE}
    check_implication(complex_, signs)
    volumes = CoreVolumes(core)
    for q in PALETTE:
        leaves = [i for i in q if i in CYCLES]
        if not leaves:
            if volumes.core_bracket(q).sign() != signs[q]:
                raise ArithmeticError(f"uncertified core bracket {q}")
        if len(leaves) == 1:
            triple = tuple(i for i in q if i != leaves[0])
            if not volumes.single_leaf(leaves[0], triple).sign():
                raise ArithmeticError(f"the one-leaf eliminant vanished for {q}")
    print("Certified all five core and nine single-leaf signs.", flush=True)
    verify_two_leaves(volumes, [q for q in PALETTE if sum(i in CYCLES for i in q) == 2])
    print("Certified embeddings for every reduced modulus with 0 <= x < 1/2.", flush=True)
