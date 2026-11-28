"""The seventeen spatial signs of the open sharp-ray family, by exact univariate algebra."""

from fractions import Fraction as F
from itertools import combinations

from flint import fmpq, fmpq_poly

from .bernstein import RING, Rational
from .chart import add, cross, subtract, volume
from .projections import CoreVolumes, rational_sign
from .reduced import CYCLES, Core
from .sharp_embeddings import core_coordinates
from .taylor import Taylor
from .two_leaves import verify as verify_two_leaves


# The hypotheses of OrigamiTorus.Type5.SharpRay.spatial_embedding.
SIGNS = {tuple(map(int, entry[:4])): (1 if entry[-1] == "+" else -1) for entry in
         ("0125+ 0126+ 0134- 0136- 0234- 1234+ 1236- 1237+ 1245+ 1345- "
          "1356+ 1357- 1456+ 2345+ 2347- 2456- 2467-").split()}


def polynomial_sign(polynomial):
    """Certify a constant strict sign on 0 < u < 1/2 using rational coefficients."""
    if not polynomial:
        raise ArithmeticError("expected a nonzero univariate polynomial")
    terms = polynomial.to_dict()
    if any(j != 0 for i, j in terms):
        raise ValueError("unexpected second variable in a sharp-ray polynomial")
    degree = polynomial.degrees()[0]
    p = fmpq_poly([terms.get((i, 0), 0) for i in range(degree+1)])
    one_plus_z = fmpq_poly([1, 1])

    def on_interval(left, right, depth):
        # Horner evaluation of (1+z)^degree p((left+right*z)/(1+z)).
        linear = fmpq_poly([left, right])
        transformed = fmpq_poly([p[degree]])
        power = one_plus_z
        for i in reversed(range(degree)):
            transformed = transformed*linear + power*p[i]
            power *= one_plus_z
        signs = {1 if c > 0 else -1 for c in transformed if c}
        if len(signs) == 1:
            return signs.pop()
        if depth == 3 or p(left)*p(right) < 0:
            raise ArithmeticError("polynomial sign not certified")
        midpoint = (left+right)/2
        midpoint_sign = int(p(midpoint) > 0) - int(p(midpoint) < 0)
        if (not midpoint_sign or on_interval(left, midpoint, depth+1) != midpoint_sign
                or on_interval(midpoint, right, depth+1) != midpoint_sign):
            raise ArithmeticError("polynomial does not have one strict sign")
        return midpoint_sign

    return on_interval(fmpq(0), fmpq(1, 2), 0)


def sign(value):
    return rational_sign(value, polynomial_sign)


class SharpCore(Core):
    """The rational core in (X, yY) coordinates, with u = t/(1+2t)."""

    def __init__(self, complex_):
        self.complex = complex_
        u = Rational(RING.gens()[0])
        t = u/(1-2*u)
        self.x = Rational(F(1, 2))
        self.y_sq = t+F(3, 4)
        intrinsic = core_coordinates(t, u, Rational)
        self.p = {i: (Rational.coerce(x), dot_b-self.x*x) for i, (x, dot_b) in intrinsic.items()}
        self.xy = {i: self.p[i] for i in (1, 2, 5)}
        self.height_sq = {i: Rational(0) for i in self.xy}
        for i in (3, 4):
            self.xy[i] = self.project(i, self.p[i])
            self.height_sq[i] = self.dot(self.p[i], self.p[i])-self.dot(self.xy[i], self.xy[i])

    def check_geometry(self, volumes):
        for points in (self.p, self.xy):
            for pair in points.values():
                for coordinate in pair:
                    polynomial_sign(coordinate.denominator)
        for value in (self.y_sq, cross(self.p[5], self.p[2]), self.height_sq[3], self.height_sq[4]):
            if sign(value) != 1:
                raise ArithmeticError("degenerate sharp core")
        edges = set(combinations(sorted(self.p), 2))
        for i, j in edges - {(3, 4)}:
            direct = add(subtract(self.p[j], self.p[i]), self.period(i, j))
            horizontal = subtract(self.xy[j], self.xy[i])
            residual = (self.dot(direct, direct)-self.dot(horizontal, horizontal)
                        -self.height_sq[i]-self.height_sq[j])
            if residual.numerator:
                raise ArithmeticError(f"core length mismatch at {(i, j)}")
        for leaf, cycle in CYCLES.items():
            cycle_edges = {tuple(sorted(e)) for e in zip(cycle, cycle[1:]+cycle[:1])}
            link = {tuple(sorted(v for v in f if v != leaf)) for f in self.complex.faces if leaf in f}
            if edges-cycle_edges != link or any(w.sign(sign) != 1 for w in volumes.weights[leaf]):
                raise ArithmeticError(f"invalid positive five-cycle at {leaf}")
            for i, j in link:
                a = subtract(self.p[i], self.period(i, leaf))
                b = subtract(self.p[j], self.period(j, leaf))
                direct, horizontal = subtract(a, b), subtract(self.xy[i], self.xy[j])
                residual = (self.dot(direct, direct)-self.dot(horizontal, horizontal)
                            -self.height_sq[i]-self.height_sq[j])
                if residual.numerator:
                    raise ArithmeticError(f"nonzero off-cycle Gram entry at {(leaf, i, j)}")


def verify(complex_):
    core = SharpCore(complex_)
    volumes = CoreVolumes(core, root4=1)
    core.check_geometry(volumes)
    # At u=1/4 (t=1/2) fix the positive/negative/positive leaf branches.
    p, r, period = core.placement_at(fmpq(1, 4), fmpq(0), root4=1, leaf_signs=(1, -1, 1))
    if not complex_.positive_faces(p, period, Taylor.sign):
        raise ArithmeticError("a marked base-point face is not positive")
    binary = []
    for q, expected in SIGNS.items():
        base = volume(*(subtract(r[i], r[q[0]]) for i in q[1:]))
        if base.sign() != expected:
            raise ArithmeticError(f"wrong base-point bracket sign at {q}")
        leaves = [i for i in q if i in CYCLES]
        if not leaves:
            if volumes.core_bracket(q).sign(sign) != expected:
                raise ArithmeticError(f"incorrect core bracket sign at {q}")
        elif len(leaves) == 1:
            triple = tuple(i for i in q if i != leaves[0])
            if volumes.single_leaf(leaves[0], triple).sign(sign) == 0:
                raise ArithmeticError(f"vanishing one-leaf eliminant at {q}")
        else:
            binary.append(q)
    verify_two_leaves(volumes, binary, check_factor=polynomial_sign, check_norm=polynomial_sign)
    print("Certified the seventeen sharp-ray signs for every t > 0.", flush=True)
