"""All sixteen nonplanar completions of a fixed Type 5 core on the sharp ray."""

from fractions import Fraction as F
from itertools import combinations, product

from flint import fmpq

from .bernstein import RING, Rational, polynomial_sign
from .chart import subtract, volume
from .projections import CoreVolumes
from .reduced import CYCLES, Core
from .taylor import Taylor


class SharpCore(Core):
    def __init__(self, complex_):
        self.complex = complex_
        self.x = Rational(F(1, 2))
        u = Rational(RING.gen(1))
        T = 1/u
        self.y_sq = T - self.x**2

        def point(a, b):
            return Rational.coerce(a), b-self.x*a

        self.p = {
            1: point(0, 0),
            2: point(F(-1, 12), -T/2+F(1, 12)),
            3: point(F(5, 12), F(1, 6)),
            4: point(F(-1, 6), T/3-F(1, 6)),
            5: point(F(-5, 12), -T/2+F(1, 12)),
        }
        self.xy = {i: self.project(i, p) if i in (3, 4) else p for i, p in self.p.items()}
        self.height_sq = {i: self.dot(p, p)-self.dot(self.xy[i], self.xy[i]) for i, p in self.p.items()}


def bracket_norms(core):
    """A nonzero norm excludes a zero of the bracket for either root-4 height and every leaf choice."""
    volumes = CoreVolumes(core)
    norms = {}
    for labels in combinations(range(8), 4):
        leaves = set(labels) & CYCLES.keys()
        if len(leaves) > 1:
            continue
        if leaves:
            leaf, = leaves
            value = volumes.single_leaf(leaf, tuple(i for i in labels if i != leaf))
        else:
            value = volumes.core_bracket(labels)
        norms[labels] = value.a**2 - value.b**2*value.radicand
    return norms


def strict_on_cell(norm, left, right):
    """Certify nonvanishing for left < U <= right."""
    d, u = RING.gens()
    coordinate = RING.constant(left) + (right-left)*u
    try:
        polynomial_sign(norm.numerator.compose(d, coordinate))
        polynomial_sign(norm.denominator.compose(d, coordinate))
    except ArithmeticError:
        return False
    return True


def crossings_on_cell(core, norms, left, right):
    stable = {q for q, norm in norms.items() if strict_on_cell(norm, left, right)}
    circuits = []
    for edge, face in core.complex.disjoint:
        labels = tuple(sorted((*edge, *face)))
        minors = [labels[:i]+labels[i+1:] for i in range(5)]
        if stable.issuperset(minors):
            circuits.append([(q, (-1)**i * (1 if v in edge else -1))
                             for i, (q, v) in enumerate(zip(minors, labels, strict=True))])
    for root4, *leaf_signs in product((-1, 1), repeat=4):
        p, r, period = core.placement_at(0, (left+right)/2, root4=root4, leaf_signs=leaf_signs)
        if not core.complex.positive_faces(p, period, Taylor.sign):
            raise ArithmeticError("uncertified orientation in a sharp-ray completion")
        signs = {q: Taylor.sign(volume(*(subtract(r[i], r[q[0]]) for i in q[1:]))) for q in stable}
        if not any(abs(sum(factor*signs[q] for q, factor in circuit)) == 5 for circuit in circuits):
            return False
    return True


def verify(complex_):
    core = SharpCore(complex_)
    # The test uses the smaller root-pair deficit H - |h3*h4|, hence works for both root signs.
    core.check()
    norms = bracket_norms(core)
    pending = [(fmpq(0), fmpq(1), 0)]
    count = 0
    while pending:
        left, right, depth = pending.pop()
        if crossings_on_cell(core, norms, left, right):
            count += 1
            continue
        if depth == 16:
            raise ArithmeticError(f"could not certify a crossing on ({left}, {right}]")
        middle = (left+right)/2
        pending.extend(((left, middle, depth+1), (middle, right, depth+1)))
    print(f"Certified all 16 nonplanar folds and a crossing in each on the entire sharp ray ({count} cells).",
          flush=True)
