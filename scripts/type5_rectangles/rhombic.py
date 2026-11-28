"""Certify the reduced equal-length arc and a sector approaching the hexagon."""

from fractions import Fraction as F

from flint import ctx

from .ball_taylor import BallTaylor
from .chart import add, cross, dot, norm_sq, scale, subtract
from .interval import Interval
from .laurent import Laurent, System
from .shear import ShearArithmetic


TIP = (F(1, 4), F(3, 2), F(1, 16), F(1, 16), F(1, 2), F(1, 16), F(-1, 8), F(1, 16))
MIDDLE = (F(7, 32), F(1, 8), F(1, 256), F(1, 256), F(19, 32), F(1, 64), F(-5, 32), F(1, 64))
SQUARE = (F(9, 32), F(1, 8), F(1, 128), F(1, 512), F(9, 16), F(1, 32), F(-1, 8), F(1, 2048))


def core(complex_, delta, x, y, parameters):
    one = delta**0
    half = one/2
    length_sq = x*x + y*y
    width, gap, lift2, inset3, lift5, slack, horizontal, perturb = parameters
    w = delta - width*delta**2
    q = w-half
    d = lift5*delta
    b = (-q-slack*delta**5)/(one-2*d/length_sq)

    def point(first, projection):
        return first, (projection-x*first)/y

    p = {1: (0, 0),
         2: point(w-gap*delta**3, -length_sq/2 + lift2*delta**10),
         3: point(half-inset3*delta**9, b),
         5: point(q, -length_sq/2+d)}
    period, _, project = complex_.anchor_geometry(p, x, y)

    def reflect(v):
        return subtract(scale(2*dot(p[2], v)/norm_sq(p[2]), p[2]), v)

    # A height-zero leaf 0 on the reflected side of the line through 1 and 2.
    e = subtract(reflect(p[5]), add(p[5], period(0, 5)))
    f = subtract(reflect(project(3, p[3])), p[3])
    leaf = scale(-w/cross(e, f), (f[1], -f[0]))
    reflected = reflect(leaf)
    shift = period(4, 0)

    def residual(v):
        return (dot(project(4, v), reflected) - dot(leaf, subtract(v, shift))
                - dot(v, shift) + norm_sq(shift)/2)

    # The leaf-to-4 squared distance equality is affine in the core point v.
    intercept = residual((0, 0))
    slope_x = residual((1, 0)) - intercept
    slope_y = residual((0, 1)) - intercept
    height = -(slope_x*horizontal+intercept)/slope_y
    p[4] = (horizontal, height + perturb*delta**4/y)
    return p


def compact(complex_, left, right, order, parameters):
    # All models used in a cell have the same truncation order.
    count = 0
    stack = [(left, right, 0)]
    old_cap = ctx.cap
    try:
        ctx.cap = order
        with ctx.workprec(max(512, 16*order)):
            while stack:
                lo, hi, depth = stack.pop()
                delta = BallTaylor.variable(lo, hi)
                x = F(1, 2) - delta
                try:
                    y = (1-x*x).sqrt()
                    p = core(complex_, delta, x, y, parameters)
                    placement = complex_.reconstruct(p, x, y, BallTaylor.sqrt)
                    if complex_.certifies_embedding(*placement, BallTaylor.sign):
                        count += 1
                        continue
                except ValueError:
                    pass  # A failed enclosure can be retried on smaller intervals.
                if depth == 16:
                    raise ArithmeticError(f"uncertified equal-length cell [{lo}, {hi}]")
                mid = (lo+hi)/2
                stack.extend([(mid, hi, depth+1), (lo, mid, depth+1)])
    finally:
        ctx.cap = old_cap
    return count


def verify(complex_):
    # delta=t^2 permits ordinary integral Laurent orders for every radical.
    field = ShearArithmetic(Interval.between(0, F(1, 2**16)))
    system = System(field, F(1, 4096))
    delta = system.t**2
    slope = system.lift(field.variable())
    x = F(1, 2) - delta
    y = (1+slope*delta-x*x).sqrt()
    p = core(complex_, delta, x, y, TIP)
    placement = complex_.reconstruct(p, x, y, Laurent.sqrt)
    if not complex_.certifies_embedding(*placement, Laurent.sign):
        raise ArithmeticError("hexagonal sector sign check failed")
    print("Certified 0 < delta <= 2^-24, 1 <= x²+y² <= 1+delta/65536.", flush=True)

    count = 0
    for exponent in range(2, 24):
        count += compact(complex_, F(1, 2**(exponent+1)), F(1, 2**exponent),
                         2*exponent+10, MIDDLE)
    count += compact(complex_, F(1, 4), F(7, 16), 12, MIDDLE)
    count += compact(complex_, F(7, 16), F(1, 2), 12, SQUARE)
    print(f"Certified the rest of the equal-length arc in {count} closed intervals.", flush=True)
