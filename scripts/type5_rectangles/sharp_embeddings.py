"""Certify the embedded Type 5 family on the open sharp ray."""

from fractions import Fraction as F

from flint import ctx

from .ball_taylor import BallTaylor
from .interval import Interval
from .laurent import Laurent, System
from .shear import ShearArithmetic


def placement(complex_, y, t, u, constant, sqrt):
    """Here t = y² - 3/4, u = t/(1+2t) and the periods are (1,0), (1/2,y)."""
    half = constant(F(1, 2))
    s = constant(F(-3, 20))
    g = constant(F(147, 62410)) * (1 + u/4)
    h = constant(F(1, 100))
    beta = u**2 * (h + 2*s*g + constant(F(9, 400))*u)
    split = u**4/16384
    t_norm = 1 + t

    def point(x, dot_b):
        return x, (dot_b-half*x)/y

    core = {1: (0, 0),
            2: point(s, -t_norm/2 + split),
            3: point(half - g*u**2, beta - s),
            4: point(s - h*u**2, t_norm*(half + s - u/10)),
            5: point(u/36 - half, -t_norm/2 + 3*split)}
    return complex_.reconstruct(core, half, y, sqrt, root4=1, leaf_signs=(1, -1, 1))


def from_height_parameter(complex_, t, constant, sqrt):
    return placement(complex_, sqrt(t + F(3, 4)), t, t/(1+2*t), constant, sqrt)


def verify(complex_):
    # Both Laurent domains exclude zero and include their positive endpoints.
    field = ShearArithmetic(Interval.rational(0))
    near = System(field, F(1, 1024))
    points = from_height_parameter(complex_, near.t, near.constant, Laurent.sqrt)
    if not complex_.certifies_embedding(*points, Laurent.sign):
        raise ArithmeticError("uncertified sharp-ray family near the hexagon")

    far = System(field, F(1, 64))
    v = far.t  # v = 1/sqrt(t), so u = 1/(2+v²).
    y = (1 + F(3, 4)*v**2).sqrt()/v
    points = placement(complex_, y, 1/v**2, 1/(2+v**2), far.constant, Laurent.sqrt)
    if not complex_.certifies_embedding(*points, Laurent.sign):
        raise ArithmeticError("uncertified sharp-ray family near the cusp")

    ctx.prec, ctx.cap = 448, 12
    stack = [(F(2)**i, F(2)**(i+1), 0) for i in range(-10, 12)]
    count = 0
    while stack:
        left, right, depth = stack.pop()
        t = BallTaylor.variable(left, right)
        try:
            points = from_height_parameter(complex_, t, BallTaylor.constant, BallTaylor.sqrt)
            if complex_.certifies_embedding(*points, BallTaylor.sign):
                count += 1
                continue
        except ValueError:
            pass
        if depth >= 22:
            raise ArithmeticError(f"uncertified sharp-ray parameter interval [{left}, {right}]")
        middle = (left+right)/2
        stack.extend([(left, middle, depth+1), (middle, right, depth+1)])
    print(f"Certified every sharp height y > sqrt(3)/2 ({count} intervals and both Laurent bounds).",
          flush=True)
