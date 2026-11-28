"""Univariate Taylor polynomials with a rigorous remainder on [-1,1], using Arb."""

from fractions import Fraction
from functools import cached_property

from flint import arb, arb_poly, arb_series, ctx, fmpq


UNIT = arb(0, 1)


def rational(value):
    value = Fraction(value)
    return arb(fmpq(value.numerator, value.denominator))


class BallTaylor:
    """Represents P(z) + z^n R(z), with R(z) in remainder and n = ctx.cap.

    Set the FLINT working precision and series cap before creating a variable
    and keep them fixed until its certificate has been checked.
    """

    def __init__(self, polynomial, remainder=0):
        self.polynomial = polynomial
        self.remainder = remainder

    @classmethod
    def variable(cls, left, right):
        return cls(arb_poly([rational((left+right)/2), rational((right-left)/2)]))

    @classmethod
    def constant(cls, value):
        return cls(arb_poly([rational(value)]))

    def coerce(self, value):
        return value if isinstance(value, BallTaylor) else self.constant(value)

    @cached_property
    def polynomial_range(self):
        return self.polynomial(UNIT)

    @cached_property
    def enclosure(self):
        return self.polynomial_range + UNIT*self.remainder

    def __add__(self, other):
        other = self.coerce(other)
        return BallTaylor(self.polynomial + other.polynomial, self.remainder + other.remainder)

    __radd__ = __add__

    def __neg__(self):
        return BallTaylor(-self.polynomial, -self.remainder)

    def __sub__(self, other):
        return self + -self.coerce(other)

    def __rsub__(self, other):
        return -self + other

    def __mul__(self, other):
        other = self.coerce(other)
        product = self.polynomial * other.polynomial
        remainder = (product.right_shift(ctx.cap)(UNIT) + self.remainder*other.enclosure
                     + self.polynomial_range*other.remainder)
        return BallTaylor(product.truncate(ctx.cap), remainder)

    __rmul__ = __mul__

    def __truediv__(self, other):
        other = self.coerce(other)
        if not other.sign():
            raise ValueError("divisor enclosure contains zero")
        quotient = arb_series(self.polynomial) / arb_series(other.polynomial)
        polynomial = arb_poly(quotient.coeffs())
        high = (polynomial*other.polynomial).right_shift(ctx.cap)(UNIT)
        remainder = (self.remainder - high - polynomial(UNIT)*other.remainder)/other.enclosure
        return BallTaylor(polynomial, remainder)

    def __rtruediv__(self, other):
        return self.coerce(other) / self

    def __pow__(self, n):
        if n < 0:
            return 1/self**-n
        if n == 0:
            return self.constant(1)
        if n == 1:
            return self
        half = self**(n//2)
        square = half*half
        return square*self if n % 2 else square

    def sqrt(self):
        if not self.enclosure > 0:
            raise ValueError("radicand enclosure reaches zero")
        polynomial = arb_poly(arb_series(self.polynomial).sqrt().coeffs())
        divisor = self.enclosure.sqrt() + polynomial(UNIT)
        if not divisor > 0:
            raise ValueError("square-root remainder divisor reaches zero")
        high = (polynomial*polynomial).right_shift(ctx.cap)(UNIT)
        return BallTaylor(polynomial, (self.remainder - high)/divisor)

    def sign(self):
        return int(self.enclosure > 0) - int(self.enclosure < 0)
