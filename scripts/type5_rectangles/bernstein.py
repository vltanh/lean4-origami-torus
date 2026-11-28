"""Rational functions of d,U and exact signs on (0,1/2] × (0,1]."""

from fractions import Fraction
from functools import cache
from math import comb, lcm

from flint import fmpq, fmpq_mpoly, fmpq_mpoly_ctx, fmpz_mat


RING = fmpq_mpoly_ctx.get(("d", "u"))


class Rational:
    """Reduced fractions of rational polynomials, with monic denominator."""

    def __init__(self, numerator, denominator=None):
        if not isinstance(numerator, fmpq_mpoly):
            value = Fraction(numerator)
            numerator = RING.constant(fmpq(value.numerator, value.denominator))
        if denominator is None:
            self.numerator, self.denominator = numerator, RING.constant(1)
            return
        if denominator.is_zero():
            raise ZeroDivisionError("identically zero polynomial divisor")
        divisor = numerator.gcd(denominator)
        denominator = denominator/divisor
        leading = denominator.leading_coefficient()
        self.numerator = (numerator/divisor)/leading
        self.denominator = denominator/leading

    @classmethod
    def _reduced(cls, numerator, denominator):
        # Callers preserve a monic denominator and coprimality.
        result = object.__new__(cls)
        result.numerator, result.denominator = numerator, denominator
        return result

    @staticmethod
    def coerce(value):
        return value if isinstance(value, Rational) else Rational(value)

    def __add__(self, other):
        other = self.coerce(other)
        if self.numerator.is_zero():
            return other
        if other.numerator.is_zero():
            return self
        common = self.denominator.gcd(other.denominator)
        left, right = self.denominator/common, other.denominator/common
        numerator = self.numerator*right + other.numerator*left
        cancel = numerator.gcd(common)
        return self._reduced(numerator/cancel, left*(other.denominator/cancel))

    __radd__ = __add__

    def __neg__(self):
        return self._reduced(-self.numerator, self.denominator)

    def __sub__(self, other):
        return self + -self.coerce(other)

    def __rsub__(self, other):
        return -self + other

    def __mul__(self, other):
        other = self.coerce(other)
        if self.numerator.is_zero() or other.numerator.is_zero():
            return Rational(0)
        first = self.numerator.gcd(other.denominator)
        second = other.numerator.gcd(self.denominator)
        return self._reduced((self.numerator/first)*(other.numerator/second),
                             (self.denominator/second)*(other.denominator/first))

    __rmul__ = __mul__

    def __truediv__(self, other):
        other = self.coerce(other)
        return Rational(self.numerator*other.denominator, self.denominator*other.numerator)

    def __rtruediv__(self, other):
        return self.coerce(other)/self

    def __pow__(self, exponent):
        return self._reduced(self.numerator**exponent, self.denominator**exponent)

    def at(self, d, u):
        value = self.numerator(d, u)/self.denominator(d, u)
        return Fraction(int(value.p), int(value.q))


@cache
def _bernstein_matrix(degree, scale):
    # Convert monomials in x/scale into degree-n Bernstein coefficients on [0,1].
    denominators = [comb(degree, i)*scale**i for i in range(degree+1)]
    multiplier = lcm(*denominators)
    return fmpz_mat([[comb(j, i)*(multiplier//denominators[i]) if i <= j else 0
                      for i in range(degree+1)] for j in range(degree+1)])


def polynomial_sign(polynomial):
    """Certify a sign only if every coefficient has that weak sign and the last is strict."""
    if polynomial.is_zero():
        raise ArithmeticError("expected a nonzero polynomial")
    m, n = polynomial.degrees()
    coefficients = polynomial.to_dict()
    scale = lcm(*(int(c.q) for c in coefficients.values()))
    power = fmpz_mat(m+1, n+1)
    for (i, j), c in coefficients.items():
        power[i, j] = c.p*(scale//c.q)
    table = _bernstein_matrix(m, 2) * power * _bernstein_matrix(n, 1).transpose()
    if table[m, n] > 0 and min(table.entries()) >= 0:
        return 1
    if table[m, n] < 0 and max(table.entries()) <= 0:
        return -1
    raise ArithmeticError("Bernstein coefficients do not certify a strict sign")


def positive(value):
    if polynomial_sign(value.numerator) != polynomial_sign(value.denominator):
        raise ArithmeticError("expected a strictly positive rational function")
