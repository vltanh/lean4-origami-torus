"""Exact coefficient identities and enclosures on one closed shear interval.

The coefficient expressions are real analytic on this interval. Each reciprocal
and positive square root is checked on the entire interval before use. An
identity can therefore be tested in the ordered field of germs at its midpoint.
The formal variable approaches that point from the right to give rational
functions (including those with a zero or a pole there) a well-defined sign.
"""

from __future__ import annotations

from fractions import Fraction
from functools import cached_property

from flint import fmpq, fmpq_poly
from flint.utils.flint_exceptions import DomainError

from .interval import Interval


def _fraction(value):
    return Fraction(int(value.numerator), int(value.denominator))


class _RationalFunction:
    """A reduced fraction of rational polynomials, with monic denominator."""

    __slots__ = ("numerator", "denominator")

    def __init__(self, numerator, denominator=None):
        if denominator is None:
            denominator = fmpq_poly([1])
        if not denominator:
            raise ZeroDivisionError("zero polynomial denominator")
        if not numerator:
            self.numerator, self.denominator = fmpq_poly(), fmpq_poly([1])
            return
        if denominator.degree() > 0:
            divisor = numerator.gcd(denominator)
            if divisor.degree() > 0:
                numerator, denominator = numerator / divisor, denominator / divisor
        scale = denominator.leading_coefficient()
        self.numerator = numerator / scale
        self.denominator = denominator / scale

    @classmethod
    def constant(cls, value):
        return cls(fmpq_poly([fmpq(int(value.numerator), int(value.denominator))]))

    def __add__(self, other):
        if self.denominator == other.denominator:
            return _RationalFunction(self.numerator + other.numerator, self.denominator)
        return _RationalFunction(self.numerator * other.denominator
                                 + other.numerator * self.denominator,
                                 self.denominator * other.denominator)

    def __neg__(self):
        return _RationalFunction(-self.numerator, self.denominator)

    def __mul__(self, other):
        return _RationalFunction(self.numerator * other.numerator,
                                 self.denominator * other.denominator)

    def inverse(self):
        return _RationalFunction(self.denominator, self.numerator)

    def square_root_candidate(self):
        try:
            return _RationalFunction(self.numerator.sqrt(), self.denominator.sqrt())
        except (DomainError, ValueError):
            return None


_ZERO = _RationalFunction.constant(0)
_ONE = _RationalFunction.constant(1)


class _Radical:
    """The expression a + b*sqrt(r), with r at this level of the tower."""

    __slots__ = ("level", "a", "b")

    def __init__(self, level, a, b):
        self.level, self.a, self.b = level, a, b


def _level(value):
    return value.level if isinstance(value, _Radical) else 0


def _parts(value, level):
    return (value.a, value.b) if _level(value) == level else (value, _ZERO)


def _obvious_zero(value):
    return isinstance(value, _RationalFunction) and not value.numerator


def _radical(level, a, b):
    return a if _obvious_zero(b) else _Radical(level, a, b)


class _Coefficient:
    def __init__(self, exact, enclose, scalar=None):
        self.scalar = scalar
        self._exact = exact
        self._enclose = enclose

    @cached_property
    def exact(self):
        return self._exact()

    @cached_property
    def interval(self):
        return self._enclose()


class ShearArithmetic:
    """Arithmetic on a connected dyadic shear interval, local to this instance."""

    def __init__(self, x_interval):
        if x_interval.low > x_interval.high:
            raise ValueError("empty shear interval")
        self._x = x_interval
        self._zero = Interval.rational(0)
        self._one = Interval.rational(1)
        midpoint = Fraction(x_interval.low + x_interval.high, 2 * self._one.low)
        self._midpoint = fmpq(int(midpoint.numerator), int(midpoint.denominator))
        self._constants = {}
        self._roots = []
        self._root_bounds = []

    def constant(self, value):
        value = Fraction(value)
        if value not in self._constants:
            self._constants[value] = _Coefficient(lambda: _RationalFunction.constant(value),
                                                  lambda: Interval.rational(value), value)
        return self._constants[value]

    def variable(self):
        if self._x.low == self._x.high:
            return self.constant(_fraction(self._midpoint))
        return _Coefficient(lambda: _RationalFunction(fmpq_poly([0, 1])), lambda: self._x)

    def _polynomial_sign(self, polynomial):
        while polynomial:
            value = polynomial(self._midpoint)
            if value:
                return 1 if value > 0 else -1
            polynomial = polynomial.derivative()
        return 0

    def _neg(self, x):
        if isinstance(x, _RationalFunction):
            return -x
        return _radical(x.level, self._neg(x.a), self._neg(x.b))

    def _add(self, x, y):
        if _obvious_zero(x):
            return y
        if _obvious_zero(y):
            return x
        level = max(_level(x), _level(y))
        if level == 0:
            return x + y
        a, b = _parts(x, level)
        c, d = _parts(y, level)
        return _radical(level, self._add(a, c), self._add(b, d))

    def _mul(self, x, y):
        if _obvious_zero(x) or _obvious_zero(y):
            return _ZERO
        level = max(_level(x), _level(y))
        if level == 0:
            return x * y
        a, b = _parts(x, level)
        c, d = _parts(y, level)
        radicand = self._roots[level - 1]
        return _radical(level,
                        self._add(self._mul(a, c), self._mul(self._mul(b, d), radicand)),
                        self._add(self._mul(a, d), self._mul(b, c)))

    def _norm(self, x):
        radicand = self._roots[x.level - 1]
        return self._add(self._mul(x.a, x.a), self._neg(self._mul(self._mul(x.b, x.b), radicand)))

    def _sign(self, x):
        if isinstance(x, _RationalFunction):
            return self._polynomial_sign(x.numerator) * self._polynomial_sign(x.denominator)
        a_sign, b_sign = self._sign(x.a), self._sign(x.b)
        if not b_sign:
            return a_sign
        if not a_sign or a_sign == b_sign:
            return b_sign
        # Compare a^2 to b^2*r in the preceding field of the tower.
        return a_sign * self._sign(self._norm(x))

    def _inverse(self, x):
        if isinstance(x, _RationalFunction):
            return x.inverse()
        norm = self._norm(x)
        if self._sign(norm) == 0:
            # x was proved nonzero. Its conjugate must vanish, so x = 2a.
            return self._inverse(self._add(x.a, x.a))
        reciprocal_norm = self._inverse(norm)
        return _radical(x.level, self._mul(x.a, reciprocal_norm),
                        self._neg(self._mul(x.b, reciprocal_norm)))

    def _sqrt(self, x, positive_root_bounds):
        if isinstance(x, _RationalFunction):
            candidate = x.square_root_candidate()
            if candidate is not None:
                # x is positive throughout the cell. The reduced candidate has
                # no poles or zeros there, so its sign is constant.
                return candidate if self._sign(candidate) > 0 else -candidate
        try:
            simplified = self._symbolic_bounds(x).sqrt()
        except ValueError:
            pass
        else:
            positive_root_bounds = positive_root_bounds.intersection(simplified)
        self._roots.append(x)
        self._root_bounds.append(positive_root_bounds)
        return _radical(len(self._roots), _ZERO, _ONE)

    def _horner(self, polynomial):
        result = self._zero
        for i in range(polynomial.degree(), -1, -1):
            result = result * self._x + Interval.rational(_fraction(polynomial[i]))
        return result

    def _symbolic_bounds(self, x):
        if isinstance(x, _RationalFunction):
            return self._horner(x.numerator) / self._horner(x.denominator)
        return self._symbolic_bounds(x.a) + self._symbolic_bounds(x.b) * self._root_bounds[x.level - 1]

    def _operation(self, exact, natural):
        # Natural and simplified forms can lose precision at different points.
        # Only intersect when the symbolic rational denominators are certified.
        def enclosure():
            bound = natural()
            width = bound.high - bound.low
            if width == 0 or (bound.sign() and width * 32 < min(abs(bound.low), abs(bound.high))):
                return bound
            try:
                simplified = self._symbolic_bounds(value.exact)
            except (ArithmeticError, ValueError, AssertionError):
                return bound
            return bound.intersection(simplified)
        value = _Coefficient(exact, enclosure)
        return value

    def add(self, a, b):
        if a.scalar == 0:
            return b
        if b.scalar == 0:
            return a
        if a.scalar is not None and b.scalar is not None:
            return self.constant(a.scalar + b.scalar)
        return self._operation(lambda: self._add(a.exact, b.exact),
                               lambda: a.interval + b.interval)

    def neg(self, a):
        if a.scalar is not None:
            return self.constant(-a.scalar)
        return self._operation(lambda: self._neg(a.exact), lambda: -a.interval)

    def mul(self, a, b):
        if a.scalar == 0 or b.scalar == 1:
            return a
        if b.scalar == 0 or a.scalar == 1:
            return b
        if a.scalar is not None and b.scalar is not None:
            return self.constant(a.scalar * b.scalar)
        return self._operation(lambda: self._mul(a.exact, b.exact),
                               lambda: a.interval * b.interval)

    def inverse(self, a):
        if a.interval.sign() == 0:
            raise ValueError("coefficient divisor is not separated from zero on this shear interval")
        return self._operation(lambda: self._inverse(a.exact), lambda: self._one / a.interval)

    def sqrt(self, a):
        if a.interval.low <= 0:
            raise ValueError("coefficient radicand is not strictly positive on this shear interval")
        positive_root_bounds = a.interval.sqrt()
        return self._operation(lambda: self._sqrt(a.exact, positive_root_bounds),
                               lambda: positive_root_bounds)

    def is_zero(self, a):
        if a.interval.sign():
            return False
        if a.interval.low == a.interval.high == 0:
            return True
        return self._sign(a.exact) == 0

    def enclosure(self, a):
        return a.interval
