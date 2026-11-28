"""Outward-rounded closed intervals with a common dyadic denominator."""

from fractions import Fraction
from math import isqrt


class Interval:
    precision = 256
    unit = 1 << precision
    __slots__ = ("low", "high")

    def __init__(self, low, high):
        if low > high:
            raise ValueError("empty interval")
        self.low, self.high = low, high

    @classmethod
    def rational(cls, value):
        value = Fraction(value)
        numerator = value.numerator * cls.unit
        return cls(numerator // value.denominator, -(-numerator // value.denominator))

    @classmethod
    def between(cls, left, right):
        return cls(cls.rational(left).low, cls.rational(right).high)

    def __add__(self, other):
        return Interval(self.low + other.low, self.high + other.high)

    def __neg__(self):
        return Interval(-self.high, -self.low)

    def __sub__(self, other):
        return Interval(self.low - other.high, self.high - other.low)

    def __mul__(self, other):
        products = (self.low * other.low, self.low * other.high,
                    self.high * other.low, self.high * other.high)
        return Interval(min(products) >> self.precision, -(-max(products) >> self.precision))

    def __truediv__(self, other):
        if other.sign() == 0:
            raise ValueError("the divisor enclosure contains zero")
        scale = self.unit ** 2
        return self * Interval(scale // other.high, -(-scale // other.low))

    def __pow__(self, exponent):
        if exponent < 0:
            return ONE / self ** -exponent
        if exponent == 0:
            return ONE
        half = self ** (exponent // 2)
        result = half * half
        return result * self if exponent % 2 else result

    def sqrt(self):
        if self.low <= 0:
            raise ValueError("the radicand enclosure is not strictly positive")
        return Interval(isqrt(self.low * self.unit), 1 + isqrt(self.high * self.unit - 1))

    def intersection(self, other):
        return Interval(max(self.low, other.low), min(self.high, other.high))

    def sign(self):
        """Zero denotes an interval containing zero."""
        return int(self.low > 0) - int(self.high < 0)


ZERO = Interval.rational(0)
ONE = Interval.rational(1)


def interval_sum(values):
    low = high = 0
    for value in values:
        low += value.low
        high += value.high
    return Interval(low, high)
