"""Normalized tails of convergent Laurent expansions on 0 < t <= radius."""

from functools import cache
from .interval import Interval, ZERO, ONE, interval_sum


class Laurent:
    def __init__(self, system, lower_order, coefficient, tail):
        self.system = system
        self.order = lower_order
        self._coefficient = cache(coefficient)
        self._tail = cache(tail)
        self.leading = cache(self._leading)
        self.tight_tail = cache(self._tight_tail)

    def coefficient(self, j):
        return self.system.field.constant(0) if j < self.order else self._coefficient(j)

    def tail(self, j):
        if j < self.order:
            return self.system.domain**(self.order-j) * self._tail(self.order)
        return self._tail(j)

    def _leading(self):
        field = self.system.field
        for j in range(self.order, self.order+120):
            c = self.coefficient(j)
            if not field.is_zero(c):
                return j, c
        raise ValueError("no leading coefficient certified")

    def _tight_tail(self, j):
        """Try higher-order tails when the direct enclosure is too wide."""
        field = self.system.field
        base, power = ZERO, ONE
        for k in range(j, j+10):
            bound = base + power*self.tail(k)
            if bound.sign() and bound.high-bound.low < min(abs(bound.low), abs(bound.high)):
                return bound
            base = base + power*field.enclosure(self.coefficient(k))
            power = power*self.system.domain
        return bound

    def sign(self):
        return self.tight_tail(self.leading()[0]).sign()

    def __add__(self, other):
        other = self.system.coerce(other)
        if self is self.system.zero:
            return other
        if other is self.system.zero:
            return self
        field = self.system.field
        return self.system.series(min(self.order, other.order),
            lambda j: field.add(self.coefficient(j), other.coefficient(j)),
            lambda j: self.tail(j)+other.tail(j))

    __radd__ = __add__

    def __neg__(self):
        if self is self.system.zero:
            return self
        field = self.system.field
        return Laurent(self.system, self.order, lambda j: field.neg(self.coefficient(j)),
                                  lambda j: -self.tail(j))

    def __sub__(self, other):
        other = self.system.coerce(other)
        return self.system.zero if self is other else self + -other

    def __rsub__(self, other):
        return self.system.coerce(other) + -self

    def __mul__(self, other):
        other = self.system.coerce(other)
        if self is self.system.zero or other is self.system.zero:
            return self.system.zero
        if self is self.system.one:
            return other
        if other is self.system.one:
            return self
        field = self.system.field
        n, m = self.order, other.order

        def coefficient(j):
            return self.system.sum(field.mul(self.coefficient(i), other.coefficient(j-i))
                                   for i in range(n, j-m+1))

        def tail(j):
            known = interval_sum(field.enclosure(self.coefficient(i))*other.tail(j-i)
                                 for i in range(n, j-m))
            return known + self.tail(j-m)*other.tail(m)

        return self.system.series(n+m, coefficient, tail)

    __rmul__ = __mul__

    def __truediv__(self, other):
        other = self.system.coerce(other)
        if other is self.system.one:
            return self
        field = self.system.field
        k, c = other.leading()
        denominator = other.tight_tail(k)
        if not denominator.sign():
            raise ValueError("uncertified leading divisor")
        if self is self.system.zero:
            return self
        reciprocal = field.inverse(c)
        n = self.order-k

        def coefficient(j):
            known = self.system.sum(field.mul(out.coefficient(i), other.coefficient(j+k-i))
                                    for i in range(n, j))
            return field.mul(reciprocal, field.add(self.coefficient(j+k), field.neg(known)))

        def tail(j):
            known = interval_sum(field.enclosure(out.coefficient(i))*other.tail(j+k-i)
                                 for i in range(n, j))
            return (self.tail(j+k) - known)/denominator

        # The coefficient recurrence uses only indices strictly below j.
        out = Laurent(self.system, n, coefficient, tail)
        return self.system.trim(out)

    def __rtruediv__(self, other):
        return self.system.coerce(other)/self

    def __pow__(self, n):
        if n < 0:
            return self.system.one / self**-n
        if n == 0:
            return self.system.constant(1)
        if n == 1:
            return self
        half = self**(n//2)
        square = half*half
        return square*self if n % 2 else square

    def sqrt(self):
        field = self.system.field
        k, c = self.leading()
        if k % 2:
            raise ValueError("the square root needs a fractional power")
        m = k//2
        base = self.tight_tail(k).sqrt()
        z = field.sqrt(c)
        reciprocal = field.inverse(field.add(z, z))

        def coefficient(j):
            if j == m:
                return z
            known = self.system.sum(field.mul(out.coefficient(i), out.coefficient(m+j-i))
                                    for i in range(m+1, j))
            return field.mul(reciprocal, field.add(self.coefficient(m+j), field.neg(known)))

        def tail(j):
            if j == m:
                return base
            known = interval_sum(field.enclosure(out.coefficient(i))*out.tail(m+j-i)
                                 for i in range(m+1, j))
            return (self.tail(m+j)-known)/(base+field.enclosure(z))

        out = Laurent(self.system, m, coefficient, tail)
        return out


class System:
    def __init__(self, field, radius):
        self.field = field
        self.domain = Interval.between(0, radius)
        self.constant = cache(self._constant)
        self.zero, self.one = self.constant(0), self.constant(1)
        self.t = Laurent(self, 1, lambda j: field.constant(int(j == 1)),
                         lambda j: ONE if j == 1 else ZERO)

    def sum(self, values):
        result = self.field.constant(0)
        for value in values:
            result = self.field.add(result, value)
        return result

    def trim(self, v):
        # Removing one exact zero keeps the convolution bounds small.
        n = v.order
        if self.field.is_zero(v.coefficient(n)):
            return Laurent(self, n+1, v.coefficient, v.tail)
        return v

    def series(self, order, coefficient, tail):
        return self.trim(Laurent(self, order, coefficient, tail))

    def lift(self, c):
        return Laurent(self, 0, lambda j: c if j == 0 else self.field.constant(0),
                       lambda j: self.field.enclosure(c) if j == 0 else ZERO)

    def _constant(self, value):
        return self.lift(self.field.constant(value))

    def coerce(self, value):
        return value if isinstance(value, Laurent) else self.constant(value)
