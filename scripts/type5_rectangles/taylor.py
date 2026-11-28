"""Taylor coefficients with dyadic enclosures for the remainder on [-1,1]."""

from functools import cached_property
from .interval import Interval, ZERO, interval_sum

UNIT_INTERVAL = Interval.between(-1, 1)


class Taylor:
    def __init__(self, coefficients, remainder):
        self.c = coefficients
        self.remainder = remainder

    @classmethod
    def variable(cls, left, right, order):
        c = [Interval.rational((left + right)/2), Interval.rational((right - left)/2)]
        return cls(c + [ZERO]*(order-2), ZERO)

    def constant(self, value):
        interval = value if isinstance(value, Interval) else Interval.rational(value)
        return Taylor([interval] + [ZERO]*(len(self.c)-1), ZERO)

    def _coerce(self, other):
        return other if isinstance(other, Taylor) else self.constant(other)

    @cached_property
    def tails(self):
        values = [self.remainder]
        for c in reversed(self.c):
            values.append(c + UNIT_INTERVAL*values[-1])
        return values[::-1]

    def __add__(self, other):
        other = self._coerce(other)
        return Taylor([a+b for a, b in zip(self.c, other.c, strict=True)],
                      self.remainder + other.remainder)

    __radd__ = __add__

    def __neg__(self):
        return Taylor([-a for a in self.c], -self.remainder)

    def __sub__(self, other):
        return self + -self._coerce(other)

    def __rsub__(self, other):
        return self._coerce(other) + -self

    def __mul__(self, other):
        other = self._coerce(other)
        n = len(self.c)
        c = [interval_sum(self.c[i]*other.c[j-i] for i in range(j+1)) for j in range(n)]
        remainder = interval_sum(self.c[i]*other.tails[n-i] for i in range(n))
        return Taylor(c, remainder + self.remainder*other.tails[0])

    __rmul__ = __mul__

    def __truediv__(self, other):
        other = self._coerce(other)
        n = len(self.c)
        c = []
        for j in range(n):
            c.append((self.c[j] - interval_sum(c[i]*other.c[j-i] for i in range(j))) / other.c[0])
        remainder = self.remainder - interval_sum(c[i]*other.tails[n-i] for i in range(n))
        return Taylor(c, remainder/other.tails[0])

    def __rtruediv__(self, other):
        return self._coerce(other) / self

    def __pow__(self, n):
        if n == 0:
            return self.constant(1)
        if n == 1:
            return self
        half = self**(n//2)
        square = half*half
        return square*self if n % 2 else square

    def sqrt(self):
        n = len(self.c)
        c = [self.c[0].sqrt()]
        bounds = [self.tails[0].sqrt()]
        for j in range(1, n+1):
            if j < n:
                known = interval_sum(c[i]*c[j-i] for i in range(1, j))
                c.append((self.c[j] - known)/(c[0]+c[0]))
            known = interval_sum(c[i]*bounds[j-i] for i in range(1, j))
            bounds.append((self.tails[j] - known)/(c[0]+bounds[0]))
        return Taylor(c, bounds[-1])

    def sign(self):
        return self.tails[0].sign()
