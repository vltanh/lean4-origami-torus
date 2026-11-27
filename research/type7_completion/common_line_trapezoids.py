#!/usr/bin/env python3
"""Exact zero-cone classification for common-line trapezoid blow-ups.

The quadratic inequality is the one proved in verify_cap_limit.py.
This checker additionally covers every possible zero support among its
extreme rays. See common_line_trapezoids.md for the geometric bridge.
"""

from collections import Counter
from itertools import combinations, product

import sympy as s

from verify_cap_limit import MASK


def main():
    if not __debug__:
        raise RuntimeError('run with assertions enabled')
    A, L, C, M, X, gap = variables = s.symbols('A L C M X gap')
    supports = Counter()
    patterns = set()
    cross_supports = rays_checked = pairs_checked = 0
    for orientation in (1, -1):
        U = X-A-M-gap if orientation == 1 else X+C+L+gap
        e = (X, L, A-L-X, -A)
        f = tuple(orientation*v for v in (U, M, C-M-U, -C))
        for signs in product((-1, 1), repeat=4):
            h = (signs[0]*X, L, signs[1]*(A-L-X), A)
            k = (signs[2]*U, M, signs[3]*(C-M-U), C)
            polynomial = s.expand(2*sum(MASK[i, j]*(h[i]*k[j]-e[i]*f[j])
                                      for i, j in product(range(4), repeat=2))
                                  - sum(h)*sum(k))
            inequalities = (A, L, C, M, gap, h[0], h[2], k[0], k[2])
            H = s.Matrix([[s.diff(value, v) for v in variables] for value in inequalities])
            assert H.rank() == 6
            rays = set()
            for active in combinations(range(9), 5):
                kernel = H[list(active), :].nullspace()
                if len(kernel) != 1:
                    continue
                for ray in (kernel[0], -kernel[0]):
                    if any(value < 0 for value in H*ray):
                        continue
                    denominator = s.ilcm(*(value.q for value in ray))
                    integer = tuple(int(value*denominator) for value in ray)
                    divisor = s.igcd(*integer)
                    rays.add(tuple(value//divisor for value in integer))
            rays = sorted(rays)
            assert len(rays) <= 8
            Q = s.hessian(polynomial, variables)/2
            assert s.expand((s.Matrix(variables).T*Q*s.Matrix(variables))[0]-polynomial) == 0
            products = [[(s.Matrix(a).T*Q*s.Matrix(b))[0] for b in rays] for a in rays]
            assert all(value >= 0 for row in products for value in row)
            rays_checked += len(rays)
            pairs_checked += len(rays)**2
            # Every point is a nonnegative combination of the rays. Since
            # all pair products are nonnegative, a zero can use only a
            # support whose every pair product vanishes, including the
            # diagonal products. Enumerate all those supports exactly.
            for bits in range(1, 1 << len(rays)):
                chosen = [i for i in range(len(rays)) if bits >> i & 1]
                if any(products[i][j] for i in chosen for j in chosen):
                    continue
                total = tuple(sum(rays[i][j] for i in chosen) for j in range(6))
                base_support = tuple(i for i in range(4) if total[i] > 0)
                supports[base_support] += 1
                assert len(base_support) <= 2
                if not (set(base_support) & {0, 1} and set(base_support) & {2, 3}):
                    continue
                cross_supports += 1
                assert len(base_support) == 2 and total[5] == 0
                av, lv, cv, mv, xv, gv = total
                uv = xv-av-mv-gv if orientation == 1 else xv+cv+lv+gv
                xa = (0, xv, xv+lv, av)
                xb = (0, orientation*uv, orientation*(uv+mv), orientation*cv)
                for vertices in (xa, xb):
                    assert sorted(Counter(vertices).values()) == [1, 3]
                zeros = tuple(tuple(i for i in range(4)
                                    if vertices[(i+1) % 4] == vertices[i])
                              for vertices in (xa, xb))
                # Zero lengths cannot arise by cancellation between rays:
                # the absolute edge steps h,k are fixed nonnegative linear
                # forms on this sign cone. Verify each zero on every ray,
                # establishing the cluster identities for arbitrary
                # positive coefficients, not just the unit-coefficient sum.
                for i in chosen:
                    substitution = dict(zip(variables, rays[i]))
                    for lengths, zero_edges in zip((h, k), zeros):
                        assert all(s.expand(lengths[j]).subs(substitution) == 0
                                   for j in zero_edges)
                patterns.add((orientation, *zeros))
    assert (rays_checked, pairs_checked) == (116, 652)
    assert cross_supports == 16
    assert patterns == {
        (-1, (0, 1), (1, 2)), (-1, (2, 3), (0, 3)),
        (1, (0, 3), (0, 1)), (1, (1, 2), (2, 3)),
    }
    print('PASS 32 pointed cones, 116 rays, 652 nonnegative ray products')
    print('PASS every zero support has at most two positive bases')
    print('PASS all 16 cross-cap zero supports force two triple-cluster/tip caps')
    print('Zero physical edge patterns:', sorted(patterns))
    print('Scope: conditional shape reduction; the triangle-pair module proves the exclusion')


if __name__ == '__main__':
    main()
