#!/usr/bin/env python3
"""Exact metric and polynomial checks for the ray-1 C0 height order u>=v.

The companion proves the angle branches and continuity argument.  This
script binds the metric identities to all 29 source rows and checks a
strict polynomial inequality by exact simplex/Bernstein coefficients.
No numerical solver or optimizer is used.
"""

from collections import defaultdict
from fractions import Fraction
from functools import lru_cache
from itertools import product
import json
from math import comb
import time

import sympy as sym

import solver_remaining_c1_geometry as geometry
import solver_remaining_limit as reduction


def metric_bindings():
    u, v = sym.symbols('u v')
    h = list(sym.symbols('h0:7'))
    h.append(sym.Rational(7, 2) - sum(h))
    d = [sym.Rational(1, 2) - value for value in h]
    P = [sym.zeros(2, 1), sym.zeros(2, 1)]
    P.extend(sym.Matrix(sym.symbols(f'x{i} y{i}')) for i in range(2, 8))
    X = geometry.horizontal_displacements(h)
    T = {edge: sym.expand((P[edge[1]] - P[edge[0]]).dot(P[edge[1]] - P[edge[0]]) - value**2)
         for edge, value in X.items()}
    formal = sym.symbols('T0:24')
    formal_T = dict(zip(reduction.EDGES, formal))
    lu, lv = 1 - 2*u, 1 - 2*v

    def stresses(t):
        return [2*u*t[3, 4] + lu*t[4, 6] - 2*u*lu*t[3, 6],
                2*v*t[3, 5] + lv*t[5, 6] - 2*v*lv*t[3, 6],
                t[4, 5] - 2*u*t[3, 5] - lu*t[5, 6] - 2*v*t[3, 4] - lv*t[4, 6]
                + (2*u*lv + 2*v*lu)*t[3, 6],
                lv*(t[2, 4] - t[3, 4]) - lu*(t[2, 5] - t[3, 5]),
                v*(t[4, 7] - t[4, 6]) - u*(t[5, 7] - t[5, 6])]

    rows = []
    for index, expression in enumerate(stresses(formal_T)):
        row = [sym.diff(expression, variable) for variable in formal] + [sym.Integer(0)]*5
        if index == 3:
            row[25] = -1
        if index == 4:
            row[28] = sym.Rational(1, 2)
        rows.append(row)
    for edge in ((2, 3), (6, 7)):
        rows.append([sym.Integer(edge == other) for other in reduction.EDGES] + [sym.Integer(0)]*5)
    original = reduction.original_system((sym.Rational(1, 2),)*3 + (1-u, -v, 0))
    assert all(sym.expand(value) == 0 for value in sym.Matrix(rows)*original)

    D = h[3] + h[4] + h[5] - 1
    assert sym.expand(D - (d[0] + d[1] + d[2] + d[6] + d[7])) == 0
    r, s = h[3] - lu*D, h[5] - 2*v*D
    Q4 = P[4] - 2*u*P[3] - lu*P[6]
    Q5 = P[5] - 2*v*P[3] - lv*P[6]
    U, V, J, C, K = stresses(T)
    assert sym.expand(Q4.dot(Q4) - r*r - U) == 0
    assert sym.expand(Q5.dot(Q5) - s*s - V) == 0
    assert sym.expand(2*(Q4.dot(Q5) + r*s - d[4]) + J) == 0
    S, W = lv*Q4 - lu*Q5, v*Q4 - u*Q5
    E, F = P[3] - P[2], P[7] - P[6]
    js = E.dot(S) - h[2]*(lv*r + lu*s) + lv*(h[2] - d[3])
    jw = F.dot(W) - h[6]*(v*r + u*s) + u*(h[6] - d[5])
    assert sym.expand(2*js - C + 2*(u-v)*T[2, 3]) == 0
    assert sym.expand(2*jw + K - (v-u)*T[6, 7]) == 0

    levels = (0, sym.Rational(1, 2), sym.Rational(1, 2), sym.Rational(1, 2), u, v, 0, 0)
    points = [point.col_join(sym.Matrix([height])) for point, height in zip(P, levels)]

    def bracket(quad):
        first, *rest = quad
        return sym.Matrix.hstack(*(points[i] - points[first] for i in rest)).det()

    cross = lambda a, b: sym.Matrix.hstack(a, b).det()
    assert sym.expand(2*bracket((2, 3, 4, 5)) + cross(E, S)) == 0
    assert sym.expand(bracket((4, 5, 6, 7)) + cross(W, F)) == 0
    assert sym.expand(2*bracket((3, 4, 5, 6)) + cross(Q4, Q5)) == 0
    assert sym.expand(cross(S, W) - (v-u)*cross(Q4, Q5)) == 0
    return {'full_source_stresses': 7, 'metric_identities': 5, 'determinant_identities': 4}


def angle_identities():
    h, j, e, f, g, k, l = sym.symbols('h j e f g k l')
    half = sym.Rational(1, 2)
    sigma, tau = half-e+k*(e+f), half-g+l*(f+g)
    ns, nw = sigma*sigma-2*k*f, tau*tau-2*l*f
    a, b = 1-sigma-e/h, 1-tau-g/j
    c = sigma*tau-(1+k*l)*f
    assert sym.cancel(ns-a*a-e/h**2*((h-e)*(1-2*h)+2*k*h*(h-e-f))) == 0
    assert sym.cancel(nw-b*b-g/j**2*((j-g)*(1-2*j)+2*l*j*(j-f-g))) == 0
    for parameter, q, n in ((k, e, ns), (l, g, nw)):
        gap = (((1-parameter)*f+parameter*q)*(1-2*(f+q))
               + ((1-parameter)*f-parameter*q)**2)
        assert sym.expand(n-(half-f-q)**2-gap) == 0
    r, s = sym.symbols('r s')
    assert sym.expand(((r+k*s)**2-2*k*f)*((l*r+s)**2-2*l*f)
                      - ((r+k*s)*(l*r+s)-(1+k*l)*f)**2
                      - (1-k*l)**2*f*(2*r*s-f)) == 0
    w = sym.Symbol('w')
    D = half-e-f-g
    r0, s0 = f+g+w*D, half-g-w*D
    gap = (1-w)*g*(half-f-g)+w*e*(half-e-f)+w*(1-w)*D*D
    assert sym.expand(r0*s0-f/2-gap) == 0
    # The normalized S,W scalar identities follow directly from k=lu/lv,
    # l=v/u. This also checks the correct factors of two.
    u, v = sym.symbols('u v')
    actual_r, actual_s = half-e-(1-2*u)*D, half-g-2*v*D
    kk, ll = (1-2*u)/(1-2*v), v/u
    assert sym.cancel(actual_r+kk*actual_s-sigma.subs(k, kk)) == 0
    assert sym.cancel(ll*actual_r+actual_s-tau.subs(l, ll)) == 0
    return {'positive_norm_bounds': 2, 'cosine_range_factorizations': 3,
            'height_ratio_bindings': 2}


@lru_cache(maxsize=None)
def multinomial_terms(degree, dimension=6):
    if dimension == 1:
        return (((degree,), 1),)
    return tuple(((first,)+rest, comb(degree, first)*coefficient)
                 for first in range(degree+1)
                 for rest, coefficient in multinomial_terms(degree-first, dimension-1))


def positive_gram_certificate():
    # The six nonnegative simplex variables are twice the deficits:
    # b=2(d0+d1+d7), d2,...,d6=2 times the corresponding d_i.
    variables = sym.symbols('b d2 d3 d4 d5 d6')
    b0, d2, d3, d4, d5, d6 = variables
    k, l = sym.symbols('k l')
    h, j = (1-d2)/2, (1-d6)/2
    e, f, g = d3/2, d4/2, d5/2
    sigma, tau = sym.Rational(1, 2)-e+k*(e+f), sym.Rational(1, 2)-g+l*(f+g)
    ns, nw, c = sigma*sigma-2*k*f, tau*tau-2*l*f, sigma*tau-(1+k*l)*f
    a, b = (1-sigma)*h-e, (1-tau)*j-g
    polynomial = sym.Poly(sym.expand(a*a*j*j*nw+b*b*h*h*ns+c*c*h*h*j*j
                                    +2*a*b*h*j*c-ns*nw*h*h*j*j), *variables, k, l)
    denominator, integer = polynomial.clear_denoms()
    assert denominator == 64
    powers = integer.terms()
    degree = max(sum(exponent[:6]) for exponent, _ in powers)
    assert degree == 8 and len(powers) == 530
    assert all(exponent[-2] <= 2 and exponent[-1] <= 2 for exponent, _ in powers)

    # Verify the exact power-to-Bernstein conversion separately in one
    # variable. The product identity applies independently to k and l.
    z = sym.Symbol('z')
    for exponent in range(3):
        expansion = sum(sym.Rational(comb(i, exponent), comb(2, exponent))
                        *comb(2, i)*z**i*(1-z)**(2-i) for i in range(exponent, 3))
        assert sym.expand(expansion-z**exponent) == 0

    counts = []
    for i, j0 in product(range(3), repeat=2):
        coefficients = defaultdict(Fraction)
        for exponent, coefficient in powers:
            ka, la = exponent[-2:]
            if ka > i or la > j0:
                continue
            weight = Fraction(int(coefficient)*comb(i, ka)*comb(j0, la), comb(2, ka)*comb(2, la))
            # Homogenize each simplex monomial with (b+d2+...+d6)^n.
            # This is exactly one on the deficit simplex.
            for extra, multiplicity in multinomial_terms(degree-sum(exponent[:6])):
                monomial = tuple(exponent[t]+extra[t] for t in range(6))
                coefficients[monomial] += weight*multiplicity
        coefficients = {power: value for power, value in coefficients.items() if value}
        assert all(sum(power) == 8 and value > 0 for power, value in coefficients.items())
        assert coefficients[(8, 0, 0, 0, 0, 0)] == 1
        counts.append(len(coefficients))
    assert counts == [1144, 1144, 1143, 1144, 1144, 1123, 1143, 1123, 1040]
    return {'simplex_degree': 8, 'bernstein_degrees': [2, 2],
            'nonnegative_coefficient_checks': sum(counts),
            'strict_b8_coefficient_in_each_of_nine_blocks': 1,
            'lower_bound': '64*h2^2*h6^2*nS^2*nW^2*GramGap >= (2*(d0+d1+d7))^8 > 0'}


def verify():
    return {'metric': metric_bindings(), 'angle': angle_identities(),
            'positive_gram': positive_gram_certificate(),
            'analytic_consequence': 'for u>=v, actual [2345]>0 or [4567]>0',
            'topological_height_order_companion_required': True,
            'v_greater_than_u_or_degenerate_caps_excluded': False}


if __name__ == '__main__':
    if not __debug__:
        raise RuntimeError('run with assertions enabled')
    started = time.monotonic()
    result = verify()
    result['seconds'] = round(time.monotonic()-started, 3)
    print(json.dumps(result), flush=True)
