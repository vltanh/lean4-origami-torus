#!/usr/bin/env python3
"""Exact algebra for the regular C1 turning-angle exclusion of ray 1.

The analytic argument is in the accompanying note. Its topology inputs
are the independently replayed regular-cap C1 formulas, and its metric
inputs are the closed circle/dot identities. No finite height is claimed.
"""

import json

import sympy as sym

import exhaustive_c1_angles as topology
import solver_remaining_c1_geometry as geometry


def exact_checks():
    geometry.verify()
    topology.exact_geometry()
    p, q, alpha, sigma, cosine = sym.symbols('p q alpha sigma cosine')
    h, k, r, a, ell, t = sym.symbols('h k r a ell t')
    s = p+q
    sig = sym.Rational(1, 2)+(1-alpha)*p-alpha*q
    norm2 = sig**2-2*(1-alpha)*p
    w = alpha*p+(1-alpha)*q
    assert sym.expand(norm2-(sym.Rational(1, 2)-s)**2
                      -w*(1-2*s)-(alpha*p-(1-alpha)*q)**2) == 0

    # The first angle difference is positive, with no division by p or q.
    hvalue, kvalue = sym.Rational(1, 2)-r, sym.Rational(1, 2)-t
    assert sym.expand(hvalue*kvalue-q*kvalue-p*hvalue
                      -(sym.Rational(1, 2)*(sym.Rational(1, 2)-s-r-t)
                        +r*t+p*r+q*t)) == 0

    # A Gram determinant for Y0 and the two unit directions vanishes.
    norm_in_sigma = sigma**2-2*p*sigma/s+2*p*(sym.Rational(1, 2)-q)/s
    assert sym.cancel(norm_in_sigma.subs(sigma, sig)-norm2) == 0
    first, second = 1-q/h-sigma, p/k-sigma
    gram = sym.expand(norm_in_sigma*(1-cosine**2)-first**2-second**2
                      +2*cosine*first*second)
    discriminant = sym.factor(sym.discriminant(gram, sigma))
    obstruction = h*k*((1-2*s)*cosine+1+2*s)-2*s*(h+k-s)
    expected = -4*p*q*(cosine-1)**2*(cosine+1)*obstruction/(h*k*s**2)
    assert sym.cancel(discriminant-expected) == 0
    assert sym.expand(gram.coeff(sigma, 2)+(1-cosine)**2) == 0

    S, R, L, H = sym.symbols('S R L H')
    U = (2*S*(h+k-S)-h*k*(1+2*S))/(h*k*(1-2*S))
    # Direct bounds replace the discriminant when one deficit vanishes.
    assert sym.cancel(U-(-1+2*S/h)
                      -2*S*(h-S)*(1-2*k)/(h*k*(1-2*S))) == 0
    assert sym.cancel(U-(-1+2*S/k)
                      -2*S*(k-S)*(1-2*h)/(h*k*(1-2*S))) == 0

    # Half-angle formula for a perimeter-one cap triangle.
    side1, side2, side3 = sym.Rational(1, 2)-r, sym.Rational(1, 2)-a, r+a
    cap_cosine = (side1**2+side2**2-side3**2)/(2*side1*side2)
    assert sym.cancel((1-cap_cosine)/(1+cap_cosine)
                      -2*r*a/(sym.Rational(1, 2)-r-a)) == 0

    Lmax = sym.Rational(1, 2)-S-R
    H0 = sym.Rational(1, 4)-R/2
    bound = (2*S*(1-R-S)-H*(1+2*S))/(H*(1-2*S))
    bound0 = bound.subs(H, H0)
    assert sym.cancel(bound0-bound
                      -2*S*(1-R-S)*(H-H0)/(H0*H*(1-2*S))) == 0
    merged_cosine = (S-2*R*Lmax)/(S+2*R*Lmax)
    assert sym.cancel(merged_cosine-bound0
                      -4*S*Lmax/((S+R)*(1-2*R))) == 0
    assert sym.expand(hvalue*kvalue-(sym.Rational(1, 4)-(r+t)/2)-r*t) == 0

    # The same strict dot-projection gap is used for the second pair.
    p2, q2, r2, t2 = sym.symbols('p2 q2 r2 t2')
    h2, k2 = sym.Rational(1, 2)-r2, sym.Rational(1, 2)-t2
    assert sym.expand(h2*k2-q2*k2-p2*h2
                      -(sym.Rational(1, 2)*(sym.Rational(1, 2)-p2-q2-r2-t2)
                        +r2*t2+p2*r2+q2*t2)) == 0

    # Raw bracket [3467] has the orientation used in the turning argument.
    points = [sym.Matrix(sym.symbols(f'x{i} y{i}')) for i in range(8)]
    heights = [0, alpha/2, sym.Rational(1, 2), sym.Rational(1, 2),
               sym.Rational(1, 2), 0, 0, 0]
    spatial = [point.col_join(sym.Matrix([height])) for point, height in zip(points, heights)]
    bracket = sym.Matrix.hstack(*(spatial[i]-spatial[3] for i in (4, 6, 7))).det()
    cross = sym.Matrix.hstack(points[4]-points[3], points[7]-points[6]).det()
    assert sym.expand(2*bracket-cross) == 0
    return {'metric_and_orientation_sources_replayed': True,
            'positive_norm_factorization': True, 'gram_discriminant_factorization': True,
            'zero_deficit_bounds': 2, 'strict_turning_gap_factorization': True,
            'conclusion': 'ray 1 cannot have regular C1 caps with 0<alpha,beta<1',
            'finite_height_bound': None,
            'remaining_boundaries': ['a collinear endpoint cap', 'alpha=1', 'beta=0 or beta=1']}


if __name__ == '__main__':
    if not __debug__:
        raise RuntimeError('run with assertions enabled')
    print(json.dumps(exact_checks()), flush=True)
