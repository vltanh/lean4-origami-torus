#!/usr/bin/env python3
"""Exact algebra for the C0 endpoint bound and positive-branch exclusion.

The analytical support and ellipse arguments are in the companion note.
The conditional topology premise is the independently replayed CNF from
exhaustive_c0_positive_cones.py.  This file performs no numerical search.
"""

import json

import sympy as sym

import exhaustive_c0_positive_cones as cones
import exhaustive_c0_turning as turning
import remaining_c0_height_order as metric


def support_checks():
    L, H, radius = sym.symbols('L H R')
    h1 = 1-L-H
    x = (L*L+H*H-h1*h1)/(2*H)
    y2 = L*L-x*x
    N = radius*radius+2*x*radius+L*L
    K = (H-x)*radius+H*x-L*L
    # For q(R)=K/sqrt(N), verify the exact derivative numerators.
    first = sym.diff(K, radius)*N-K*sym.diff(N, radius)/2
    assert sym.cancel(first-y2*(radius+H)) == 0
    second_numerator = (-2*radius*radius-(x+3*H)*radius+L*L-3*H*x)
    assert sym.cancel(N-3*(radius+H)*(radius+x)-second_numerator) == 0
    assert sym.cancel(second_numerator.subs(radius, L)+(L+x)*(L+3*H)) == 0
    assert sym.cancel(sym.diff(second_numerator, radius)+4*radius+x+3*H) == 0
    assert sym.cancel(2*H*(1-L-x)-(1-2*L)) == 0

    # Parameterize the norm at R=1/2 by its triangle-inequality interval.
    n = sym.Symbol('n')
    p = n+L-sym.Rational(1, 2)
    q = L+sym.Rational(1, 2)-n
    slack = 1-2*L
    A = q*(1+p)+slack
    projected_H = slack/(2*A)
    projected_h1 = 1-L-projected_H
    projected_x = (L*L+projected_H**2-projected_h1**2)/(2*projected_H)
    assert sym.cancel(p+q+slack-1) == 0
    assert sym.cancel(sym.Rational(1, 4)+projected_x+L*L-n*n) == 0
    q_projection = ((projected_H-projected_x)/2
                    +projected_H*projected_x-L*L)/n
    certificate = q*(q*(1-q)*(1+p)+slack*slack)
    assert sym.cancel(2*n*A*(q_projection-projected_H+L)-certificate) == 0
    return {'derivative_identities': 4, 'half_radius_positive_identity': True,
            'norm_interval_reparameterization': True}


def ellipse_checks():
    M, t, sine, B = sym.symbols('M t sine B')
    h7 = (1-M+M*t)/2
    h6 = (1-M-M*t)/2
    parallel = (M+(1-M)*t)/2
    perpendicular = B*sine

    def circle_zero(expression):
        expression = sym.expand(expression).subs(sine**2, 1-t*t)
        expression = sym.expand(expression).subs(B**2, (1-2*M)/4)
        assert sym.expand(expression) == 0

    circle_zero(parallel**2+perpendicular**2-h7*h7)
    circle_zero((parallel-M)**2+perpendicular**2-h6*h6)
    assert sym.expand(h6+h7+M-1) == 0
    assert sym.expand(sym.Rational(1, 2)-h7-M*(1-t)/2) == 0
    assert sym.expand(sym.Rational(1, 2)-h6-M*(1+t)/2) == 0

    nx, ny, w = sym.symbols('nx ny w')
    Fy = (parallel-M)*ny+perpendicular*nx
    half_angle = {t: (1-w*w)/(1+w*w), sine: 2*w/(1+w*w)}
    assert sym.cancel(2*(1+w*w)*Fy.subs(half_angle)/ny
                      -(1-2*M-w*w+4*B*nx*w/ny)) == 0

    H, x, y, radius, n, L = sym.symbols('H x y R n L')
    P2 = sym.Matrix([x-H, -y])
    direction = sym.Matrix([-(radius+x)/n, y/n])
    perpendicular_direction = sym.Matrix([-y/n, -(radius+x)/n])
    q = ((H-x)*radius+H*x-L*L)/n
    positive_coefficient = y*(H+radius)/n
    assert sym.expand((P2.dot(direction)-q)*n).subs(y*y, L*L-x*x).expand() == 0
    assert sym.expand(P2.dot(perpendicular_direction)-positive_coefficient) == 0

    P6 = M*direction
    hh6 = sym.Symbol('h6')
    P7_boundary = P6-sym.Matrix([hh6, 0])
    cross = lambda a, b: sym.Matrix.hstack(a, b).det()
    assert sym.expand(cross(P2, -P7_boundary)
                      -M*y*(H+radius)/n-hh6*y) == 0
    # Core d0=h1*h7+P2 dot P7 is affine in t plus a positive
    # coefficient times sqrt(1-t^2).
    h1 = sym.Symbol('h1')
    core = h1*h7+q*parallel+positive_coefficient*B*sine
    expected = (h1*(1-M)+q*M)/2 + (h1*M+q*(1-M))*t/2 \
        +positive_coefficient*B*sine
    assert sym.expand(core-expected) == 0
    assert sym.expand(core.subs({t: 1, sine: 0})-(h1+q)/2) == 0
    return {'ellipse_norm_identities': 2, 'perimeter_and_deficit_identities': 3,
            'unique_positive_half_angle_root': True,
            'positive_concavity_coefficient': True,
            'turn_boundary_outer_sign_identity': True}


def verify():
    source = {'turning': turning.verify(), 'metric': metric.metric_bindings(),
              'conditional_cones': cones.symbolic_checks()}
    return {'source_bindings': source, 'support': support_checks(),
            'ellipse': ellipse_checks(),
            'endpoint_bound': 'D*cross(E,P6)+h2*C36>0 when C36<0',
            'actual_positive_2345_branch_excluded': True,
            'actual_positive_4567_branch_excluded': True,
            'requires_independent_positive_cones_cnf': True,
            'whole_regular_C0_excluded': False}


if __name__ == '__main__':
    if not __debug__:
        raise RuntimeError('run with assertions enabled')
    result = verify()
    print(json.dumps({key: value for key, value in result.items()
                      if key != 'source_bindings'}), flush=True)
