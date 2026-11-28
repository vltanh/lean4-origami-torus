#!/usr/bin/env python3
"""Exact metric and Boolean data at the remaining ray-1 h1=0 endpoint.

Usage: python remaining_ray1_endpoint.py OUTPUT

This module binds the331 possible generic models to the verified first
stretch formula, checks the exact anchor/height/polarization identities,
and exports seven direct UNSAT obligations. It does not itself exclude
the endpoint.
"""

import argparse
import json
from pathlib import Path

import sympy as s

import exhaustive_remaining_axis as axis
from remaining_ray1_mask04_blowup import A_ORDERS, B_ORDERS, SlopeModel
import solver_remaining_chambers as shared
from solver_sat import FastSAT

HALF = s.Rational(1, 2)


def endpoint_model():
    return SlopeModel(A_ORDERS['II_sum_right'], B_ORDERS['II_both'])


def endpoint_primary_models():
    """Complete sorted primary projections; auxiliary witnesses stay free."""
    model = endpoint_model()
    result = set()
    with FastSAT(model.n, model.clauses) as solver:
        while True:
            status = solver.check()
            if status == -1:
                break
            assert status == 1
            signs = tuple(solver.model())
            assert signs not in result
            result.add(signs)
            solver.add([-(index+1)*value for index, value in enumerate(signs)])
    assert len(result) == 331
    return tuple(sorted(result))


def height_constants():
    """All t=0 metric equations in the bounded axis compactification."""
    shifts, _, edges = axis.case_data(1)
    v = (0, HALF, HALF, HALF, HALF, 0, 0, 0)
    intrinsic, spatial = axis.baselines(v)
    x = (0, -HALF, HALF, 0, -HALF, HALF, 0, HALF)
    transverse = (0, 0, 0, HALF, 0, HALF, 0, HALF)
    heights = [s.Integer(0)]+list(s.symbols('H1:8'))
    w, q25, q47 = s.symbols('w q25 q47')
    offsets = [s.Integer(0)]*8
    offsets[6] = w
    products = {(2, 5): q25, (4, 7): q47}
    residuals = []
    for i, j in edges:
        horizontal = x[j]-x[i]+shifts[i, j][0]+HALF*shifts[i, j][1]
        vertical = intrinsic[j]-intrinsic[i]+shifts[i, j][1]
        dz = spatial[j]-spatial[i]
        residuals.append(s.expand((transverse[j]-transverse[i])**2-horizontal**2
                                 +2*dz*(heights[j]-heights[i])
                                 -2*vertical*(offsets[j]-offsets[i])
                                 +products.get((i, j), 0)))
    unknowns = heights[1:]+[w, q25, q47]
    matrix, right = s.linear_eq_to_matrix(residuals, unknowns)
    assert matrix.rank() == 10
    expected = (s.Rational(1, 4), s.Rational(1, 4), -s.Rational(1, 4),
                -s.Rational(1, 4), -s.Rational(1, 4), -s.Rational(1, 8),
                HALF, -s.Rational(1, 8), -HALF, s.Rational(3, 4))
    assert s.linsolve((matrix, right), unknowns) == s.FiniteSet(expected)
    # q25 -> -2*b2/t; q47 -> -2*b6/t-2*w.
    assert -expected[-2]/2 == s.Rational(1, 4)
    assert -(expected[-1]+2*expected[-3])/2 == -s.Rational(1, 4)
    return {'rank': 10, 'heights': list(map(str, expected[:7])),
            'w': str(expected[7]), 'q25': str(expected[8]), 'q47': str(expected[9]),
            'b2_over_t': '1/4', 'b6_over_t': '-1/4'}


def anchor_identities():
    h, d0, d2, b1, b2, t, v1 = s.symbols('h d0 d2 b1 b2 t v1')
    h0, h2 = HALF-d0, HALF-d2
    v2, v3 = v1+b1, v1+b1+b2
    x1, x2 = -h0, 1-h0-h
    x3 = x2-h2
    ell2 = v1*v1+t*h0*h0
    face = h0*v3+v1*x3
    a2 = x2*x2+h0*h0-h*h
    a3 = x3*x3+h0*h0-(x3+h0)**2
    assert s.expand(a3+2*h0*x3) == 0
    norm3 = x3*x3*ell2+h0*h0*v3*v3-v1*v3*a3-t*a3*a3/4
    assert s.expand(norm3-face*face) == 0

    dot23 = (x2*x3*ell2+h0*h0*v2*v3
             -v1*(v2*a3+v3*a2)/2-t*a2*a3/4)
    k = HALF-h
    numerator = s.expand(face*(v1*x2+h0*v2)-k*(v1*v3-t*h0*x3))
    assert s.expand(dot23-numerator) == 0
    c = h0*h+HALF-h0-h
    gram = (v1*v1*h*h+h0*h0*b1*b1-2*v1*b1*c
            +t*(h0*h0*h*h-c*c))
    norm2 = x2*x2*ell2+h0*h0*v2*v2-v1*v2*a2-t*a2*a2/4
    assert s.expand(gram-norm2) == 0

    error_x = s.Poly(s.expand(numerator-b1*face/2), h, d0, d2, b1)
    assert all(sum(powers[:3]) >= 1 for powers, _ in error_x.terms())
    normal_numerator = s.expand(gram*face*face-numerator*numerator)
    error_y = s.Poly(normal_numerator, h, d0, d2, b1)
    assert all(sum(powers[:3]) >= 2 or
               (sum(powers[:3]) >= 1 and powers[3] >= 1)
               for powers, _ in error_y.terms())

    # First and second homogeneous jets at the endpoint. Coefficients
    # of the omitted terms are continuous; the two factor-ideal checks
    # above exclude an independent t or b2 remainder.
    base = {v1: HALF, b2: 0, t: 0}
    xjet = s.Poly(s.expand(numerator.subs(base)), h, d0, d2, b1)
    linear = sum(coefficient*s.prod(variable**power for variable, power in
                                   zip((h, d0, d2, b1), powers))
                 for powers, coefficient in xjet.terms() if sum(powers) == 1)
    assert s.expand(8*linear-(b1-h+2*d2)) == 0
    yjet = s.Poly(s.expand(normal_numerator.subs(base)), h, d0, d2, b1)
    quadratic = sum(coefficient*s.prod(variable**power for variable, power in
                                      zip((h, d0, d2, b1), powers))
                    for powers, coefficient in yjet.terms() if sum(powers) == 2)
    expected = 4*(b1*(h-d0-d2)+d2*(h-d2))
    assert s.expand(64*quadratic-expected) == 0
    assert s.expand(expected.subs(b1, d0-d2)-4*d0*(h-d0)) == 0
    return {'horizontal_factor_ideal': '(h,d0,d2)',
            'normal_factor_ideal': '(h,d0,d2)^2+b1*(h,d0,d2)',
            'horizontal_first_jet': 'b1-h+2*d2',
            'normal_second_jet': str(expected),
            'normal_jet_after_polarization': '4*d0*(h-d0)'}


def polarization_identity():
    h, d0, h7, b1, v1, v7, t = s.symbols('h d0 h7 b1 v1 v7 t')
    h0 = HALF-d0
    h1, h2, h7height = s.symbols('H1 H2 H7')
    p2norm, p7norm, dot = s.symbols('P2norm P7norm P2dotP7')
    x2 = 1-h0-h
    edge17 = h0+h7-1
    e01 = 2*v1*h1+t*h1*h1-h0*h0
    e02 = p2norm+2*(v1+b1)*h2+t*h2*h2-x2*x2
    e17 = p7norm+2*(v7-v1)*(h7height-h1)+t*(h7height-h1)**2-edge17**2
    e27 = (p7norm+p2norm-2*dot+2*(v7-v1-b1)*(h7height-h2)
           +t*(h7height-h2)**2-(edge17+h)**2)
    target = dot+b1*h7height+(v7+t*h7height)*(h2-h1)+h*h7-d0
    assert s.expand((e02-e01-e27+e17)/2-target) == 0
    return 'P2.dot(P7)+b1*H7+(v7+t*H7)*(H2-H1)=d0-h1*h7'


def planar_reference():
    """An exact all-t metric reference and a checked22-row extension.

    The boundary has h1=0 and degenerate intrinsic faces. No embedding
    or uniqueness assertion is made for the chosen normal extension.
    """
    shifts, _, edges = axis.case_data(1)
    t, u, p = s.symbols('t u p')
    denominator = 1+2*u+t/4
    v1 = u+HALF-t/8
    v3 = denominator/2-u*t*p/denominator
    v5 = u-t/4+t*denominator*(1-p)/(2*(denominator-t*p))
    vertical = [0, v1, v1, v3, v1, v5, u, u-t/4]
    intrinsic_x = [0, -HALF, HALF, 0, -HALF, HALF, 0, HALF]
    spatial_x = [0, HALF, HALF, 2*v1*p/denominator, HALF, HALF, 0, HALF]
    spatial_z = list(vertical)
    spatial_z[3] = v3-t*p/denominator
    normal_square = p*(1-p)
    nonzero = []
    residual = -t*denominator*(1-p)/(denominator-t*p)
    for i, j in edges:
        horizontal = (intrinsic_x[j]-intrinsic_x[i]+shifts[i, j][0]
                      +HALF*shifts[i, j][1])
        intrinsic_vertical = vertical[j]-vertical[i]+shifts[i, j][1]
        normal = normal_square if 3 in (i, j) else 0
        actual = s.factor(t*((spatial_x[j]-spatial_x[i])**2+normal-horizontal**2)
                          +(spatial_z[j]-spatial_z[i])**2-intrinsic_vertical**2)
        assert s.cancel(actual.subs(p, 1)) == 0
        if actual != 0:
            nonzero.append((i, j))
            assert s.cancel(actual-residual) == 0
    assert nonzero == [(2, 5), (4, 5)]
    # Explicit positive axis01 gauge map from the B-plane coordinates.
    # P_x=(v1*U-Z/2)/ell, zeta=(t*U/2+v1*Z)/ell,
    # with ell^2=v1^2+t/4; the normal coordinate is unchanged.
    du, dz, dw = s.symbols('du dz dw')
    ell2 = v1*v1+t/4
    transverse_numerator = v1*du-dz/2
    axial_numerator = t*du/2+v1*dz
    assert s.expand(t*transverse_numerator**2+axial_numerator**2
                    -ell2*(t*du*du+dz*dz)) == 0
    assert s.expand(v1*spatial_x[1]-spatial_z[1]/2) == 0
    assert s.expand(t*spatial_x[1]/2+v1*spatial_z[1]-ell2) == 0
    assert s.cancel((v1*spatial_x[3]-spatial_z[3]/2)
                    .subs({p: 1, u: 0, t: 0})) == s.Rational(1, 4)
    return {'parameter': 'u=v6', 'A': str(denominator),
            'all_24_residuals_at_p_one': 0,
            'normal_square': str(normal_square),
            'nonzero_extension_rows': nonzero,
            'extension_residual': str(residual),
            'axis_gauge': {'ell_squared': 'v1^2+t/4',
                           'P_x': '(v1*U-Z/2)/ell',
                           'zeta': '(t*U/2+v1*Z)/ell'}}


def exact_checks():
    return {'height_constants': height_constants(), 'anchor': anchor_identities(),
            'polarization': polarization_identity(), 'planar_reference': planar_reference()}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('output', type=Path)
    args = parser.parse_args()
    args.output.mkdir(parents=True, exist_ok=True)
    model = endpoint_model()
    models = endpoint_primary_models()
    coverage = model.clauses+[[-(index+1)*value for index, value in enumerate(row)]
                              for row in models]
    shared.common.write_cnf(args.output/'primary_coverage.cnf', model.n, coverage)
    vertical_tests = []
    for edge_index in (0, 2, 4):
        for direction, bit in zip(('positive', 'negative'), model.trits['vertical', edge_index]):
            clauses = model.clauses+[[bit]]
            with FastSAT(model.n, clauses) as solver:
                assert solver.check() == -1
            filename = f'upper_cluster_{edge_index}_{direction}.cnf'
            shared.common.write_cnf(args.output/filename, model.n, clauses)
            vertical_tests.append(filename)
    record = {'exact_checks': exact_checks(), 'complete': True,
              'models': [''.join('+' if value > 0 else '-' for value in row) for row in models],
              'upper_cluster_vertical_exclusions': vertical_tests}
    (args.output/'endpoint.json').write_text(json.dumps(record, indent=2)+'\n')
    print(json.dumps({'primary_models': 331, 'upper_cluster_vertical_exclusions': 6,
                      'exact_checks': 'PASS', 'status': 'relative endpoint data only'}))


if __name__ == '__main__':
    if not __debug__:
        raise RuntimeError('run with assertions enabled')
    main()
