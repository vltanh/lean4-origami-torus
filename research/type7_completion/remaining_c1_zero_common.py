#!/usr/bin/env python3
"""Common-line reductions in the EF orbit and at the two EE endpoints.

Six strict-minor CNFs require independent RUP replay.  This package
does not exclude the resulting scalar families or height endpoints.
"""

import argparse
import json
from pathlib import Path
import time

import sympy as S

import remaining_c1_flat_positive_stretch as signs
import solver_remaining_chambers as shared
import solver_remaining_c1_collinear as trits
import solver_remaining_c1_geometry as metric
import solver_remaining_limit as source_metric
from solver_chambers import write_cnf
from solver_sat import FastSAT

A, B, R = signs.A, signs.B, signs.X
HALF = S.Rational(1, 2)


def scalar_checks():
    rho1 = A*HALF+(1-A)*R
    projection1 = A*HALF-(1+A)*R
    assert S.expand(rho1**2-projection1**2-4*A*R*(HALF-R)) == 0
    rho5 = B*R+(1-B)*HALF
    projection5 = 2*R-rho5
    assert S.expand(rho5**2-projection5**2-4*(1-B)*R*(HALF-R)) == 0
    assert rho1.subs(R, 0) == projection1.subs(R, 0) == A/2
    assert S.expand(rho1.subs(R, HALF)-HALF) == 0
    assert S.expand(projection1.subs(R, HALF)+HALF) == 0
    assert S.expand(rho5.subs(R, 0)+projection5.subs(R, 0)) == 0
    assert S.expand(rho5.subs(R, HALF)-HALF) == 0
    assert S.expand(projection5.subs(R, HALF)-HALF) == 0
    return {'EE_relative_circle_norms': 2, 'EE_Cauchy_endpoint_equalities': 4}


def factored_sign(expression):
    constant, factors = S.factor_list(expression)
    result = int(S.sign(constant))
    for factor, power in factors:
        sign = signs.coefficient_sign(factor)
        if sign is None:
            return None
        result *= sign**power
    return int(result)


def coordinates(case):
    xi = S.Symbol('xi')
    if case.startswith('EF'):
        u = S.Matrix([1, 0])
        v = u if case == 'EF_same' else -u
        w = S.Matrix([xi, 1])
        h5 = {'EF_same': B/2, 'EF_opposite_left': S.Integer(0),
              'EF_opposite_interior': R, 'EF_opposite_right': HALF}[case]
        p3 = w/A
        p4 = p3+u
        p5 = B*p3+(1-B)*v+2*h5*u
        p7 = S.zeros(2, 1)
    else:
        u, v = S.Matrix([1, 0]), S.Matrix([xi, 1])
        assert case in ('EE_left', 'EE_right')
        p3 = v if case == 'EE_left' else -v/A
        p4 = p3+u
        p5 = v-(1-B)*u if case == 'EE_left' else B*p3+(1-B)*v+u
        p7 = v
    p = [S.zeros(2, 1), S.zeros(2, 1), p3, p3, p4, p5, v, p7]
    heights = (0, A/2, HALF, HALF, HALF, B/2, 0, 0)
    return xi, [point.col_join(S.Matrix([height])) for point, height in zip(p, heights)]


def scalar_families():
    stress = source_metric.closed_c1_rows().subs({source_metric.A: A/2, source_metric.B: -B/2})
    records = []

    def check(name, weights, points):
        assert S.expand(sum(weights)-S.Rational(5, 2)) == 0
        horizontal = metric.horizontal_displacements(weights)
        residuals = S.Matrix([(points[j]-points[i])**2-horizontal[i, j]**2
                              for i, j in source_metric.EDGES]+[0]*5)
        assert all(S.cancel(value) == 0 for value in stress*residuals)
        records.append({'family': name, 'weights': list(map(str, weights)),
                        'transverse': list(map(str, points))})

    for eta in (-1, 1):
        for epsilon in (-1, 1):
            h5 = B/2 if epsilon == 1 else R
            p3 = eta/(2*A)
            points = [0, 0, p3, p3, p3+HALF,
                      B*p3+(1-B)*epsilon*HALF+h5, epsilon*HALF, 0]
            check(f'EF_eta{eta}_epsilon{epsilon}',
                  [HALF, HALF, 0, HALF, HALF-h5, h5, HALF, 0], points)
    for r in (0, HALF):
        for epsilon in (-1, 1):
            p3 = HALF if r == 0 else -1/(2*A)
            p5 = HALF-(1-B)*epsilon*HALF if r == 0 else B*p3+(1-B)*HALF+epsilon*HALF
            check(f'EE_h0{r}_epsilon{epsilon}',
                  [r, HALF, 0, HALF, HALF-r, HALF, 0, HALF],
                  [0, 0, p3, p3, p3+epsilon*HALF, p5, HALF, HALF])
    assert len(records) == 8
    return records


def build(directory):
    started = time.monotonic()
    directory.mkdir(parents=True, exist_ok=True)
    checks = scalar_checks()
    families = scalar_families()
    obligations = []
    cases = ('EF_same', 'EF_opposite_left', 'EF_opposite_interior',
             'EF_opposite_right', 'EE_left', 'EE_right')
    for case in cases:
        xi, points = coordinates(case)
        n, base, *_ = shared.base_formula()
        assert base[0] == [1]
        clauses = [list(row) for row in base[1:]]
        units, omitted = [], []
        for quad in trits.QUADS:
            expression = S.cancel(A*S.det(S.Matrix.hstack(*(points[i]-points[quad[0]]
                                                            for i in quad[1:]))))
            assert not expression.has(xi)
            sign = factored_sign(expression)
            if sign is None:
                omitted.append(quad)
            elif sign:
                literal = sign*shared.common.lit(quad)
                clauses.append([literal])
                units.append(literal)
        expected = {'EF_same': (24, 0), 'EF_opposite_left': (23, 0),
                    'EF_opposite_interior': (20, 5), 'EF_opposite_right': (23, 0),
                    'EE_left': (33, 0), 'EE_right': (33, 0)}
        assert (len(units), len(omitted)) == expected[case]
        with FastSAT(n, clauses) as solver:
            assert solver.check() == -1, case
        filename = f'c1_zero_common_{case}.cnf'
        write_cnf(directory/filename, n, clauses)
        obligations.append({'file': filename, 'case': case, 'variables': n,
                            'clauses': len(clauses), 'strict_original_minors': units,
                            'omitted_variable_sign_minors': omitted})
    packet = {'domain': 'interior ray2 C1; EF, or EE with h0=0 or h0=1/2',
              'checks': checks, 'unsat_obligations': obligations,
              'remaining_scalar_families': families,
              'closed_projected_stress_checks_per_family': 12,
              'EF_nonparallel_cap_dependency': 'remaining_c1_opposite_zero.py',
              'conclusion': 'all transverse points lie on a common line through zero',
              'scalar_families_excluded': False, 'height_endpoints_excluded': False,
              'seconds': time.monotonic()-started}
    (directory/'c1_zero_common.json').write_text(json.dumps(packet, indent=2)+'\n')
    return packet


if __name__ == '__main__':
    if not __debug__:
        raise RuntimeError('run with assertions enabled')
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('output', type=Path)
    result = build(parser.parse_args().output)
    print(json.dumps({'unsat_obligations': 6, 'scalar_families_excluded': False,
                      'seconds': result['seconds']}))
