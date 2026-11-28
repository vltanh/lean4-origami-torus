#!/usr/bin/env python3
"""Positive mixed brackets on the positive-other-cap C0 boundary.

Four actual-trit CNFs extend the regular positive-branch argument to
all three collinear upper-cap orders with positive regular lower cap.
The companion explains the two metric endpoint arguments.
"""

import argparse
import json
from pathlib import Path

import sympy as sym

import exhaustive_c0_collinear as boundary
import exhaustive_c0_endpoint_bound as endpoint
import exhaustive_c0_positive_cones as cones
from solver_chambers import write_cnf
from solver_sat import FastSAT


CASES = ('3_between_1_2', '1_equals_3')


def reflected_consequences():
    permutation = tuple((1-i) % 8 for i in range(8))
    conclusions = cones.CONSEQUENCES + (((1, 2, 4, 5), 1), ((1, 3, 4, 5), -1))
    result = []
    for quad, sign in conclusions:
        image = tuple(permutation[i] for i in quad)
        literal = boundary.shared.common.lit(image)
        result.append((tuple(sorted(image)), sign*(1 if literal > 0 else -1)))
    return tuple(result)


def symbolic_checks():
    source = endpoint.verify()
    u, v, L, x, y = sym.symbols('u v L x y')
    P3 = sym.Matrix([L, 0])
    P2 = sym.Matrix([x, y])
    E = P3-P2
    lu, lv = 1-2*u, 1-2*v
    s = sym.Rational(1, 2)-2*v*L
    Q4, Q5 = -2*u*P3, s*P3/L
    S = lv*Q4-lu*Q5
    cross = lambda a, b: sym.Matrix.hstack(a, b).det()
    coefficient = 2*u*lv+lu*s/L
    assert all(sym.expand(value) == 0 for value in S+coefficient*P3)
    assert sym.expand(-cross(E, S)/2+coefficient*cross(P2, P3)/2) == 0
    assert sym.expand(Q4.dot(Q5)+(2*u*L)*s) == 0
    assert sym.expand(Q5.dot(Q5)-s*s) == 0
    deficits = sym.symbols('d0:8')
    reflected = [deficits[(-i) % 8] for i in range(8)]
    assert reflected[6] == deficits[2] and reflected[7] == deficits[1]
    return {'source_endpoint_and_cones_checked': True,
            'collapsed_lower_metric_identities': 4,
            'reflected_deficits': [str(value) for value in reflected],
            'source_scope': source['whole_regular_C0_excluded']}


def build(directory):
    directory.mkdir(parents=True, exist_ok=True)
    identities = symbolic_checks()
    relations = boundary.height_relations()
    conclusions = reflected_consequences()
    obligations = []
    for case in CASES:
        model = boundary.ActualModel(case, 1, relations)
        turn = [[model.bits((2, 3, 6, 7))[0]],
                [model.bits((1, 2, 6, 7))[1]],
                [-model.bits((0, 2, 3, 7))[1]]]
        source = model.clauses+turn
        rows = (
            ('upper_mixed_nonpositive', source+[[model.bits((2, 3, 4, 5))[0]]]),
            ('lower_positive_reflected_cones', source+[[model.bits((4, 5, 6, 7))[0]],
                [model.bits(quad, -sign)[0] for quad, sign in conclusions]]),
        )
        for label, clauses in rows:
            with FastSAT(model.n, clauses) as solver:
                assert solver.check() == -1
            filename = f'c0_boundary_{case}_{label}.cnf'
            write_cnf(directory/filename, model.n, clauses)
            obligations.append({'file': filename, 'case': case, 'claim': label,
                                'variables': model.n, 'clauses': len(clauses)})
    record = {'identities': identities, 'reflected_weak_actual_consequences': conclusions,
              'unsat_obligations': obligations,
              'existing_third_order': '1_between_2_3 from exhaustive_c0_collinear',
              'conclusion_after_metric_and_independent_replay':
                  'all upper-collinear orders with positive regular067 have actual2345<=0 and4567<=0',
              'height_order_consequence':
                  'all three positive-other-cap orders excluded for0<v<=u<1/2',
              'negative_other_cap_coincidence_not_claimed': True,
              'whole_one_collinear_boundary_excluded': False}
    (directory/'collinear_positive.json').write_text(json.dumps(record, indent=2)+'\n')
    return record


if __name__ == '__main__':
    if not __debug__:
        raise RuntimeError('run with assertions enabled')
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('output', type=Path)
    result = build(parser.parse_args().output)
    print(json.dumps({'unsat_obligations': len(result['unsat_obligations']),
                      'collapsed_lower_metric_identities': 4,
                      'whole_one_collinear_boundary_excluded': False}), flush=True)
