#!/usr/bin/env python3
"""Exact conditional signs and height bounds for regular ray-1 C0 caps.

Usage: python exhaustive_c0_height_order.py OUTPUT_DIRECTORY

The two exported CNFs require independent RUP replay.  Actual zeros
retain either generic completion sign.  The polynomial checks bind the
conditional generic signs to quantitative bounds on actual brackets.
"""

import argparse
import json
from pathlib import Path

import sympy as sym

import exhaustive_c0_angles as angles
import exhaustive_c0_turning as turning
import solver_remaining_chambers as shared
from solver_chambers import write_cnf
from solver_sat import FastSAT

CONDITIONALS = (
    ((2, 3, 4, 5), (((1, 2, 4, 5), 1), ((1, 3, 4, 5), -1))),
    ((4, 5, 6, 7), (((0, 4, 5, 6), 1), ((0, 4, 5, 7), -1))),
)


def source_formula():
    n, clauses, *_ = shared.base_formula()
    clauses += angles.cap_units(1)
    clauses += [[sign * shared.common.lit(quad)]
                for quad, sign in turning.METRIC_SIGNS]
    return n, clauses


def symbolic_checks():
    u, v = sym.symbols('u v')
    projected = [sym.zeros(2, 1), sym.zeros(2, 1)]
    projected.extend(sym.Matrix(sym.symbols(f'x{i} y{i}')) for i in range(2, 8))
    heights = (0, sym.Rational(1, 2), sym.Rational(1, 2), sym.Rational(1, 2), u, v, 0, 0)
    points = [point.col_join(sym.Matrix([height]))
              for point, height in zip(projected, heights)]

    def bracket(quad):
        first, *rest = quad
        return sym.Matrix.hstack(*(points[i] - points[first] for i in rest)).det()

    cross = lambda first, second: sym.Matrix.hstack(first, second).det()
    cap23 = cross(projected[2], projected[3])
    cap67 = cross(projected[6], projected[7])
    identities = (
        bracket((2, 3, 4, 5)) + bracket((1, 2, 4, 5))
        - bracket((1, 3, 4, 5)) + (u-v) * cap23,
        bracket((4, 5, 6, 7)) + bracket((0, 4, 5, 6))
        - bracket((0, 4, 5, 7)) + (u-v) * cap67,
    )
    assert all(sym.expand(expression) == 0 for expression in identities)
    assert sym.expand(2 * bracket((0, 1, 2, 3)) - cap23) == 0
    assert sym.expand(2 * bracket((0, 1, 6, 7)) - cap67) == 0

    edge2 = projected[3] - projected[2]
    edge6 = projected[7] - projected[6]
    S0 = (1-2*v) * projected[4] - (1-2*u) * projected[5]
    W0 = v * projected[4] - u * projected[5]
    assert sym.expand(bracket((2, 3, 4, 5)) - (v-u) * cap23
                      + cross(edge2, S0) / 2) == 0
    assert sym.expand(bracket((4, 5, 6, 7)) - (v-u) * cap67
                      + cross(W0, edge6)) == 0
    return {'exact_height_identities': 2, 'strict_cap_factors': 2,
            'quantitative_cross_product_factors': 2}


def build(directory):
    directory.mkdir(parents=True, exist_ok=True)
    identities = symbolic_checks()
    n, source = source_formula()
    obligations = []
    for branch, consequences in CONDITIONALS:
        branch_literal = shared.common.lit(branch)
        signed_targets = [sign * shared.common.lit(quad) for quad, sign in consequences]
        # Negate the conjunction of the claimed generic consequences.
        clauses = source + [[branch_literal], [-literal for literal in signed_targets]]
        with FastSAT(n, clauses) as solver:
            assert solver.check() == -1
        filename = 'c0_height_order_' + ''.join(map(str, branch)) + '.cnf'
        write_cnf(directory / filename, n, clauses)
        obligations.append({'file': filename, 'positive_generic_branch': branch,
                            'generic_consequences': consequences,
                            'variables': n, 'clauses': len(clauses)})
    record = {
        'premises': ['regular C0 cap orientations from exhaustive_c0_angles',
                     'the three actual strict ray1 signs from exhaustive_c0_turning'],
        'identities': identities,
        'unsat_obligations': obligations,
        'actual_bounds': ['[2345] <= max(v-u,0)*cross(P2,P3)',
                          '[4567] <= max(v-u,0)*cross(P6,P7)'],
        'actual_strict_disjunction_requires': 'v>u',
        'whole_regular_C0_excluded': False,
    }
    (directory / 'height_order.json').write_text(json.dumps(record, indent=2) + '\n')
    return record


if __name__ == '__main__':
    if not __debug__:
        raise RuntimeError('run with assertions enabled')
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('output', type=Path)
    result = build(parser.parse_args().output)
    print(json.dumps({'unsat_obligations': len(result['unsat_obligations']),
                      'identities': result['identities'],
                      'whole_regular_C0_excluded': False}), flush=True)
