#!/usr/bin/env python3
"""Exclude three complete scalar families in the double-zero C1 cover.

Five independent RUP obligations cover EF eta=-1,epsilon=+1 and
both EE h0 endpoints when U,V point in the same direction. The other
double-zero families and all height endpoints remain separate.
"""

import argparse
import json
from pathlib import Path
import time

import sympy as S

import remaining_c1_zero_common as common
import remaining_c1_single_zero_scalar as single
import remaining_c1_short_edges as relative
from solver_chambers import write_cnf
from solver_sat import FastSAT

A, B = single.A, single.B
HALF = S.Rational(1, 2)


def families():
    result = {}
    for record in common.scalar_families():
        result[record['family']] = {
            'points': [S.sympify(value, locals={'alpha': A, 'beta': B,
                                               'x': single.L})
                       for value in record['transverse']],
            'weights': [S.sympify(value, locals={'alpha': A, 'beta': B,
                                                'x': single.L})
                        for value in record['weights']],
        }
    return result


def symmetry_checks(source):
    marked = relative.symmetry_and_orbits()
    permutation = tuple((i+4) % 8 for i in range(8))
    assert any(tuple(row['permutation']) == permutation and row['mark'] == 2
               for row in marked['marked_symmetries'])
    right = source['EE_h01/2_epsilon1']
    left = source['EE_h00_epsilon1']
    points = right['points']
    levels = (0, A/2, HALF, HALF, HALF, B/2, 0, 0)
    slope = S.cancel((points[5]-points[4])/(levels[5]-levels[4]))
    assert S.cancel(slope+(1+A)/A) == 0
    # Reanchor the actual long edge 45; its limiting transverse chart
    # subtracts this finite axial shear. Reverse the scalar axis so
    # the new lower cap direction is positive.
    transformed = [-points[permutation[i]]+points[4]
                   +slope*(levels[permutation[i]]-levels[4]) for i in range(8)]
    substitution = {A: 1-B, B: 1-A}
    for i in range(8):
        assert S.cancel(transformed[i]
                        -left['points'][i].subs(substitution, simultaneous=True)) == 0
        assert S.cancel(HALF-levels[permutation[i]]
                        -S.sympify(levels[i]).subs(substitution, simultaneous=True)) == 0
        assert S.cancel(right['weights'][permutation[i]]
                        -left['weights'][i].subs(substitution, simultaneous=True)) == 0
    return {'marked_cap_swap': permutation,
            'height_map': ['1-beta', '1-alpha'],
            'EE_right_same_direction_maps_to_left': True,
            'coordinate_weight_and_height_identities': 24}


def build(directory):
    started = time.monotonic()
    directory.mkdir(parents=True, exist_ok=True)
    source = families()
    checks = {'relative_short_edge': relative.relative_metric_checks(),
              'scalar_source': 'all twelve original closed stresses checked in scalar_families',
              'cap_swap': symmetry_checks(source)}
    obligations = []

    def export(filename, model, clauses, claim, **extra):
        with FastSAT(model.n, clauses) as solver:
            assert solver.check() == -1, filename
        write_cnf(directory/filename, model.n, clauses)
        obligations.append({'file': filename, 'variables': model.n,
                            'clauses': len(clauses), 'claim': claim, **extra})

    ef = single.NormalModel(source['EF_eta-1_epsilon1'])
    export('c1_double_EF_negative_same.cnf', ef, ef.clauses,
           'EF eta=-1,epsilon=+1 has no nontrivial normal stretch',
           normal_source=ef.record)

    ee_family = source['EE_h00_epsilon1']
    ee = single.NormalModel(ee_family)
    export('c1_double_EE_left_same_N2_zero.cnf', ee,
           ee.clauses+[list(ee.normal_bits[0])],
           'EE h0=0,epsilon=+1 forces N2=0', normal_source=ee.record)
    for horizontal in (-1, 0, 1):
        model, rows = single.virtual_model(ee_family, horizontal)
        export(f'c1_double_EE_left_same_virtual_{horizontal}.cnf', model, model.clauses,
               'the independently normalized edge32 direction is impossible',
               virtual_horizontal=horizontal, exact_virtual_rows=rows)
    assert len(obligations) == 5
    result = {'domain': 'ray2 C1; interior alpha,beta; three double-zero scalar families',
              'source_checks': checks, 'unsat_obligations': obligations,
              'excluded_scalar_families': ['EF_eta-1_epsilon1', 'EE_h00_epsilon1',
                                           'EE_h01/2_epsilon1'],
              'relative_rate_assumptions': [],
              'all_double_zero_families_excluded': False,
              'height_endpoints_excluded': False,
              'seconds': time.monotonic()-started}
    (directory/'c1_double_zero_endpoints.json').write_text(json.dumps(result, indent=2)+'\n')
    return result


if __name__ == '__main__':
    if not __debug__:
        raise RuntimeError('run with assertions enabled')
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('output', type=Path)
    result = build(parser.parse_args().output)
    print(json.dumps({'excluded_scalar_families': result['excluded_scalar_families'],
                      'unsat_obligations': len(result['unsat_obligations']),
                      'seconds': result['seconds']}))
