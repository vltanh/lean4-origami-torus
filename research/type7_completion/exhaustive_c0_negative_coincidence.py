#!/usr/bin/env python3
"""Exclude C0 upper-cap coincidence with a negative regular lower cap.

One actual-trit implication bounds P5 on a segment.  Its exact metric
radius is strictly larger.  The CNF requires independent RUP replay.
"""

import argparse
import json
from pathlib import Path

import sympy as sym

import exhaustive_c0_collinear as boundary
import exhaustive_c0_turning as turning
import remaining_c0_height_order as metric
from solver_chambers import write_cnf
from solver_sat import FastSAT


def symbolic_checks():
    v = sym.Symbol('v')
    lv = 1-2*v
    P = [sym.zeros(2, 1), sym.zeros(2, 1)]
    P.append(sym.Matrix(sym.symbols('x2 y2')))
    P.append(sym.zeros(2, 1))
    P.extend(sym.Matrix(sym.symbols(f'x{i} y{i}')) for i in range(4, 8))
    u = sym.Symbol('u')
    levels = (0, sym.Rational(1, 2), sym.Rational(1, 2),
              sym.Rational(1, 2), u, v, 0, 0)
    Q = [point.col_join(sym.Matrix([height])) for point, height in zip(P, levels)]
    cross = lambda a, b: sym.Matrix.hstack(a, b).det()

    def bracket(quad):
        first, *rest = quad
        return sym.Matrix.hstack(*(Q[i]-Q[first] for i in rest)).det()

    C56, C57, C67 = cross(P[5], P[6]), cross(P[5], P[7]), cross(P[6], P[7])
    identities = (
        2*bracket((0, 1, 5, 6))-C56,
        2*bracket((0, 1, 5, 7))-C57,
        2*bracket((0, 1, 6, 7))-C67,
        2*bracket((0, 1, 2, 7))-cross(P[2], P[7]),
        2*bracket((1, 5, 6, 7))-C57+C56+lv*C67,
    )
    assert all(sym.expand(value) == 0 for value in identities)
    t = sym.Symbol('t')
    substitution = dict(zip(P[5], t*P[6]))
    assert sym.expand(2*bracket((1, 5, 6, 7)).subs(substitution)-(t-lv)*C67) == 0
    assert all(sym.expand(value) == 0 for value in
               (P[5]-lv*P[6]).subs(substitution)-(t-lv)*P[6])
    assert sym.expand(P[2].dot(P[2])*P[7].dot(P[7])
                      -P[2].dot(P[7])**2-cross(P[2], P[7])**2) == 0
    d0, d3, d4, d5, M = sym.symbols('d0 d3 d4 d5 M')
    D = d0+M
    radius = sym.Rational(1, 2)-d5-2*v*D
    assert sym.expand((radius-d3-d4-lv*D).subs(d5, sym.Rational(1, 2)-D-d3-d4)) == 0
    source = {'metric': metric.metric_bindings(), 'core': turning.verify()}
    return {'determinant_identities': 6, 'segment_vector_identity': True,
            'strict_cauchy_identity': True, 'exact_radius_decomposition': True,
            'source_bindings': source}


def build(directory):
    directory.mkdir(parents=True, exist_ok=True)
    checks = symbolic_checks()
    relations = boundary.height_relations()
    model = boundary.ActualModel('1_equals_3', -1, relations)
    # Negation of: actual0156=0, actual0157<=0, actual1567>=0,
    # and actual0127>0.  The strict conclusion retains its zero violation.
    violation = list(model.bits((0, 1, 5, 6)))
    violation += [model.bits((0, 1, 5, 7))[0],
                  model.bits((1, 5, 6, 7))[1],
                  -model.bits((0, 1, 2, 7))[0]]
    clauses = model.clauses+[violation]
    with FastSAT(model.n, clauses) as solver:
        assert solver.check() == -1
    filename = 'c0_negative_other_cap_coincidence.cnf'
    write_cnf(directory/filename, model.n, clauses)
    record = {'checks': checks,
              'unsat_obligations': [{'file': filename, 'variables': model.n,
                                    'clauses': len(clauses)}],
              'actual_conclusions': ['[0156]=0', '[0157]<=0', '[1567]>=0', '[0127]>0'],
              'excluded_after_metric_and_independent_replay':
                  'ray1 C0,0<u,v<1/2,P1=P3,regular negative-oriented067',
              'whole_C0_excluded': False}
    (directory/'negative_coincidence.json').write_text(json.dumps(record, indent=2)+'\n')
    return record


if __name__ == '__main__':
    if not __debug__:
        raise RuntimeError('run with assertions enabled')
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('output', type=Path)
    result = build(parser.parse_args().output)
    print(json.dumps({'unsat_obligations': len(result['unsat_obligations']),
                      'negative_other_cap_coincidence_excluded': True,
                      'whole_C0_excluded': False}), flush=True)
