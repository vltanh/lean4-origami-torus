#!/usr/bin/env python3
"""Exclude the two-sided middle wedge in regular ray-1 C0, uniformly in height.

Usage: python solver_remaining_c0_middle_wedge.py OUTPUT_DIRECTORY

The companion note proves the analytic implication, including actual zeros.
The two completeness CNFs require independent RUP replay.
"""

import argparse
from itertools import combinations
import json
from pathlib import Path
import time

import sympy as s

import exhaustive_c0_height_order as source
import remaining_c0_height_order as metric
import solver_remaining_chambers as shared
from solver_chambers import write_cnf
from solver_sat import FastSAT


def symbolic_checks():
    u, v = s.symbols('u v')
    lu, lv, K = 1-2*u, 1-2*v, v-u
    P = [s.zeros(2, 1), s.zeros(2, 1)]
    P += [s.Matrix(s.symbols(f'x{i} y{i}')) for i in range(2, 8)]
    levels = (0, s.Rational(1, 2), s.Rational(1, 2), s.Rational(1, 2), u, v, 0, 0)
    points = [p.col_join(s.Matrix([z])) for p, z in zip(P, levels)]
    cross = lambda a, b: s.det(s.Matrix.hstack(a, b))

    def bracket(q):
        return s.det(s.Matrix.hstack(*(points[i]-points[q[0]] for i in q[1:])))

    E, F = P[3]-P[2], P[7]-P[6]
    Q4 = P[4]-2*u*P[3]-lu*P[6]
    Q5 = P[5]-2*v*P[3]-lv*P[6]
    S, W = lv*Q4-lu*Q5, v*Q4-u*Q5
    identities = (
        2*bracket((2, 3, 5, 6))+cross(E, Q5),
        2*bracket((3, 4, 6, 7))-cross(Q4, F),
        2*bracket((2, 3, 4, 5))+cross(E, S),
        bracket((4, 5, 6, 7))+cross(W, F),
        2*bracket((3, 4, 5, 6))+cross(Q4, Q5),
        2*bracket((2, 3, 6, 7))-cross(E, F),
    )
    assert all(s.expand(value) == 0 for value in identities)

    # A finite half-angle coordinate includes the zero-angle endpoint.
    a, b = s.symbols('a b')
    unit = lambda t: s.Matrix((1-t*t, 2*t))/(1+t*t)
    assert s.cancel(unit(a).dot(unit(a))-1) == 0
    assert s.cancel(cross(unit(a), unit(b))
                    -2*(b-a)*(1+a*b)/((1+a*a)*(1+b*b))) == 0
    assert s.cancel(1-unit(a)[0]-a*unit(a)[1]) == 0

    d = list(s.symbols('d0:7'))
    d.append(s.Rational(1, 2)-sum(d))
    h = [s.Rational(1, 2)-value for value in d]
    D = d[0]+d[1]+d[2]+d[6]+d[7]
    r, q = h[3]-lu*D, h[5]-2*v*D
    RS, RW = lv*r+lu*q, v*r+u*q
    ES = h[2]*RS-lv*(h[2]-d[3])
    FW = h[6]*RW-u*(h[6]-d[5])
    upper = d[3]*d[2]-lu*D*h[2]
    lower = d[5]*d[6]-2*v*D*h[6]
    assert s.expand(h[2]*(lv*r-lu*q)+ES-2*lv*upper) == 0
    assert s.expand(h[6]*(v*r-u*q)-FW+2*u*lower) == 0

    R2, R6 = h[2]-d[3]-d[5], h[6]-d[3]-d[5]
    assert s.expand(R2-(d[0]+d[1]+d[4]+d[6]+d[7])) == 0
    assert s.expand(R6-(d[0]+d[1]+d[2]+d[4]+d[7])) == 0
    delta = h[2]*h[6]-d[3]*h[6]-d[5]*h[2]
    assert s.expand(delta-d[3]*R2-d[5]*R6-R2*R6) == 0
    positive = (D*(d[3]*R2+d[5]*R6+R2*R6)
                +d[3]*(D-d[2])*h[6]+d[5]*(D-d[6])*h[2]
                +2*K*D*h[2]*h[6])
    assert s.expand(h[6]*upper+h[2]*lower+positive) == 0
    return {'metric_source': metric.metric_bindings(),
            'actual_bracket_identities': 6, 'half_angle_identities': 3,
            'weighted_support_identities': 2,
            'positive_deficit_identity': True,
            'height_domain': '0<u<v<1/2', 'actual_zeros_retained': True}


def build(directory):
    directory.mkdir(parents=True, exist_ok=True)
    checks = symbolic_checks()
    n, clauses = source.source_formula()
    literal = shared.common.lit
    base = clauses+[[literal((0, 1, 3, 6))],
                    [-literal((2, 3, 4, 5))], [-literal((4, 5, 6, 7))]]
    q1, q2 = literal((2, 3, 5, 6)), literal((3, 4, 6, 7))
    words = []
    with FastSAT(n, base) as solver:
        while solver.check() == 1:
            word = tuple(solver.model(70))
            words.append(word)
            solver.add([-(i+1)*value for i, value in enumerate(word)])
    words.sort()
    assert len(words) == len(set(words)) == 42
    excluded = [word for word in words if word[q1-1] == word[q2-1] == -1]
    remaining = [word for word in words if word not in excluded]
    assert len(excluded) == 16 and len(remaining) == 26
    obligations = []

    def export(name, rows, claim):
        with FastSAT(n, rows) as solver:
            assert solver.check() == -1, name
        write_cnf(directory/name, n, rows)
        obligations.append({'file': name, 'claim': claim,
                            'variables': n, 'clauses': len(rows)})

    def blocks(members):
        return [[-(i+1)*value for i, value in enumerate(word)] for word in members]

    export('c0_middle_wedge_16_coverage.cnf',
           base+[[-q1], [-q2]]+blocks(excluded),
           'the two negative generic antecedents have exactly the listed 16 completions')
    export('c0_after_middle_wedge_26_coverage.cnf',
           base+[[q1, q2]]+blocks(remaining),
           'after the proved metric clause, the exact 26 listed completions cover the source')
    record = {'checks': checks,
              'antecedents': [[[2, 3, 5, 6], -1], [[3, 4, 6, 7], -1]],
              'proved_metric_clause': [q1, q2],
              'excluded_words': excluded, 'excluded_word_count': len(excluded),
              'remaining_words': remaining, 'remaining_word_count': len(remaining),
              'unsat_obligations': obligations, 'actual_zeros_retained': True,
              'research_exclusion_after_independent_replay':
                  'the 16 two-sided middle-wedge completions, uniformly on 0<u<v<1/2',
              'whole_regular_C0_excluded': False}
    (directory/'c0_middle_wedge.json').write_text(json.dumps(record, indent=2)+'\n')
    return record


if __name__ == '__main__':
    if not __debug__:
        raise RuntimeError('run with assertions enabled')
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('output', type=Path)
    start = time.monotonic()
    result = build(parser.parse_args().output)
    print(json.dumps({'excluded': result['excluded_word_count'],
                      'remaining': result['remaining_word_count'],
                      'unsat_obligations': len(result['unsat_obligations']),
                      'seconds': round(time.monotonic()-start, 3)}), flush=True)
