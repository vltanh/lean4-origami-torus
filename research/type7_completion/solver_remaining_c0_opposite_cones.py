#!/usr/bin/env python3
"""Reduce regular ray-1 C0 to the 42 positive-stem generic completions.

Usage: python solver_remaining_c0_opposite_cones.py OUTPUT_DIRECTORY

The six CNFs retain every actual zero through generic completions.
Their UNSAT answers require independent RUP replay.  The analytic proof
uses the exact endpoint support bound and is given in the companion note.
"""

import argparse
from itertools import combinations
import json
from pathlib import Path
import time

import sympy as s

import exhaustive_c0_endpoint_bound as endpoint
import exhaustive_c0_height_order as source
import exhaustive_c0_positive_cones as positive
import solver_remaining_chambers as shared
from solver_chambers import write_cnf
from solver_sat import FastSAT

CONSEQUENCES = (
    ((0, 1, 3, 4), -1), ((0, 1, 4, 6), -1),
    ((0, 3, 4, 6), 1), ((1, 3, 4, 6), -1),
    ((0, 2, 3, 6), 1), ((0, 3, 5, 6), -1),
    ((1, 3, 5, 6), 1), ((0, 1, 2, 6), -1),
    ((0, 2, 3, 4), 1), ((1, 2, 4, 6), -1),
    ((0, 2, 3, 5), 1), ((3, 4, 5, 6), -1),
)
PERMUTATION = tuple((1-i) % 8 for i in range(8))


def symbolic_checks():
    u, v = s.symbols('u v')
    lu, lv, K = 1-2*u, 1-2*v, v-u
    P = [s.zeros(2, 1), s.zeros(2, 1)]
    P += [s.Matrix(s.symbols(f'x{i} y{i}')) for i in range(2, 8)]
    levels = (0, s.Rational(1, 2), s.Rational(1, 2), s.Rational(1, 2), u, v, 0, 0)
    points = [p.col_join(s.Matrix([z])) for p, z in zip(P, levels)]
    cross = lambda a, b: s.det(s.Matrix.hstack(a, b))

    def bracket(quad):
        return s.det(s.Matrix.hstack(*(points[i]-points[quad[0]] for i in quad[1:])))

    E = P[3]-P[2]
    Q4, Q5 = P[4]-2*u*P[3]-lu*P[6], P[5]-2*v*P[3]-lv*P[6]
    identities = (
        2*bracket((0, 3, 4, 6))-cross(P[4]-2*u*P[3], P[6]),
        2*bracket((1, 3, 4, 6))+cross(P[3], P[4]-lu*P[6]),
        2*bracket((0, 3, 5, 6))-cross(P[5]-2*v*P[3], P[6]),
        2*bracket((1, 3, 5, 6))+cross(P[3], P[5]-lv*P[6]),
        2*bracket((0, 2, 3, 6))-cross(E, P[6]),
        2*bracket((2, 3, 4, 5))+cross(E, lv*Q4-lu*Q5),
        2*bracket((3, 4, 5, 6))+cross(Q4, Q5),
    )
    assert all(s.expand(value) == 0 for value in identities)
    A, cE, C36, a, b, c, d = s.symbols('A cE C36 a b c d')
    q4_e, q5_e = a*A-b*cE, -c*A+d*cE
    assert s.expand(b*q5_e-d*(-q4_e)-A*(a*d-b*c)) == 0
    actual_q4, actual_q5 = -a*P[3]-b*P[6], c*P[3]+d*P[6]
    assert s.expand(cross(actual_q4, actual_q5)-(b*c-a*d)*cross(P[3], P[6])) == 0
    assert all(s.expand(value) == 0 for value in
               cross(P[3], P[6])*E-cross(E, P[6])*P[3]-cross(P[2], P[3])*P[6])

    # The parallel-stem boundary is checked without dividing by C36.
    L, M, x, y, x4, y4, x5, y5 = s.symbols('L M x y x4 y4 x5 y5')
    substitution = dict(zip(P[2], (x, y))) | dict(zip(P[3], (L, 0)))
    substitution |= dict(zip(P[6], (-M, 0))) | dict(zip(P[4], (x4, y4)))
    substitution |= dict(zip(P[5], (x5, y5)))
    boundary = (
        2*bracket((0, 1, 4, 6)).subs(substitution)-M*y4,
        2*bracket((0, 3, 4, 6)).subs(substitution)-M*y4,
        2*bracket((1, 2, 4, 6)).subs(substitution).subs(y4, 0)-y*(x4+lu*M),
        2*bracket((0, 2, 3, 4)).subs(substitution).subs(y4, 0)-y*(x4-2*u*L),
        2*bracket((0, 3, 5, 6)).subs(substitution)-M*y5,
        2*bracket((0, 2, 3, 5)).subs(substitution).subs(y5, 0)-y*(x5-2*v*L),
    )
    assert all(s.expand(value) == 0 for value in boundary)
    literal = shared.common.lit
    assert literal(tuple(PERMUTATION[i] for i in (0, 1, 3, 6))) == literal((0, 1, 3, 6))
    assert literal(tuple(PERMUTATION[i] for i in (0, 3, 5, 6))) == -literal((1, 3, 4, 6))
    return {'mixed_determinant_identities': 7, 'cone_product_identity': True,
            'parallel_stem_boundary_identities': 6,
            'reflection': positive.symbolic_checks(), 'endpoint': endpoint.verify()}


def build(directory):
    directory.mkdir(parents=True, exist_ok=True)
    checks = symbolic_checks()
    n, clauses = source.source_formula()
    literal = shared.common.lit
    premises = (((0, 1, 3, 6), -1), ((2, 3, 4, 5), -1), ((4, 5, 6, 7), -1))
    base = clauses+[[sign*literal(quad)] for quad, sign in premises]
    first = -literal((0, 3, 5, 6))
    second = literal((1, 3, 4, 6))
    obligations = []

    def export(name, rows, claim):
        with FastSAT(n, rows) as solver:
            assert solver.check() == -1, name
        write_cnf(directory/name, n, rows)
        obligations.append({'file': name, 'claim': claim, 'variables': n, 'clauses': len(rows)})

    export('c0_opposite_cone_cover.cnf', base+[[-first], [-second]],
           'the stated source implies generic0356 negative or generic1346 positive')
    targets = [sign*literal(quad) for quad, sign in CONSEQUENCES]
    export('c0_opposite_cone_first.cnf', base+[[first], [-value for value in targets]],
           'generic0356 negative implies all twelve weak actual cone consequences')
    reflected = [sign*literal(tuple(PERMUTATION[i] for i in quad)) for quad, sign in CONSEQUENCES]
    export('c0_opposite_cone_reflected.cnf', base+[[second], [-value for value in reflected]],
           'generic1346 positive implies the marked reflections of all twelve consequences')
    positive_targets = [sign*literal(quad) for quad, sign in positive.CONSEQUENCES]
    positive_reflected = [sign*literal(tuple(PERMUTATION[i] for i in quad))
                          for quad, sign in positive.CONSEQUENCES]
    export('c0_weak_positive_first.cnf', clauses+[[literal((2, 3, 4, 5))],
                                                [-value for value in positive_targets]],
           'generic2345 positive implies the positive-cone consequences, even when actual2345=0')
    export('c0_weak_positive_reflected.cnf', clauses+[[literal((4, 5, 6, 7))],
                                                    [-value for value in positive_reflected]],
           'generic4567 positive implies the reflected weak-positive cone consequences')

    remaining_source = clauses+[[literal((0, 1, 3, 6))],
                                [-literal((2, 3, 4, 5))], [-literal((4, 5, 6, 7))]]
    members = []
    with FastSAT(n, remaining_source) as solver:
        while solver.check() == 1:
            word = tuple(solver.model(70))
            members.append(word)
            solver.add([-(i+1)*sign for i, sign in enumerate(word)])
    members.sort()
    assert len(members) == len(set(members)) == 42
    coverage = remaining_source+[[-(i+1)*sign for i, sign in enumerate(word)] for word in members]
    export('c0_positive_stem_42_coverage.cnf', coverage,
           'the remaining generic0136-positive source is covered by the exact 42 listed words')
    record = {'checks': checks, 'generic_premises': premises,
              'first_branch_consequences': CONSEQUENCES,
              'unsat_obligations': obligations,
              'research_exclusion_after_independent_replay':
                  'all compatible generic completions except the 42 listed generic0136-positive words',
              'remaining_words': members, 'remaining_word_count': len(members),
              'actual_zeros_retained': True, 'whole_regular_C0_excluded': False}
    (directory/'c0_opposite_cones.json').write_text(json.dumps(record, indent=2)+'\n')
    return record


if __name__ == '__main__':
    if not __debug__:
        raise RuntimeError('run with assertions enabled')
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('output', type=Path)
    start = time.monotonic()
    result = build(parser.parse_args().output)
    print(json.dumps({'unsat_obligations': len(result['unsat_obligations']),
                      'whole_regular_C0_excluded': False,
                      'seconds': round(time.monotonic()-start, 3)}), flush=True)
