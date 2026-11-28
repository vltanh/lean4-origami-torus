#!/usr/bin/env python3
"""Exact regular-cap orientation and angular cover on component C1.

Usage: python exhaustive_c1_angles.py OUTPUT_DIRECTORY

Both endpoint triangles234 and067 are noncollinear, with0<alpha,beta<1.
The six emitted UNSAT formulas require independent replay. All actual
minor signs remain weak. No metric infeasibility is claimed.
"""

import argparse
from itertools import combinations, product
import json
from pathlib import Path

import sympy as sym

import solver_remaining_chambers as common
from solver_chambers import write_cnf
from solver_sat import FastSAT

PAIRS = tuple(combinations(range(2, 8), 2))
ANCHORS = tuple(common.common.lit((0, 1)+pair) for pair in PAIRS)
EXPECTED = {
    '+++--+--------+', '+++------+----+', '+++-----------+',
    '++-+-+-+++-++-+', '++-+-+-++-+++-+', '++-+-+-++--++-+',
    '++-+-+-+-+-++-+', '++-+-+-+--+++-+', '++-+-+-+---++-+',
    '++-+---++-+++-+', '++---+--------+', '++-----------++',
    '++------------+', '+-+---+--+--+-+',
}
EXTRA_SIGNS = (((3, 4, 5, 6), -1), ((4, 5, 6, 7), -1))


def cap_units(upper_orientation, lower_orientation):
    assert upper_orientation in (-1, 1) and lower_orientation in (-1, 1)
    return [[sign*common.common.lit(triangle+(vertex,))]
            for triangle, sign in (((2, 3, 4), -upper_orientation),
                                   ((0, 6, 7), lower_orientation))
            for vertex in range(8) if vertex not in triangle]


def exact_geometry():
    alpha, beta = sym.symbols('alpha beta')
    p = [sym.zeros(2, 1), sym.zeros(2, 1)]
    p.extend(sym.Matrix(sym.symbols(f'p{i}x p{i}y')) for i in range(2, 8))
    levels = [0, alpha/2, sym.Rational(1, 2), sym.Rational(1, 2),
              sym.Rational(1, 2), beta/2, 0, 0]
    points = [point.col_join(sym.Matrix([level])) for point, level in zip(p, levels)]
    cross = lambda a, b: sym.det(sym.Matrix.hstack(a, b))

    def bracket(quad):
        first, *rest = quad
        return sym.det(sym.Matrix.hstack(*(points[i]-points[first] for i in rest)))

    for i, j in PAIRS:
        assert sym.expand(2*bracket((0, 1, i, j))-alpha*cross(p[i], p[j])) == 0
    e3, f = p[4]-p[3], p[7]-p[6]
    r5 = p[5]-beta*p[3]-(1-beta)*p[6]
    y5 = beta*e3-r5
    assert sym.expand(2*bracket((3, 4, 5, 6))-cross(r5, e3)) == 0
    assert sym.expand(2*bracket((4, 5, 6, 7))+cross(y5, f)) == 0
    return {'anchor_identities': 15,
            'extra_signs': ['cross(R5,E3)<=0', 'cross(Y5,F)>=0']}


def build(directory):
    n, base, *_ = common.base_formula()
    directory.mkdir(parents=True, exist_ok=True)
    obligations = []
    for upper, lower in product((-1, 1), repeat=2):
        if (upper, lower) == (1, 1):
            continue
        clauses = base+cap_units(upper, lower)
        with FastSAT(n, clauses) as solver:
            assert solver.check() == -1
        name = f'c1_cap_orientation_{upper}_{lower}.cnf'
        write_cnf(directory/name, n, clauses)
        obligations.append(name)

    positive = base+cap_units(1, 1)
    models, assignments = [], []
    with FastSAT(n, positive) as solver:
        while solver.check() == 1:
            assignment = solver.model(n)
            assert all(any(assignment[abs(literal)-1]*(1 if literal > 0 else -1) > 0
                           for literal in clause) for clause in positive)
            values = tuple(assignment[:70])
            assert values not in models
            models.append(values)
            assignments.append(assignment)
            solver.add([-(i+1)*value for i, value in enumerate(values)])
        assert solver.check() == -1
    assert len(models) == 132
    patterns = sorted({tuple(row[variable-1] for variable in ANCHORS) for row in models})
    words = {''.join('+' if value > 0 else '-' for value in row) for row in patterns}
    assert words == EXPECTED and len(patterns) == 14

    common_literals = {(i+1)*models[0][i] for i in range(70)
                       if all(row[i] == models[0][i] for row in models)}
    cap_literals = {clause[0] for clause in cap_units(1, 1)}
    anchor_literals = {variable*patterns[0][i] for i, variable in enumerate(ANCHORS)
                       if all(row[i] == patterns[0][i] for row in patterns)}
    extra = [sign*common.common.lit(quad) for quad, sign in EXTRA_SIGNS]
    assert common_literals-cap_literals-anchor_literals == set(extra)
    # These checked assignments witness both signs of every nonunanimous
    # primary variable. They do not rely on an UNSAT or model-count claim.
    common_variables = {abs(literal) for literal in common_literals}
    uncovered = {sign*i for i in range(1, 71) if i not in common_variables
                 for sign in (-1, 1)}
    witnesses = []
    while uncovered:
        witness = max(assignments, key=lambda row: len(uncovered & {
            (i+1)*value for i, value in enumerate(row[:70])}))
        covered = uncovered & {(i+1)*value for i, value in enumerate(witness[:70])}
        assert covered
        witnesses.append(witness)
        uncovered -= covered

    formulas = {
        'c1_anchor_coverage.cnf': positive+[
            [-variable*value for variable, value in zip(ANCHORS, row)] for row in patterns],
        'c1_primary_coverage.cnf': positive+[
            [-(i+1)*value for i, value in enumerate(row)] for row in models],
        'c1_extra_signs.cnf': positive+[[-literal for literal in extra]],
    }
    for name, clauses in formulas.items():
        with FastSAT(n, clauses) as solver:
            assert solver.check() == -1
        write_cnf(directory/name, n, clauses)
        obligations.append(name)
    result = {
        'assumptions': ['noncollinear projected234 and067', '0<alpha,beta<1'],
        'cap_orientations': [1, 1], 'pairs': PAIRS, 'anchor_variables': ANCHORS,
        'patterns': sorted(words),
        'primary_models': sorted(''.join('+' if value > 0 else '-' for value in row)
                                 for row in models),
        'extra_necessary_signs': [{'quad': quad, 'sign': sign} for quad, sign in EXTRA_SIGNS],
        'nonunanimity_full_boolean_witnesses': witnesses,
        'exact_geometry': exact_geometry(), 'unsat_obligations': obligations,
        'actual_minor_semantics': 'weak signs of a generic completion',
        'metric_exclusion': False,
    }
    (directory/'c1_angles.json').write_text(json.dumps(result, indent=2)+'\n')
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('output', type=Path)
    args = parser.parse_args()
    result = build(args.output)
    print(json.dumps({'primary_models': len(result['primary_models']),
                      'angular_patterns': len(result['patterns']),
                      'unsat_obligations': len(result['unsat_obligations']),
                      'extra_nonanchor_signs': 2, 'metric_exclusion': False}))


if __name__ == '__main__':
    if not __debug__:
        raise RuntimeError('run with assertions enabled')
    main()
