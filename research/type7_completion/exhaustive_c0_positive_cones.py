#!/usr/bin/env python3
"""Exact topology and convex-cone reduction for positive C0 mixed brackets.

The exported CNFs need independent RUP replay.  This module certifies a
reduction, not an exclusion of the positive branches by itself.
"""

import argparse
import json
from pathlib import Path

import sympy as sym

import exhaustive_c0_height_order as height_order
import exhaustive_remaining_locus as locus
import solver_remaining_c1_geometry as geometry
from solver_chambers import write_cnf
from solver_sat import FastSAT


POSITIVE_BRANCH = (2, 3, 4, 5)
CONSEQUENCES = (
    ((0, 1, 3, 4), -1),
    ((0, 1, 2, 6), -1), ((0, 1, 3, 6), -1),
    ((0, 1, 3, 7), -1), ((0, 1, 4, 6), -1),
    ((0, 2, 3, 4), 1), ((0, 2, 3, 6), 1),
    ((0, 3, 4, 6), 1), ((1, 2, 4, 6), -1),
    ((1, 3, 4, 6), -1), ((2, 4, 5, 6), 1),
    ((3, 4, 5, 6), -1),
)


def symbolic_checks():
    u, v = sym.symbols('u v')
    lu, lv, gap = 1-2*u, 1-2*v, v-u
    P = [sym.zeros(2, 1), sym.zeros(2, 1)]
    P.extend(sym.Matrix(sym.symbols(f'x{i} y{i}')) for i in range(2, 8))
    z = (0, sym.Rational(1, 2), sym.Rational(1, 2),
         sym.Rational(1, 2), u, v, 0, 0)
    Q = [point.col_join(sym.Matrix([height])) for point, height in zip(P, z)]
    cross = lambda first, second: sym.Matrix.hstack(first, second).det()

    def bracket(quad):
        first, *rest = quad
        return sym.Matrix.hstack(*(Q[i]-Q[first] for i in rest)).det()

    E, F = P[3]-P[2], P[7]-P[6]
    Q4 = P[4]-2*u*P[3]-lu*P[6]
    Q5 = P[5]-2*v*P[3]-lv*P[6]
    S, W = lv*Q4-lu*Q5, v*Q4-u*Q5
    area = cross(Q4, Q5)
    identities = (
        2*bracket((2, 3, 4, 5))+cross(E, S),
        2*bracket((2, 4, 5, 6))+area-2*cross(E, W),
        2*bracket((3, 4, 5, 6))+area,
        gap*cross(E, Q4)-lu*cross(E, W)+u*cross(E, S),
        gap*cross(E, Q4)-lu*area/2-lu*bracket((2, 4, 5, 6))
        -2*u*bracket((2, 3, 4, 5)),
        2*bracket((0, 3, 4, 6))-cross(P[4]-2*u*P[3], P[6]),
        2*bracket((1, 3, 4, 6))+cross(P[3], P[4]-lu*P[6]),
        2*bracket((0, 2, 3, 4))-cross(E, P[4])-2*u*cross(P[2], P[3]),
        2*bracket((1, 2, 4, 6))-lu*cross(P[2], P[6])+cross(P[2], P[4]),
        2*bracket((0, 2, 3, 6))-cross(E, P[6]),
    )
    assert all(sym.expand(value) == 0 for value in identities)
    # C36 * E = cross(E,P6) * P3 + C23 * P6.
    basis = cross(P[3], P[6])*E-cross(E, P[6])*P[3]-cross(P[2], P[3])*P[6]
    assert all(sym.expand(value) == 0 for value in basis)

    # This reflection reverses the axis and one transverse coordinate,
    # hence preserves spatial orientation and swaps the two branches.
    permutation = tuple((1-i) % 8 for i in range(8))
    R = sym.diag(1, -1)
    reflected_P = [R*P[i] for i in permutation]
    reflected_z = [sym.Rational(1, 2)-z[i] for i in permutation]
    new_u, new_v = sym.Rational(1, 2)-v, sym.Rational(1, 2)-u
    expected_z = (0, sym.Rational(1, 2), sym.Rational(1, 2),
                  sym.Rational(1, 2), new_u, new_v, 0, 0)
    assert all(sym.expand(a-b) == 0 for a, b in zip(reflected_z, expected_z))
    reflected_Q4 = reflected_P[4]-2*new_u*reflected_P[3]-(1-2*new_u)*reflected_P[6]
    assert all(sym.expand(value) == 0 for value in reflected_Q4-R*Q5)
    literal = height_order.shared.common.lit
    assert literal(tuple(permutation[i] for i in POSITIVE_BRANCH)) == literal((4, 5, 6, 7))

    # Check the complete marked cocycle and the induced horizontal weights.
    h = sym.symbols('h0:8')
    X = geometry.horizontal_displacements(h)
    horizontal = lambda i, j: X[i, j] if i < j else -X[j, i]
    reflected_h = [h[(-i) % 8] for i in range(8)]
    reflected_X = geometry.horizontal_displacements(reflected_h)
    assert all(sym.expand(value+horizontal(permutation[i], permutation[j])) == 0
               for (i, j), value in reflected_X.items())
    intrinsic = (0, sym.Rational(1, 2), sym.Rational(1, 2),
                 sym.Rational(1, 2), 1-u, -v, 0, 0)
    expected_intrinsic = (0, sym.Rational(1, 2), sym.Rational(1, 2),
                          sym.Rational(1, 2), 1-new_u, -new_v, 0, 0)
    marked = []
    for mark in (1, 2):
        record = next(row for row in locus.marked_dihedral_gauges(mark)
                      if row['sign'] == -1 and row['rotation'] == 1)
        transformed = [-intrinsic[permutation[i]]+intrinsic[permutation[0]]
                       +record['gauge'][i][1] for i in range(8)]
        assert all(sym.expand(a-b) == 0 for a, b in zip(transformed, expected_intrinsic))
        marked.append(record)
    return {'determinant_identities': len(identities),
            'zero_safe_basis_identity': True,
            'orientation_preserving_reflection': permutation,
            'marked_reflections': marked}


def build(directory):
    directory.mkdir(parents=True, exist_ok=True)
    identities = symbolic_checks()
    n, source = height_order.source_formula()
    literal = height_order.shared.common.lit
    conclusions = [sign*literal(quad) for quad, sign in CONSEQUENCES]
    clauses = source+[[literal(POSITIVE_BRANCH)], [-value for value in conclusions]]
    with FastSAT(n, clauses) as solver:
        assert solver.check() == -1
    filename = 'c0_positive_2345_cone.cnf'
    write_cnf(directory/filename, n, clauses)
    record = {'identities': identities,
              'positive_actual_antecedent': POSITIVE_BRANCH,
              'weak_actual_consequences': CONSEQUENCES,
              'unsat_obligations': [{'file': filename, 'variables': n,
                                    'clauses': len(clauses)}],
              'mirror_covers_actual_4567_positive': True,
              'whole_positive_branch_excluded': False}
    (directory/'positive_cones.json').write_text(json.dumps(record, indent=2)+'\n')
    return record


if __name__ == '__main__':
    if not __debug__:
        raise RuntimeError('run with assertions enabled')
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('output', type=Path)
    result = build(parser.parse_args().output)
    print(json.dumps({'unsat_obligations': len(result['unsat_obligations']),
                      'determinant_identities': result['identities']['determinant_identities'],
                      'whole_positive_branch_excluded': False}), flush=True)
