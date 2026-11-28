#!/usr/bin/env python3
"""Rank, height and symmetry completion for one collinear C1 endpoint cap.

The three exported CNFs exclude a negatively oriented regular lower cap.
Their actual-bracket rank and height clauses are checked below.  The
companion note combines them with solver_remaining_c1_collinear's five
independently certified implications; no SAT status alone is a proof.
"""

import argparse
from itertools import combinations
import json
from pathlib import Path

import sympy as sym

import exhaustive_remaining_locus as locus
import solver_remaining_c1_collinear as collinear
import solver_remaining_c1_geometry as geometry
from solver_chambers import write_cnf
from solver_sat import FastSAT

RANK_QUADS = ((0, 2, 3, 6), (0, 2, 3, 7), (2, 3, 6, 7))
HEIGHT_SIGNS = (
    (((1, 2, 3, 7), 1), ((0, 1, 2, 3), 1), ((0, 2, 3, 7), -1)),
    (((1, 4, 6, 7), 1), ((0, 1, 6, 7), -1),
     ((0, 1, 4, 7), -1), ((0, 1, 4, 6), 1)),
)


def symbolic_checks():
    alpha, beta = sym.symbols('alpha beta')
    P = [sym.zeros(2, 1), sym.zeros(2, 1)]
    P.extend(sym.Matrix(sym.symbols(f'x{i} y{i}')) for i in range(2, 8))
    z = (0, alpha/2, sym.Rational(1, 2), sym.Rational(1, 2),
         sym.Rational(1, 2), beta/2, 0, 0)
    points = [p.col_join(sym.Matrix([height])) for p, height in zip(P, z)]
    cross = lambda a, b: sym.Matrix.hstack(a, b).det()

    def bracket(quad):
        origin, *rest = quad
        return sym.Matrix.hstack(*(points[i]-points[origin] for i in rest)).det()

    E = P[2]-P[3]
    factors = (cross(E, P[6]), cross(E, P[7]), cross(E, P[7]-P[6]))
    for quad, factor in zip(RANK_QUADS, factors):
        assert sym.expand(2*bracket(quad)+factor) == 0
    assert sym.expand(factors[2]-factors[1]+factors[0]) == 0
    vector_identity = factors[0]*P[7]-factors[1]*P[6]+cross(P[6], P[7])*E
    assert all(sym.expand(value) == 0 for value in vector_identity)
    height_identities = (
        bracket((1, 2, 3, 7))+bracket((0, 1, 2, 3))
        -(1-alpha)*bracket((0, 2, 3, 7)),
        alpha*bracket((1, 4, 6, 7))-(1-alpha)*bracket((0, 1, 6, 7))
        -alpha*bracket((0, 1, 4, 7))+alpha*bracket((0, 1, 4, 6)),
    )
    assert all(sym.expand(value) == 0 for value in height_identities)

    # Both relabelings preserve the marked metric, including the horizontal
    # cyclic weights.  A reflected labeling uses intrinsic inversion -I.
    v = (0, alpha/2, sym.Rational(1, 2), sym.Rational(1, 2),
         sym.Rational(1, 2), -beta/2, 0, 0)
    h = sym.symbols('h0:8')
    X = geometry.horizontal_displacements(h)

    def ordered_horizontal(i, j):
        return X[i, j] if i < j else -X[j, i]

    records = []
    for mark in (1, 2):
        gauges = locus.marked_dihedral_gauges(mark)
        for sign, rotation, new_alpha, new_beta in (
                (-1, 6, beta, alpha), (1, 4, 1-beta, 1-alpha)):
            record = next(row for row in gauges
                          if row['sign'] == sign and row['rotation'] == rotation)
            permutation = tuple((rotation+sign*i) % 8 for i in range(8))
            gauge = record['gauge']
            transformed = [sym.expand(sign*(v[permutation[i]]-v[permutation[0]])
                                      +gauge[i][1]) for i in range(8)]
            expected = (0, new_alpha/2, sym.Rational(1, 2), sym.Rational(1, 2),
                        sym.Rational(1, 2), -new_beta/2, 0, 0)
            assert all(sym.expand(a-b) == 0 for a, b in zip(transformed, expected))
            weights = tuple((rotation+i) % 8 if sign == 1 else (rotation-i-1) % 8
                            for i in range(8))
            transformed_X = geometry.horizontal_displacements([h[i] for i in weights])
            assert all(sym.expand(value-sign*ordered_horizontal(permutation[i], permutation[j])) == 0
                       for (i, j), value in transformed_X.items())
            # A change of the spatial axis may shear the transverse plane,
            # but on either equal-height cap it is only a translation.
            spatial = ([sym.expand(z[permutation[i]]-z[permutation[0]]) for i in range(8)]
                       if sign == -1 else
                       [sym.expand(z[permutation[0]]-z[permutation[i]]) for i in range(8)])
            expected_spatial = (0, new_alpha/2, sym.Rational(1, 2), sym.Rational(1, 2),
                                sym.Rational(1, 2), new_beta/2, 0, 0)
            assert all(sym.expand(a-b) == 0 for a, b in zip(spatial, expected_spatial))
            records.append({'mark': mark, 'sign': sign, 'rotation': rotation,
                            'permutation': permutation, 'gauge': gauge,
                            'weight_indices': weights,
                            'new_alpha': str(new_alpha), 'new_beta': str(new_beta)})
    reflection = tuple((6-i) % 8 for i in range(8))
    literal = collinear.shared.common.lit
    assert literal(tuple(reflection[i] for i in (0, 1, 2, 3))) == literal((3, 4, 5, 6))
    for vertex in range(8):
        if vertex not in (0, 6, 7):
            assert literal(tuple(reflection[i] for i in (0, 6, 7, vertex))) == \
                -literal((0, 6, 7, reflection[vertex]))
    return {'rank_bracket_factors': True, 'rank_vector_identity': True,
            'height_identities': True, 'strict_reflection_signs': True,
            'marked_symmetries': records}


def negative_model(case):
    model = collinear.ActualBracketModel(case)
    for vertex in range(8):
        if vertex not in (0, 6, 7):
            positive, negative = model.bits((0, 6, 7, vertex))
            assert model.clauses.count([positive]) == 1
            model.clauses.remove([positive])
            model.clauses.append([negative])
    # E2 is nonzero and P6,P7 are independent.  No pair of the three
    # determinant factors can vanish simultaneously; both signs remain
    # allowed for whichever factor is nonzero.
    for first, second in combinations(RANK_QUADS, 2):
        model.clauses.append(list(model.bits(first))+list(model.bits(second)))
    # The omitted coefficient magnitudes are all strictly positive for
    # 0<alpha<1.  Their signed-zero-sum condition is necessary at zero
    # brackets as well as at nonzero ones.
    for relation in HEIGHT_SIGNS:
        model.sumzero([model.bits(quad, sign) for quad, sign in relation])
    return model


def build(directory):
    directory.mkdir(parents=True, exist_ok=True)
    identities = symbolic_checks()
    obligations = []
    for case in collinear.CASES:
        model = negative_model(case)
        with FastSAT(model.n, model.clauses) as solver:
            assert solver.check() == -1
        filename = f'c1_collinear_negative_{case}.cnf'
        # This fixed clause order yields a RUP-only trace for the one
        # formula whose forward order used an independently rejected step.
        clauses = list(reversed(model.clauses)) if case == '2_between_3_4' else model.clauses
        write_cnf(directory/filename, model.n, clauses)
        obligations.append({'file': filename, 'case': case, 'strict_0123': False,
                            'variables': model.n, 'clauses': len(model.clauses)})
    packet = {'assumptions': ['0<alpha,beta<1', 'negatively oriented noncollinear067',
                              'the stated collinear order or coincidence of234', 'E2!=0'],
              'identities': identities, 'rank_quadruples': RANK_QUADS,
              'height_relation_signs': HEIGHT_SIGNS,
              'unsat_obligations': obligations,
              'uses_positive_cap_package': 'solver_remaining_c1_collinear.py',
              'conclusion_after_all_eight_independent_replays':
                  'ray1 excludes exactly-one-collinear-cap limits, including coincidence',
              'both_collinear_caps_excluded': False}
    (directory/'c1_collinear_rank.json').write_text(json.dumps(packet, indent=2)+'\n')
    return packet


if __name__ == '__main__':
    if not __debug__:
        raise RuntimeError('run with assertions enabled')
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('output', type=Path)
    result = build(parser.parse_args().output)
    print(json.dumps({'unsat_obligations': len(result['unsat_obligations']),
                      'marked_symmetries_checked': len(result['identities']['marked_symmetries']),
                      'both_collinear_caps_excluded': False}), flush=True)
