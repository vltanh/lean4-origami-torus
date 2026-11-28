#!/usr/bin/env python3
"""Reduce nonparallel flat C0 caps to bd/da or dd.

An exact first-order cap tilt closes aa/ad, including every ratio
between planar cap area and inverse squared height. The marked
reflection also closes bb/db. Two further actual-trit certificates
close ab/ba. Four exported CNFs require independent RUP replay.
"""

import argparse
from itertools import combinations
import json
from pathlib import Path

import sympy as s

import exhaustive_c0_collinear as boundary
import exhaustive_c0_flat_common as common
import solver_remaining_c1_geometry as geometry
import solver_remaining_limit as reduction
from solver_chambers import write_cnf
from solver_sat import FastSAT

HALF = s.Rational(1, 2)


def symbolic_checks():
    u, v, length, p = s.symbols('u v L p')
    lu = 1-2*u
    hh = HALF-length
    d = list(s.symbols('d0:8'))
    d[1], d[2], d[3] = s.Integer(0), length, p
    d[7] = HALF-sum(d[:7])
    h = [HALF-value for value in d]
    points = [s.zeros(2, 1), s.zeros(2, 1), s.Matrix([-HALF, 0]),
              s.Matrix([-length, 0])]
    points += [s.Matrix(s.symbols(f'x{i} y{i}')) for i in range(4, 8)]
    X = geometry.horizontal_displacements(h)
    T = []
    for i, j in reduction.EDGES:
        delta = points[j]-points[i]
        T.append(s.expand(delta.dot(delta)-X[i, j]**2))
    matrix = reduction.original_system((HALF, HALF, HALF, 1-u, -v, 0))
    equations = s.Matrix(T+[0]*5)+matrix*s.Matrix(reduction.AUXILIARIES)

    def eq(edge):
        return equations[reduction.EDGES.index(edge)]

    H = reduction.H
    q14, q24 = reduction.QMAP[1, 4], reduction.QMAP[2, 4]
    correction = HALF*H[3]-length*H[2]-hh*H[1]
    assert s.expand(correction-(HALF*eq((0, 3))-length*eq((0, 2))-hh*eq((0, 1)))) == 0
    intrinsic_tilt = -(hh*q14+length*q24)/(2*lu)
    actual_tilt = intrinsic_tilt+correction
    witness = lu*(HALF*eq((0, 3))-length*eq((0, 2))-hh*eq((0, 1))) \
        -hh*eq((1, 4))-length*eq((2, 4))+HALF*eq((3, 4))
    assert s.cancel(2*lu*actual_tilt-2*length*(hh-p)-witness) == 0
    assert s.expand(hh-p-(d[0]+d[4]+d[5]+d[6]+d[7])) == 0

    # All three cap intrinsic rate parameters are bounded. These are
    # exact finite polynomial expansions; the limit coefficients 4v
    # and 2lu are strictly positive on the stated open height square.
    t, g1, g2, g3 = s.symbols('t gamma1 gamma2 gamma3')
    lifts = [0, HALF+t*g1, HALF+t*g2, HALF+t*g3, 1-u, -v, t*g3, 0]
    products = reduction.axis.product_polynomials(lifts)
    assert s.expand(products[0, 5]/t-4*v*g3-4*t*g3*g3) == 0
    assert s.expand(products[1, 4]/t-2*lu*(g1-g3)+4*t*g3*(g1-g3)) == 0
    assert s.expand(products[2, 4]/t-2*lu*(g2-g3)+4*t*g3*(g2-g3)) == 0
    assert s.cancel((HALF*(g3-g1)-length*(g2-g1))
                    -intrinsic_tilt.subs({q14: 2*lu*(g1-g3), q24: 2*lu*(g2-g3)})) == 0

    # Exact determinant expansion before taking any limit.
    z1, z7, a2, a3 = s.symbols('z1 z7 a2 a3')
    P2, P3, P7 = [s.Matrix(s.symbols(f'P{i}x P{i}y')) for i in (2, 3, 7)]
    cross = lambda a, b: s.det(s.Matrix.hstack(a, b))
    A, C27, C37 = cross(P2, P3), cross(P2, P7), cross(P3, P7)
    vectors = (P2.col_join(s.Matrix([t*a2])),
               P3.col_join(s.Matrix([t*a3])),
               P7.col_join(s.Matrix([z7-z1])))
    determinant = s.det(s.Matrix.hstack(*vectors))
    assert s.expand(determinant-(z7-z1)*A-t*(a2*C37-a3*C27)) == 0
    gamma = s.Symbol('Gamma')
    assert s.expand((2*length*a2-a3)*C27+2*(HALF*a3-length*a2)*C27) == 0

    # Exact marked reflection cover of the nine endpoint order pairs.
    # d'_i=d_{-i}; it interchanges upper a with lower b and vice versa.
    flip = {'a': 'b', 'b': 'a', 'd': 'd'}
    reflected = {a+b: flip[b]+flip[a] for a, b in __import__('itertools').product('abd', repeat=2)}
    assert reflected['aa'] == 'bb' and reflected['ad'] == 'db'
    assert reflected['bd'] == 'da' and reflected['dd'] == 'dd'
    closed = {'aa', 'ab', 'ad', 'ba', 'bb', 'db'}
    assert set(reflected)-closed == {'bd', 'da', 'dd'}
    return {'exact_cap_tilt_source_identity': True,
            'tilt': 'L*(1/2-L-d3)/(1-2u)>0',
            'bounded_intrinsic_rate_bindings': 3,
            'determinant_identity_before_limit': True,
            'marked_reflection': boundary.symmetry_checks(),
            'reflected_order_pairs': reflected}


def build(directory):
    directory.mkdir(parents=True, exist_ok=True)
    relations = boundary.height_relations()
    obligations = []
    for upper, lower in (('a', 'a'), ('a', 'd'), ('a', 'b'), ('b', 'a')):
        model = common.FlatModel(upper, lower, relations)
        nonparallel = list(model.bits((0, 1, 2, 7)))
        clauses = model.clauses+[nonparallel]
        if upper == 'a' and lower in ('a', 'd'):
            # Negate the conjunction: actual C27>0 and generic chi1237>0.
            violation = [-model.bits((0, 1, 2, 7))[0],
                         -boundary.shared.common.lit((1, 2, 3, 7))]
            clauses += [violation]
            claim = 'nonparallel caps imply actual C27>0 and generic chi1237>0'
        else:
            claim = 'this nonparallel endpoint order is impossible'
        with FastSAT(model.n, clauses) as solver:
            assert solver.check() == -1, upper+lower
        filename = f'c0_flat_nonparallel_{upper}{lower}.cnf'
        write_cnf(directory/filename, model.n, clauses)
        obligations.append({'file': filename, 'variables': model.n, 'clauses': len(clauses),
                            'claim': claim})
    packet = {'checks': symbolic_checks(), 'unsat_obligations': obligations,
              'excluded_order_pairs_after_analytic_proof': ['aa', 'ab', 'ad', 'ba', 'bb', 'db'],
              'remaining_nonparallel_order_pairs': ['bd', 'da', 'dd'],
              'canonical_remaining_pairs_up_to_marked_reflection': ['bd', 'dd'],
              'whole_flat_C0_exclusion_claimed': False}
    (directory/'flat_nonparallel.json').write_text(json.dumps(packet, indent=2)+'\n')
    return packet


if __name__ == '__main__':
    if not __debug__:
        raise RuntimeError('run with assertions enabled')
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('output', type=Path)
    result = build(parser.parse_args().output)
    print(json.dumps({'unsat_obligations': len(result['unsat_obligations']),
                      'remaining_nonparallel_order_pairs': result['remaining_nonparallel_order_pairs'],
                      'whole_flat_C0_exclusion_claimed': False}), flush=True)
