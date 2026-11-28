#!/usr/bin/env python3
"""Exclude the nonflat coincident45 circle in interior ray-1 C0.

Two exact virtual-direction implications combine with the relative
diagonal estimate. All emitted CNFs require independent RUP replay.
The two line directions of the circle are deliberately retained.
"""

import argparse
from itertools import combinations
import json
from pathlib import Path

import sympy as s

import exhaustive_c0_double_coincidence as diagonal
from solver_chambers import write_cnf
from solver_sat import FastSAT

HALF = s.Rational(1, 2)
boundary = diagonal.boundary


def circle_relations():
    """Check every divided13 determinant on the exact circle coordinates."""
    u, eps = s.symbols('u eps')
    p = s.Matrix(s.symbols('px py'))
    q = s.Matrix(s.symbols('qx qy'))
    w = s.Matrix(s.symbols('wx wy'))
    zero = s.zeros(2, 1)
    transverse = (zero, zero, p, eps*w, q, q, zero, -p)
    heights = (0, HALF, HALF, HALF, u, u, 0, 0)
    points = [v.col_join(s.Matrix([z])) for v, z in zip(transverse, heights)]
    cross = lambda a, b: s.det(s.Matrix.hstack(a, b))
    weights = ((0, 0), (0, 0), (1, 0), (0, 0),
               (0, 1), (0, 1), (0, 0), (-1, 0))
    rows = []
    for quad in diagonal.common.QUADS:
        if not {1, 3} <= set(quad):
            continue
        i, j = [vertex for vertex in quad if vertex not in (1, 3)]
        order = (1, 3, i, j)
        parity = (-1)**sum(order[a] > order[b] for a, b in combinations(range(4), 2))
        coefficients = tuple(s.expand(parity*(-weights[i][k]*(heights[j]-HALF)
                                               +weights[j][k]*(heights[i]-HALF)))
                             for k in range(2))
        determinant = s.det(s.Matrix.hstack(*(points[v]-points[quad[0]] for v in quad[1:])))
        assert s.expand(determinant/eps-coefficients[0]*cross(p, w)
                        -coefficients[1]*cross(q, w)) == 0
        signs = []
        for coefficient in coefficients:
            assert s.Poly(coefficient, u).degree() <= 1 or coefficient == 0
            values = (coefficient.subs(u, 0), coefficient.subs(u, HALF))
            if all(value == 0 for value in values):
                signs.append(0)
            else:
                sign = 1 if all(value >= 0 for value in values) else -1
                assert all(sign*value >= 0 for value in values)
                signs.append(sign)
        rows.append((quad, tuple(signs)))
    assert len(rows) == 15
    return tuple(rows)


class CircleModel(diagonal.VirtualUpper):
    def __init__(self, orientation, relations):
        assert orientation in (-1, 1)
        super().__init__(core_positive=False, independent_pair=(2, 4))
        self.clauses.append([self.bits((0, 1, 2, 4), orientation)[0]])
        # Exact spatial relations r4=r5 and r2+r7=r0+r1.
        # The latter is P7=-P2 with the actual constant height levels.
        for triple in combinations(range(8), 3):
            self.sumzero([self.bits(triple+(4,)), self.bits(triple+(5,), -1)])
            self.sumzero([self.bits(triple+(2,)), self.bits(triple+(7,)),
                          self.bits(triple+(0,), -1), self.bits(triple+(1,), -1)])
        self.sumzero([self.cross(5, 8), self.cross(4, 8, -1)])
        self.sumzero([self.cross(7, 8), self.cross(2, 8)])
        for quad, signs in relations:
            self.sumzero([self.normalized[quad][::-1]]
                         +[self.cross(node, 8, sign) for node, sign in zip((2, 4), signs) if sign])


def exact_checks():
    u, C, A, a2 = s.symbols('u C A a2')
    lu = 1-2*u
    # h3=1/2 and w=2P2 in the first orientation.
    assert s.expand((2*a2-A)*C+2*(A/2-a2)*C) == 0
    coefficient = s.cancel(((2*a2-A)*C).subs(A, 2*a2+1/lu))
    assert s.cancel(coefficient+C/lu) == 0
    p = tuple((1-i) % 8 for i in range(8))
    literal = boundary.shared.common.lit
    assert literal(tuple(p[i] for i in (0, 1, 2, 3))) == literal((0, 1, 6, 7))
    assert (-4) % 8 == 4  # The unique deficit d4=1/2 is preserved.
    P, N = s.Matrix(s.symbols('px py')), s.Matrix(s.symbols('nx ny'))
    transverse = (s.zeros(2, 1), s.zeros(2, 1), P, s.zeros(2, 1),
                  N, N, s.zeros(2, 1), -P)
    levels = (0, HALF, HALF, HALF, u, u, 0, 0)
    transformed = tuple(-transverse[p[i]] for i in range(8))
    expected = (s.zeros(2, 1), s.zeros(2, 1), P, s.zeros(2, 1),
                -N, -N, s.zeros(2, 1), -P)
    assert transformed == expected
    assert tuple(s.expand(HALF-levels[p[i]]) for i in range(8)) == (
        0, HALF, HALF, HALF, HALF-u, HALF-u, 0, 0)
    assert s.det(-s.eye(3)) == -1
    return {'relative_diagonal_source': diagonal.metric_checks(),
            'marked_reflection': boundary.symmetry_checks(),
            'circle_reflection_preserves_family_and_reverses_C24': True,
            'positive_divided_bracket_term': '-C24/(1-2u)>0 when C24<0',
            'small_cross_terms_at_vertex7': 'C27=0 and cross(2P2,P7)=0'}


def build(directory):
    directory.mkdir(parents=True, exist_ok=True)
    relations = circle_relations()
    checks = exact_checks()
    obligations = []
    for orientation in (-1, 1):
        model = CircleModel(orientation, relations)
        if orientation == -1:
            # Negate C2w=0, C4w>0, generic1234<0, generic1237>0.
            violation = list(model.cross(2, 8))+[-model.cross(4, 8)[0],
                        boundary.shared.common.lit((1, 2, 3, 4)),
                        -boundary.shared.common.lit((1, 2, 3, 7))]
            claim = 'w=2P2, generic1234<0 and generic1237>0'
        else:
            violation = [boundary.shared.common.lit((0, 1, 6, 7))]
            claim = 'generic0167<0 permits the marked reflection to C24<0'
        clauses = model.clauses+[violation]
        with FastSAT(model.n, clauses) as solver:
            assert solver.check() == -1, orientation
        name = f'c0_circle_virtual_{"negative" if orientation < 0 else "positive"}.cnf'
        write_cnf(directory/name, model.n, clauses)
        obligations.append({'file': name, 'orientation_C24': orientation,
                            'claim': claim, 'variables': model.n, 'clauses': len(clauses)})
    packet = {'checks': checks, 'exact_diagonal_height_relations': len(relations),
              'unsat_obligations': obligations,
              'excluded': 'nonflat coincident45 circle of interior ray1 C0',
              'remaining': 'the two line directions and the other common-line families',
              'relative_rate_assumptions': [], 'whole_flat_C0_exclusion_claimed': False}
    (directory/'circle.json').write_text(json.dumps(packet, indent=2)+'\n')
    return packet


if __name__ == '__main__':
    if not __debug__:
        raise RuntimeError('run with assertions enabled')
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('output', type=Path)
    record = build(parser.parse_args().output)
    print(json.dumps({'unsat_obligations': len(record['unsat_obligations']),
                      'excluded': record['excluded']}), flush=True)
