#!/usr/bin/env python3
"""Classify common-line endpoint caps of interior ray-1 C0.

Nine actual-trit certificates control the two remaining transverse
coordinates.  Exact metric identities reduce the common-line case to
four endpoint-deficit families, four middle-deficit families, and one
coincident45 circle.  This is a limit classification, not an exclusion.
"""

import argparse
from itertools import combinations, product
import json
from math import comb, factorial
from pathlib import Path

import sympy as s

import exhaustive_c0_collinear as boundary
import exhaustive_c0_turning as turning
import remaining_c0_height_order as metric
import solver_remaining_c1_geometry as geometry
import solver_remaining_limit as reduction
from solver_chambers import write_cnf
from solver_sat import FastSAT

HALF = s.Rational(1, 2)
QUADS = tuple(combinations(range(8), 4))
UPPER = {'a': (3, (1, 2)), 'b': (1, (2, 3)), 'd': (3, (1,))}
LOWER = {'a': (0, (6, 7)), 'b': (6, (0, 7)), 'd': (6, (0,))}
MIXED = ((2, 3, 4, 5), (3, 4, 5, 6), (4, 5, 6, 7))
L, M, U, V = s.symbols('L M u v')


class FlatModel(boundary.trit_source.ActualBracketModel):
    def __init__(self, upper, lower, relations):
        self.n, base, *_ = boundary.shared.base_formula()
        self.clauses = [list(row) for row in base]
        self.trits = {}
        for high in ({1, 2, 3}, {1, 2, 3, 4, 5}):
            for support in combinations(range(8), 5):
                if set(support) <= high or not set(support) & high:
                    continue
                row = [(1 if vertex in high else -1)*(-1)**i
                       *boundary.shared.common.lit(support[:i]+support[i+1:])
                       for i, vertex in enumerate(support)]
                self.clauses.extend((row, [-literal for literal in row]))
        for index, quad in enumerate(QUADS):
            positive, negative = self.new_trit()
            self.trits[quad] = positive, negative
            self.clauses.extend(([-positive, index+1], [-negative, -index-1]))
        for support in combinations(range(8), 5):
            self.sumzero([self.bits(support[:i]+support[i+1:], (-1)**i)
                          for i in range(5)])
        for triangle in ((1, 2, 3), (0, 6, 7)):
            for vertex in range(8):
                if vertex not in triangle:
                    self.clauses.extend([[-bit] for bit in self.bits(triangle+(vertex,))])
        for middle, parents in (UPPER[upper], LOWER[lower]):
            for quad in QUADS:
                if middle in quad:
                    self.sumzero([self.bits(tuple(parent if vertex == middle else vertex
                                                       for vertex in quad))
                                  for parent in parents]+[self.bits(quad, -1)])
        self.add_weak_gp()
        for quad, terms in relations:
            self.sumzero([self.bits(quad)]+[self.bits((0, 1)+pair, -sign)
                                            for pair, sign in terms])


def common_line_links(model, upper, lower):
    """Bind actual minors to the signs of the two transverse heights.

    E/h2=F/h6=(1,0), P2 and P7 point oppositely.  The strict a/b
    parameters lie in (0,1/2); d is the exact coincident endpoint.
    No formula divides by L, M, or an actual bracket.
    """
    h1 = HALF-L if upper == 'b' else HALF
    h7 = HALF-M if lower == 'a' else HALF
    p3 = {'a': -L, 'b': L, 'd': s.Integer(0)}[upper]
    p6 = {'a': -M, 'b': M, 'd': s.Integer(0)}[lower]
    x4, y4, x5, y5 = s.symbols('x4 y4 x5 y5')
    points = [s.Matrix([0, 0, 0]), s.Matrix([0, 0, HALF]),
              s.Matrix([-h1, 0, HALF]), s.Matrix([p3, 0, HALF]),
              s.Matrix([x4, y4, U]), s.Matrix([x5, y5, V]),
              s.Matrix([p6, 0, 0]), s.Matrix([h7, 0, 0])]
    substitution = ({L: 0} if upper == 'd' else {}) | ({M: 0} if lower == 'd' else {})
    points = [point.subs(substitution) for point in points]
    counts = {'zero': 0, 'signed': 0}
    for quad in QUADS:
        first, *rest = quad
        expression = s.factor(s.det(s.Matrix.hstack(*(points[i]-points[first] for i in rest))))
        varying = set(quad) & {4, 5}
        if len(varying) == 2:
            continue
        if not varying:
            assert expression == 0
            coefficient = 0
        else:
            target = y4 if 4 in quad else y5
            coefficient = s.factor(expression/target)
            assert not (coefficient.free_symbols-{L, M})
            assert s.Poly(coefficient, L, M).total_degree() <= 1
        if coefficient == 0:
            model.clauses.extend([[-bit] for bit in model.bits(quad)])
            counts['zero'] += 1
            continue
        corners = [coefficient.subs({L: a, M: b}) for a, b in product((0, HALF), repeat=2)]
        sign = 1 if all(value >= 0 for value in corners) else -1
        assert all(sign*value >= 0 for value in corners)
        assert sign*coefficient.subs({L: s.Rational(1, 8), M: s.Rational(1, 8)}) > 0
        # A nonzero affine form weakly signed on the closed square is
        # strictly signed in its interior. Substituted d coordinates
        # have already been removed before this check.
        reference = (0, 2, 3, 4 if 4 in quad else 5)
        model.sumzero([model.bits(quad), model.bits(reference, -sign)])
        counts['signed'] += 1
    return counts


def gram_face_checks():
    """Three explicit positive coefficients extend the existing lemma."""
    variables = s.symbols('a b c d e')
    a, b, c, d, e = variables
    k, ell = s.symbols('k ell')
    h, j = (1-a)/2, (1-e)/2
    p, q, g = b/2, c/2, d/2
    sigma, tau = HALF-p+k*(p+q), HALF-g+ell*(q+g)
    ns, nw = sigma*sigma-2*k*q, tau*tau-2*ell*q
    cc = sigma*tau-(1+k*ell)*q
    aa, bb = (1-sigma)*h-p, (1-tau)*j-g
    polynomial = s.Poly(s.expand(64*(aa*aa*j*j*nw+bb*bb*h*h*ns+cc*cc*h*h*j*j
                                    +2*aa*bb*h*j*cc-ns*nw*h*h*j*j)), *variables, k, ell)

    def coefficient(block, target):
        total = 0
        i, j0 = block
        for exponent, value in polynomial.terms():
            ka, la = exponent[-2:]
            if ka > i or la > j0 or any(x > y for x, y in zip(exponent[:5], target)):
                continue
            extra = tuple(y-x for x, y in zip(exponent[:5], target))
            degree = 8-sum(exponent[:5])
            assert sum(extra) == degree
            multiple = factorial(degree)
            for power in extra:
                multiple //= factorial(power)
            total += value*s.Rational(comb(i, ka)*comb(j0, la), comb(2, ka)*comb(2, la))*multiple
        return s.cancel(total)

    targets = [((2, 2), (4, 0, 4, 0, 0), 1),
               ((2, 2), (0, 0, 4, 0, 4), 1),
               ((0, 0), (0, 4, 0, 4, 0), 6)]
    for block, target, expected in targets:
        assert coefficient(block, target) == expected
    return {'base_nonnegative_certificate': metric.positive_gram_certificate(),
            'b0_face_coefficients': [(block, target, value) for block, target, value in targets]}


def scalar_checks():
    p, q, g, D, u, v, h, j = s.symbols('p q g D u v h j')
    lu, lv, gap = 1-2*u, 1-2*v, v-u
    r, ss = HALF-p-lu*D, HALF-g-2*v*D
    budget = {q: HALF-D-p-g}
    assert s.expand((q-2*r*ss).subs(budget)-2*(gap*D-(p+lu*D)*(g+2*v*D))) == 0
    assert s.expand((r+ss)**2-2*q-(p+g)**2).subs(D, 0).subs(q, HALF-p-g) == 0
    assert s.expand((p+g)**2-(p-g)**2-4*p*g) == 0
    # Opposite-sign line branch Q4=-r e, Q5=s e, q=0.
    sub = {D: HALF-p-g}
    RS, RW = lv*r+lu*ss, v*r+u*ss
    assert s.cancel((2*RS-lv+lv*p/h).subs(sub)-p*(4*gap+lv/h)) == 0
    assert s.cancel((2*RW-u+u*g/j).subs(sub)-g*(2*gap+u/j)) == 0
    assert s.expand(v*lu-gap-u*lv) == 0
    # The same-positive line branch gives g*d6=2v*D*h6.
    d6 = s.Symbol('d6')
    assert s.expand((j*(2*ss-1)+g).subs(j, HALF-d6)-2*(g*d6-2*v*D*(HALF-d6))) == 0
    return {'line_scalar_identities': 7}


def family_checks():
    """Replay all twelve closed projected stresses for every listed family."""
    u, v, length = U, V, L
    e = s.Matrix([1, 0])
    rows = reduction.closed_c0_rows().subs({reduction.A: 1-u, reduction.B: -v})
    records = []

    def check(name, d, points, substitution=None, circle=False):
        substitution = substitution or {}
        assert s.cancel(sum(d)-HALF) == 0
        h = [HALF-value for value in d]
        X = geometry.horizontal_displacements(h)
        residuals = []
        for i, j in reduction.EDGES:
            delta = points[j]-points[i]
            residuals.append(s.expand(delta.dot(delta)-X[i, j]**2))
        result = rows*s.Matrix(residuals+[0]*5)
        for value in result:
            value = s.cancel(value.subs(substitution))
            if circle:
                x, y = s.symbols('x y')
                value = s.rem(s.Poly(value, y, x), s.Poly(x*x+y*y-HALF*HALF, y, x)).as_expr()
            assert s.cancel(value) == 0, (name, value)
        records.append(name)

    # Four closed endpoint-deficit families, including zero outer edges.
    for upper, lower in product('ab', repeat=2):
        d = [s.Integer(0)]*8
        d[2 if upper == 'a' else 1] = length
        d[7 if lower == 'a' else 6] = HALF-length
        h1, h7 = HALF-d[1], HALF-d[7]
        p3 = -length if upper == 'a' else length
        p6 = -(HALF-length) if lower == 'a' else HALF-length
        point = [0, 0, -h1, p3, 2*u*p3+(1-2*u)*p6-u,
                 2*v*p3+(1-2*v)*p6+(HALF-v), p6, h7]
        check('endpoint_'+upper+lower, d, [value*e for value in point])

    # Four line families with L=M=d0=0 and just one of d3,d5 positive.
    for name, index, deficit, p4, p5 in (
        ('middle_u_lt_v_positive', 5, (v-u)/(1-2*u), HALF, HALF-(v-u)/(1-2*u)),
        ('middle_u_lt_v_negative', 3, (v-u)/(2*v), -(HALF-(v-u)/(2*v)), -HALF),
        ('middle_u_gt_v_positive', 3, (u-v)/(1-2*v), HALF-(u-v)/(1-2*v), HALF),
        ('middle_u_gt_v_negative', 5, (u-v)/(2*u), -HALF, -(HALF-(u-v)/(2*u))),
    ):
        d = [s.Integer(0)]*8
        d[index], d[4] = deficit, HALF-deficit
        check(name, d, [value*e for value in (0, 0, -HALF, 0, p4, p5, 0, HALF)])

    x, y = s.symbols('x y')
    d = [s.Integer(0)]*8
    d[4] = HALF
    points = [s.zeros(2, 1), s.zeros(2, 1), -HALF*e, s.zeros(2, 1),
              s.Matrix([x, y]), s.Matrix([x, y]), s.zeros(2, 1), HALF*e]
    check('diagonal_coincident45_circle', d, points, {v: u}, circle=True)
    assert len(records) == 9
    return {'families': records, 'projected_stresses_per_family': 12,
            'auxiliary_or_nonedge_sufficiency_claimed': False}


def build(directory):
    directory.mkdir(parents=True, exist_ok=True)
    relations = boundary.height_relations()
    obligations = []
    for upper, lower in product('abd', repeat=2):
        source = FlatModel(upper, lower, relations)
        counts = common_line_links(source, upper, lower)
        y4, y5 = source.bits((0, 2, 3, 4)), source.bits((0, 2, 3, 5))
        # Negate the three allowed alternatives: both zero; both positive
        # with all mixed minors <=0; both negative with all >=0.
        bad = [list(y4)+list(y5),
               [-y4[0], -y5[0]]+[source.bits(quad)[0] for quad in MIXED],
               [-y4[1], -y5[1]]+[source.bits(quad)[1] for quad in MIXED]]
        clauses = source.clauses+bad
        with FastSAT(source.n, clauses) as solver:
            assert solver.check() == -1, upper+lower
        filename = f'c0_flat_common_{upper}{lower}.cnf'
        write_cnf(directory/filename, source.n, clauses)
        obligations.append({'file': filename, 'variables': source.n, 'clauses': len(clauses),
                            'exact_links': counts})
    checks = {'source_metric': metric.metric_bindings(), 'source_core': turning.verify(),
              'symmetry': boundary.symmetry_checks(), 'gram_faces': gram_face_checks(),
              'scalar': scalar_checks(), 'family_replays': family_checks()}
    packet = {'checks': checks, 'unsat_obligations': obligations,
              'scope': 'interior ray1 C0 with both endpoint caps on one transverse line',
              'classification_families': 9,
              'nonparallel_cap_lines_or_sequence_exclusion_claimed': False}
    (directory/'flat_common.json').write_text(json.dumps(packet, indent=2)+'\n')
    return packet


if __name__ == '__main__':
    if not __debug__:
        raise RuntimeError('run with assertions enabled')
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('output', type=Path)
    packet = build(parser.parse_args().output)
    print(json.dumps({'unsat_obligations': len(packet['unsat_obligations']),
                      'classification_families': packet['classification_families'],
                      'sequence_exclusion_claimed': False}), flush=True)
