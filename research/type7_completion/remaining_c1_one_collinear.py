#!/usr/bin/env python3
"""Exact obligations for ray-2 C1 with exactly one collinear endpoint cap.

Usage: python remaining_c1_one_collinear.py OUTPUT_DIRECTORY

The proof uses limiting sections of actual embedded sequences.  Eight
exported CNFs require independent RUP replay.  Actual zero brackets never
fix their generic completion signs.  Both-collinear caps and height
endpoints are outside this package's scope.
"""

import argparse
from itertools import combinations, product
import json
from pathlib import Path
import time

import sympy as S

import remaining_c1_sections as sections
import solver_remaining_c1_collinear as collinear
import solver_remaining_c1_collinear_rank as rank
import solver_remaining_chambers as shared
from solver_chambers import write_cnf
from solver_sat import FastSAT


HALF = S.Rational(1, 2)
STRICT_ORDERS = {
    '4_between_2_3': (4, (2, 3)),
    '2_between_3_4': (2, (3, 4)),
    '3_between_2_4': (3, (2, 4)),
}
# Every omitted magnitude is strictly positive in the bad collinear
# critical quadrilateral; see arrow_checks and the companion proof.
ARROW_RELATIONS = (
    ((5, 1), (3, 1), (4, -1), (6, -1)),
    ((7, 1), (4, 1), (6, -1), (3, -1)),
    ((5, 1), (7, 1), (4, -1), (6, -1)),
)


def generic_source():
    n, base, *_ = shared.base_formula()
    assert base[0] == [1]
    # Remove only the freely chosen ambient orientation [0123]>0.
    # All embedding and absolute-linking constraints remain present.
    clauses = [list(row) for row in base[1:]]
    literal = shared.common.lit
    for high in ({2, 3, 4}, {1, 2, 3, 4, 5}):
        for support in combinations(range(8), 5):
            if set(support) <= high or not set(support) & high:
                continue
            row = [(1 if vertex in high else -1) * (-1) ** i
                   * literal(support[:i] + support[i + 1:])
                   for i, vertex in enumerate(support)]
            clauses.extend((row, [-value for value in row]))
    for vertex in (1, 2, 3, 4, 5):
        clauses.append([literal((0, 6, 7, vertex))])
    return n, clauses


class ActualModel(collinear.ActualBracketModel):
    """Reuse the audited trit operations, with the three strict orders."""

    def __init__(self, case):
        middle, parents = STRICT_ORDERS[case]
        self.n, self.clauses = generic_source()
        self.trits = {}
        for index, quad in enumerate(collinear.QUADS):
            positive, negative = self.new_trit()
            self.trits[quad] = positive, negative
            self.clauses.extend(([-positive, index + 1], [-negative, -index - 1]))
        for support in combinations(range(8), 5):
            self.sumzero([self.bits(support[:i] + support[i + 1:], (-1) ** i)
                          for i in range(5)])
        for quad in collinear.QUADS:
            if middle in quad:
                forms = [self.bits(tuple(parent if vertex == middle else vertex
                                         for vertex in quad)) for parent in parents]
                self.sumzero(forms + [self.bits(quad, -1)])
        for vertex in (1, 2, 3, 4, 5):
            self.clauses.append([self.bits((0, 6, 7, vertex))[0]])
        for relation in rank.HEIGHT_SIGNS:
            self.sumzero([self.bits(quad, sign) for quad, sign in relation])
        self.add_weak_gp()


def budget_and_symmetry_checks():
    h = S.symbols('h0:8')
    slacks = [h[i] + h[i + 1] - HALF for i in (0, 2, 4, 6)]
    assert S.expand(sum(slacks) - (sum(h) - 2)) == 0
    # P2=P4 gives h2=h3=1/2 and consumes the entire ray-2 slack
    # budget.  The regular lower cap has strictly positive slack.
    assert slacks[1].subs({h[2]: HALF, h[3]: HALF}) == HALF
    m, s = S.symbols('M s')
    # P2=P3: h1=h3=1/2, h2=0.  Write h4+h5=1/2+s.
    reduced = sum(h).subs({h[1]: HALF, h[2]: 0, h[3]: HALF,
                          h[0]: m - s, h[5]: HALF + s - h[4],
                          h[7]: 1 - m - h[6]})
    assert S.expand(reduced - S.Rational(5, 2)) == 0
    symmetries = rank.symbolic_checks()
    reflection = tuple((6 - i) % 8 for i in range(8))
    literal = shared.common.lit
    assert literal(tuple(reflection[i] for i in (0, 1, 5, 6))) == literal((0, 1, 5, 6))
    # Reflection of the ambient transverse plane then reverses both the
    # lower-cap sign and L, and swaps the two annuli.
    return {'pair_slack_budget': True, 'zero_edge_budget': True,
            'annulus_reflection_literal': True,
            'marked_symmetries': symmetries['marked_symmetries'],
            'height_relations': symmetries['height_identities']}


def arrow_checks():
    b, h, k, rho = S.symbols('beta h k rho')
    q = 1 - b
    h4 = HALF - 2 * h * rho
    h5 = HALF - k * (1 - 2 * b * h)
    rho_definition = b * (1 - h - h4) + q * h5
    assert S.expand(rho - rho_definition - (1 - 2 * b * h) * (rho - HALF + q * k)) == 0
    rho = HALF - q * k
    n, tau = HALF - b * h - q * k, HALF - b * h
    assert S.expand(rho - b * h - n) == 0
    assert S.expand(q * k + n - tau) == 0
    assert S.expand(n - (b * (HALF - h) + q * (HALF - k))) == 0
    assert S.expand(tau - ((1 - b) * HALF + b * (HALF - h))) == 0

    p3 = S.Matrix(S.symbols('x3 y3'))
    p6 = S.Matrix(S.symbols('x6 y6'))
    e = S.Matrix(S.symbols('ex ey'))
    p4, p7 = p3 + h * e, p6 - k * e
    p5 = b * p3 + q * p6 + rho * e
    points = {i: p.col_join(S.Matrix([z])) for i, p, z in
              ((3, p3, HALF), (4, p4, HALF), (5, p5, b / 2),
               (6, p6, 0), (7, p7, 0))}
    weighted = (
        ((5, 1), (3, n / h), (4, -rho / h), (6, -q)),
        ((7, 1), (4, k / h), (6, -1), (3, -k / h)),
        ((5, 1), (7, n / k), (4, -b), (6, -tau / k)),
    )
    for relation in weighted:
        assert S.cancel(sum(value for _, value in relation)) == 0
        sections.equal_vectors(sum((value * points[i] for i, value in relation), S.zeros(3, 1)),
                               S.zeros(3, 1))
    return {'arrow_metric_factor': True, 'arrow_positive_affine_dependencies': 3}


def zero_edge_spur_checks():
    a, b, t, k, h4, h5, d = S.symbols('alpha beta t k h4 h5 D')
    qa, qb = 1 - a, 1 - b
    p3, p6, p7, p5 = [S.Matrix(S.symbols(f'x{i} y{i}')) for i in (3, 6, 7, 5)]
    e = S.Matrix(S.symbols('ex ey'))
    p4 = p3 + HALF * e
    r, lam = (t - a) / qa, (1 - t) / qa
    base, tip = r * p3, r * p4
    y0, z0 = a * p3, a * p3 + qa * p7
    triangle = (base, t * p3, t * p3 + (1 - t) * p7)
    for vertex, critical in zip(triangle, (S.zeros(2, 1), y0, z0)):
        sections.equal_vectors(vertex, base + lam * critical)
    sections.equal_vectors(tip - base, r * HALF * e)

    x = (1 - t) * p6 + t * p3
    y = (1 - t) * p6 + t * p4
    z = (1 - t) * p7 + t * p4
    v3 = (1 - t) / qb * p5 + (t - b) / qb * p3
    v4 = (1 - t) / qb * p5 + (t - b) / qb * p4
    r5 = p5 - b * p3 - qb * p6
    sections.equal_vectors(y - x, t * HALF * e)
    sections.equal_vectors(v4 - v3, (t - b) / qb * HALF * e)
    sections.equal_vectors(v3 - x, (1 - t) / qb * r5)
    sections.equal_vectors(z - y, (1 - t) * (p7 - p6))
    sections.equal_vectors(y - tip, (1 - t) / qa * (a * p3 + qa * p6 + a * HALF * e))

    # Once the two long edges are on the outer spur, R5 and F are
    # parallel to e.  The first dot identity splits into these two cases.
    rho = b * (HALF - h4) + qb * h5
    sigma = qb * (1 - h5) + b * h4
    assert S.expand(rho - (HALF - h4) - qb * (h4 + h5 - HALF)) == 0
    # R5=+rho e: h4+h5=1/2.
    positive = {h5: HALF - h4}
    yp = b * HALF - rho
    low_plus = k * yp + k * sigma - (HALF - h5)
    assert S.expand(low_plus.subs(positive) - h4 * (2 * k - 1)) == 0
    low_minus = -k * yp + k * sigma - (HALF - h5)
    assert S.expand(low_minus.subs(positive) - (qb * k - h4)) == 0
    # R5=-rho e: h4=1/2.
    yn = b * HALF + rho
    low_plus = k * yn + k * sigma - (HALF - h5)
    assert S.expand(low_plus.subs(h4, HALF) - (k - HALF + h5)) == 0
    low_minus = -k * yn + k * sigma - (HALF - h5)
    assert S.expand(low_minus.subs(h4, HALF) - (2 * qb * k - 1) * (HALF - h5)) == 0
    # The two +F cases traverse their full segment once in each direction.
    assert S.expand(yp.subs({h4: 0, h5: HALF}) + qb * HALF) == 0
    assert S.expand((yp + qb * k).subs({h4: 0, h5: HALF}) + qb * (HALF - k)) == 0
    assert S.expand((yn + qb * k).subs({h4: HALF, h5: HALF - k}) - HALF) == 0
    # In the remaining -F,+R case, the budget gives h0=M.
    # D<=-alpha/2 implies D-qa*k<0, and the Z0 norm forces D=-alpha/2.
    assert S.expand(-(d - qa * k) - (a * HALF + qa * k) + d + a * HALF) == 0
    m = S.Symbol('M')
    h0 = m
    rho1 = a * HALF + qa * h0
    tau0 = qa * (1 - h0) + a * HALF - qa * (1 - m - k)
    assert S.expand(tau0 - (a * HALF + qa * k)) == 0
    assert S.expand(rho1 - (a * HALF + qa * m)) == 0
    return {'outer_spur_triangle_identities': 3, 'outer_spur_endpoint_identity': True,
            'inner_spur_edge_identities': 5, 'zero_edge_parallel_cases': 4,
            'zero_edge_norm_equality': True}


def coincident_lower_checks():
    zero = S.zeros(2, 1)
    x, y, z = (S.Matrix(S.symbols(f'{name}0 {name}1')) for name in ('X', 'Y', 'Z'))
    b = (zero, x, y, z)
    for shift in range(4):
        a = tuple(b[(i + shift) % 4] for i in range(4))
        closure = a[0] + a[2] - a[3] - b[1] + b[2] - b[3]
        lower = sections.cross(a[0] - b[1], b[3] - b[2])
        if shift == 0:
            assert S.expand(lower - sections.cross(closure, z - y)) == 0
        elif shift == 1:
            assert S.expand(lower) == 0
        else:
            assert S.expand(lower - sections.cross(y - x, z - y)) == 0

    s, t = S.symbols('s t')
    triangle = (zero, S.Matrix([1, 0]), S.Matrix([0, -1]))

    def polygon(flat, rotation, fraction):
        vertices = [None] * 4
        for index, vertex in enumerate(i for i in range(4) if i != flat):
            vertices[vertex] = triangle[(index + rotation) % 3]
        vertices[flat] = ((1 - fraction) * vertices[(flat - 1) % 4]
                          + fraction * vertices[(flat + 1) % 4])
        return vertices

    rows = []
    for flat_b, flat_a, rotation in product((1, 2, 3), (0, 2, 3), range(3)):
        b, a = polygon(flat_b, 0, s), polygon(flat_a, rotation, t)
        equations = a[0] + a[2] - a[3] - b[1] + b[2] - b[3]
        solutions = list(S.linsolve(list(equations), (s, t)))
        lower = S.factor(sections.cross(a[0] - b[1], b[3] - b[2]))
        if not solutions:
            kind, solution = 'inconsistent', None
        else:
            assert len(solutions) == 1
            ss, tt = solutions[0]
            solution = str((ss, tt))
            if not (ss.free_symbols | tt.free_symbols):
                assert not (0 < ss < 1 and 0 < tt < 1)
                kind = 'endpoint_or_outside'
            elif tt == t and S.expand(ss - t) in (-1, 1):
                kind = 'endpoint_or_outside'
            else:
                assert ss == tt == t
                lower = S.factor(lower.subs(s, t))
                assert lower in (t - 1, 0, -t)
                kind = 'nonpositive_lower_cap'
        rows.append({'flat_b': flat_b, 'flat_a': flat_a, 'rotation': rotation,
                     'solution': solution, 'lower_cap_numerator': str(lower),
                     'obstruction': kind})
    # If h3=0, A0=A3 is represented by flat A0 at fraction zero.
    # B has four positive edges, so its unique flat fraction is interior.
    endpoint_rows = []
    for flat_b, rotation in product((1, 2, 3), range(3)):
        b, a = polygon(flat_b, 0, s), polygon(0, rotation, 0)
        assert a[0] == a[3]
        equations = a[0] + a[2] - a[3] - b[1] + b[2] - b[3]
        solutions = list(S.linsolve(list(equations), (s,)))
        if solutions:
            assert len(solutions) == 1 and len(solutions[0]) == 1
            value = solutions[0][0]
            assert not value.free_symbols and not 0 < value < 1
        endpoint_rows.append({'flat_b': flat_b, 'rotation': rotation,
                              'solution': str(solutions)})
    return {'lower_only_quadrilateral_matches': 4, 'lower_only_triangle_matches': 27,
            'lower_only_triangle_records': rows,
            'zero_edge_triangle_matches': 9, 'zero_edge_triangle_records': endpoint_rows}


def build(directory):
    started = time.monotonic()
    identities = {**sections.metric_checks(), **sections.section_checks(),
                  **sections.finite_turn_checks(), **collinear.symbolic_checks(),
                  **budget_and_symmetry_checks(), **arrow_checks(),
                  **zero_edge_spur_checks(), **coincident_lower_checks()}
    directory.mkdir(parents=True, exist_ok=True)
    literal = shared.common.lit
    first = literal((0, 1, 5, 6))
    n, source = generic_source()
    formulas = [
        ('c1_one_collinear_nesting.cnf', n,
         source + [[first], [literal((0, 1, 5, 7))]]),
        ('c1_one_collinear_inner_a_two_turns.cnf', n,
         source + [[-first], [literal((3, 4, 5, 6)), literal((4, 5, 6, 7))]]),
    ]
    for case in STRICT_ORDERS:
        model = ActualModel(case)
        formulas.append((f'c1_one_collinear_{case}_middle_turn.cnf', model.n,
                         model.clauses + [[-first], [model.bits((3, 4, 6, 7))[1]]]))
        for relation in ARROW_RELATIONS:
            for triple in combinations(range(8), 3):
                model.sumzero([model.bits(triple + (vertex,), sign)
                               for vertex, sign in relation])
        formulas.append((f'c1_one_collinear_{case}_backtracking.cnf', model.n,
                         model.clauses + [[-first]]))
    obligations = []
    for filename, variables, clauses in formulas:
        with FastSAT(variables, clauses) as solver:
            assert solver.check() == -1, filename
        write_cnf(directory / filename, variables, clauses)
        obligations.append({'file': filename, 'variables': variables, 'clauses': len(clauses)})
    assert len(obligations) == 8
    packet = {'domain': 'ray2 C1; exactly one collinear cap; 0<alpha,beta<1',
              'requires_original_embedded_sequence': True,
              'actual_zero_semantics': 'neither trit bit; generic sign remains free',
              'both_collinear_caps_excluded': False, 'height_endpoints_excluded': False,
              'identities': identities, 'unsat_obligations': obligations,
              'replay_seconds': time.monotonic() - started}
    (directory / 'c1_one_collinear.json').write_text(json.dumps(packet, indent=2) + '\n')
    return packet


if __name__ == '__main__':
    if not __debug__:
        raise RuntimeError('run with assertions enabled')
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('output', type=Path)
    result = build(parser.parse_args().output)
    print(json.dumps({key: value for key, value in result.items() if key != 'identities'}))
