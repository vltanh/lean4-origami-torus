#!/usr/bin/env python3
"""Zero-safe bracket implications for a collinear upper C1 cap.

Usage: python solver_remaining_c1_collinear.py OUTPUT_DIRECTORY

The lower cap067 is noncollinear and positively oriented. The five
exported UNSAT formulas require independent RUP replay. Actual bracket
zeros leave their generic completion signs free.
"""

import argparse
from itertools import combinations, product
import json
from pathlib import Path

import sympy as sym

import solver_remaining_chambers as shared
from solver_chambers import write_cnf
from solver_sat import FastSAT

QUADS = tuple(combinations(range(8), 4))
CASES = {'4_between_2_3': (4, (2, 3)),
         '2_between_3_4': (2, (3, 4)),
         '2_equals_4': (4, (2,))}
FIRST = (0, 1, 2, 7)
EXTRA = ((3, 4, 5, 6), (4, 5, 6, 7))


def symbolic_checks():
    # Universal affine five-point cocycle, in the exact deletion order.
    points = [sym.Matrix(sym.symbols(f'x{i} y{i} z{i}')) for i in range(5)]
    det = lambda q: sym.Matrix.hstack(*(points[i]-points[q[0]] for i in q[1:])).det()
    assert sym.expand(sum((-1)**i*det(tuple(j for j in range(5) if j != i))
                          for i in range(5))) == 0
    # Multilinearity after replacing one affine point by a convex combination.
    lam = sym.Symbol('lambda')
    middle = lam*points[3]+(1-lam)*points[4]
    left = sym.Matrix.hstack(points[1]-points[0], points[2]-points[0], middle-points[0]).det()
    assert sym.expand(left-lam*det((0, 1, 2, 3))-(1-lam)*det((0, 1, 2, 4))) == 0
    # The three-term rank-four GP identity after fixing its common two columns.
    vectors = [sym.Matrix(sym.symbols(f'a{i} b{i}')) for i in range(4)]
    cross = lambda i, j: sym.Matrix.hstack(vectors[i], vectors[j]).det()
    assert sym.expand(cross(0, 1)*cross(2, 3)-cross(0, 2)*cross(1, 3)
                      +cross(0, 3)*cross(1, 2)) == 0
    # Positive deficit1 makes the anchor bracket nonzero in these cases.
    alpha, p, q, r = sym.symbols('alpha p q r')
    h = sym.Rational(1, 2)-r
    rho = alpha*(q+r)+(1-alpha)*(sym.Rational(1, 2)-p)
    factor = (2*alpha*r*(sym.Rational(1, 2)-r-q)
              +(1-alpha)*(sym.Rational(1, 2)-p-q-r+2*p*r))
    assert sym.expand(2*h*rho-q-factor) == 0
    return {'affine_cocycle': True, 'convex_interpolation': True,
            'three_term_gp': True, 'strict_anchor_factor': True}


class ActualBracketModel:
    def __init__(self, case):
        middle, parents = CASES[case]
        self.n, base, *_ = shared.base_formula()
        self.clauses = [list(row) for row in base]
        self.trits = {}
        # The two strict axial cuts persist under sufficiently small
        # generic perturbation, even though the upper cap is collinear.
        for high in ({2, 3, 4}, {1, 2, 3, 4, 5}):
            for support in combinations(range(8), 5):
                if set(support) <= high or not set(support) & high:
                    continue
                row = [(1 if vertex in high else -1)*(-1)**i
                       *shared.common.lit(support[:i]+support[i+1:])
                       for i, vertex in enumerate(support)]
                self.clauses.extend((row, [-literal for literal in row]))
        for index, quad in enumerate(QUADS):
            positive, negative = self.new_trit()
            self.trits[quad] = positive, negative
            self.clauses.extend(([-positive, index+1], [-negative, -index-1]))
        for support in combinations(range(8), 5):
            self.sumzero([self.bits(support[:i]+support[i+1:], (-1)**i)
                          for i in range(5)])
        for quad in QUADS:
            if middle in quad:
                forms = [self.bits(tuple(parent if vertex == middle else vertex for vertex in quad))
                         for parent in parents]
                self.sumzero(forms+[self.bits(quad, -1)])
        # A lower triangle with positive area and every other height>0.
        for vertex in range(8):
            if vertex not in (0, 6, 7):
                self.clauses.append([self.bits((0, 6, 7, vertex))[0]])
        self.add_weak_gp()

    def new_trit(self):
        result = self.n+1, self.n+2
        self.n += 2
        self.clauses.append([-result[0], -result[1]])
        return result

    def bits(self, quad, sign=1):
        if len(set(quad)) < 4:
            return None
        parity = (-1)**sum(quad[i] > quad[j] for i, j in combinations(range(4), 2))
        pair = self.trits[tuple(sorted(quad))]
        return pair if parity*sign > 0 else pair[::-1]

    def sumzero(self, forms):
        forms = [form for form in forms if form is not None]
        # A nonzero real sum cannot have only one sign. All-zero is allowed.
        for positive, negative in forms:
            self.clauses.extend(([-positive]+[form[1] for form in forms],
                                 [-negative]+[form[0] for form in forms]))

    @staticmethod
    def deny(bits, value):
        return [-bits[0]] if value == 1 else [-bits[1]] if value == -1 else list(bits)

    def add_weak_gp(self):
        cache = {}

        def multiply(left, right):
            key = tuple(sorted((left, right)))
            if key not in cache:
                result = self.new_trit()
                for a, b, c in product((-1, 0, 1), repeat=3):
                    if a*b != c:
                        self.clauses.append(self.deny(left, a)+self.deny(right, b)+self.deny(result, c))
                cache[key] = result
            return cache[key]

        for common in combinations(range(8), 2):
            for a, b, c, d in combinations([vertex for vertex in range(8) if vertex not in common], 4):
                self.sumzero((multiply(self.bits(common+(a, b)), self.bits(common+(c, d))),
                              multiply(self.bits(common+(a, c), -1), self.bits(common+(b, d))),
                              multiply(self.bits(common+(a, d)), self.bits(common+(b, c)))))


def build(directory):
    directory.mkdir(parents=True, exist_ok=True)
    identities = symbolic_checks()
    obligations = []
    for case in CASES:
        source = ActualBracketModel(case)
        stages = [('two_signs', (FIRST, EXTRA[1]), False)]
        if case != '2_equals_4':
            stages.append(('three_signs_strict_anchor', (FIRST,)+EXTRA, True))
        for stage, targets, strict in stages:
            clauses = source.clauses+[[source.bits(quad)[0] for quad in targets]]
            if strict:
                clauses.append([source.bits((0, 1, 2, 3))[0]])
            with FastSAT(source.n, clauses) as solver:
                assert solver.check() == -1
            filename = f'c1_collinear_{case}_{stage}.cnf'
            write_cnf(directory/filename, source.n, clauses)
            obligations.append({'file': filename, 'case': case, 'strict_0123': strict,
                                'nonpositive_actual_brackets': targets,
                                'variables': source.n, 'clauses': len(clauses)})
    assert len(obligations) == 5
    packet = {'assumptions': ['0<alpha,beta<1', 'positively oriented noncollinear067',
                              'the stated exact collinear order of234'],
              'identities': identities, 'unsat_obligations': obligations,
              'actual_zero_semantics': 'neither trit bit; generic sign remains free',
              'whole_collinear_boundary_exclusion': False}
    (directory/'c1_collinear.json').write_text(json.dumps(packet, indent=2)+'\n')
    return packet


if __name__ == '__main__':
    if not __debug__:
        raise RuntimeError('run with assertions enabled')
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('output', type=Path)
    result = build(parser.parse_args().output)
    print(json.dumps({'unsat_obligations': len(result['unsat_obligations']),
                      'whole_collinear_boundary_exclusion': False}), flush=True)
