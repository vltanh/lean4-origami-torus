#!/usr/bin/env python3
"""Exclude all 176 two-line first blow-ups with exactly three zero weights.

Usage: python exhaustive_three_zero_blowup.py [OUTPUT_DIRECTORY]

Three independently normalized short edges give sixteen finite sign
certificates.  Three relative-height calculations finish the surviving
cells.  No comparison across cap edge lengths or between width and t
is assumed.  See exhaustive_three_zero_blowup.md.
"""

from collections import Counter
from itertools import combinations, product
import json
from pathlib import Path
import sys

import sympy as s

import common_line_edge_collapse as two_line
from direct_metric import load_data
import exhaustive_collinear_caps as collinear
import exhaustive_two_single_blowup as two_single
from remaining_flat_blowup import rank_tuple
from remaining_one_v import DirectionalModel
import remaining_two_line_triple as triple
import solver_chambers as compiler
from verify_linking import SAT, lit

A, B = collinear.A, collinear.B
TRIPLE_ORDERS = ((2, 1, 0, 0), (1, 2, 0, 0), (2, 0, 1, 1),
                 (1, 1, 2, 0), (1, 2, 2, 0))
PARAMETERS = ((s.Rational(1, 2), 1), (-1, 1), (2, 1), (0, -1), (-1, -1))


class Directions(DirectionalModel):
    def __init__(self, variables, clauses, trits=None):
        self.n = variables
        self.clauses = [list(row) for row in clauses]
        self.trits = dict(trits or {})

    def add_trits(self, keys):
        for key in keys:
            self.trits[key] = self.n+1, self.n+2
            self.n += 2
            self.clauses.append([-self.n+1, -self.n])

    def nonzero(self, prefix):
        self.clauses.append(list(self.trits[prefix+'x'])+list(self.trits[prefix+'y']))

    def implication(self, pattern, cap, sign):
        # Negation of a conjunction of direction statements and a cap sign.
        return self.clauses+[sum((self.deny(key, value) for key, value in pattern.items()), [])
                             +[-sign*lit(cap)]]


def canonical_maps(rows, symmetries):
    phase = [entry['permutation'] for entry in symmetries if entry['phase_preserving']]
    output = []
    for row in rows:
        values = dict(zip(A, row['a'])) | dict(zip(B, row['b']))
        maps = []
        for permutation, reflection in product(phase, (-1, 1)):
            a = rank_tuple([reflection*values[permutation[i]] for i in A])
            b = rank_tuple([reflection*values[permutation[i]] for i in B])
            if a == (0, 0, 0, 1) and b in TRIPLE_ORDERS:
                maps.append((TRIPLE_ORDERS.index(b), permutation, reflection))
            if a == (0, 0, 1, 1) and b == (2, 0, 1, 1):
                maps.append((5, permutation, reflection))
        assert maps, row
        case, permutation, reflection = min(maps)
        output.append(dict(row, canonical_map={'case': case, 'permutation': permutation,
                                               'horizontal_reflection': reflection}))
    assert Counter(row['canonical_map']['case'] for row in output) == Counter({
        0: 32, 1: 32, 2: 32, 3: 32, 4: 32, 5: 16})
    return output


def triple_formula(case, hierarchy):
    lv, mv = PARAMETERS[case]
    variables, clauses, _ = triple.direction_formula(lv, mv, hierarchy)
    old = {'ax': (0,), 'ay': (1,), 'bx': (2,), 'by': (3,),
           'Ax': (0, 2), 'Ay': (1, 3), 'ab': 'ab'}
    model = Directions(variables, clauses, {key: triple.TRITS[value] for key, value in old.items()})
    model.add_trits(('dx', 'dy', 'ad', 'bd', 'Ad'))
    model.nonzero('d')
    if hierarchy == 0:
        model.clauses.extend(model.sum_clauses('ad', 'bd', 'Ad'))
    else:
        model.equal('ad' if hierarchy == -1 else 'bd', 'Ad')
    pairs = {(0, 1): 1, (0, 2): ('ay', 1), (0, 3): ('by', 1), (0, 4): ('dy', 1),
             (1, 2): ('ax', -1), (1, 3): ('bx', -1), (1, 4): ('dx', -1),
             (2, 3): ('ab', 1), (2, 4): ('ad', 1), (3, 4): ('bd', 1)}
    model.rank_two_axioms(5, pairs)
    ax, ay, bx, by, dx, dy, eps, eta, lam, mu = s.symbols('ax ay bx by dx dy eps eta lam mu')
    points = {0: (0, 0, 0), 1: (eps*ax, eps*ay, 0),
              4: (eps*(ax+bx), eps*(ay+by), 0), 5: (1, 0, 0),
              2: (0, 0, 1), 3: (0, lam, 1), 6: (0, mu, 1), 7: (0, 1, 1)}
    if case in (0, 1, 2):
        edge, relation = (6, 7), {mu: 1}
    elif case == 3:
        edge, relation = (2, 3), {lam: 0}
    else:
        edge, relation = (3, 6), {mu: lam}
    points = {i: tuple(s.sympify(value).subs(relation) for value in point)
              for i, point in points.items()}
    start, end = edge
    points[end] = (points[start][0]+eta*dx, points[start][1]+eta*dy, 1)
    forms = {'dx': dx, 'dy': dy, 'ad': ax*dy-ay*dx, 'bd': bx*dy-by*dx,
             'Ad': (ax+bx)*dy-(ay+by)*dx}
    allowed = {s.expand((x-y).subs(relation)) for x, y in product(
        map(s.sympify, (0, lam, mu, 1)), repeat=2)}-{s.Integer(0)}
    links = []
    for index, quad in enumerate(compiler.Q, 1):
        if not set(edge) <= set(quad):
            continue
        first, *rest = quad
        raw = s.expand(s.Matrix([[points[i][k]-points[first][k] for k in range(3)]
                                 for i in rest]).det())
        linear = s.expand(raw.coeff(eta, 1))
        constant = linear.subs(eps, 0)
        expression = constant if constant else linear.coeff(eps, 1)
        if not expression:
            continue
        matches = []
        for key, form in forms.items():
            factor = s.cancel(expression/form)
            if not factor.has(ax, ay, bx, by, dx, dy):
                matches.append((key, s.expand(factor)))
        assert len(matches) == 1, (quad, expression)
        key, factor = matches[0]
        assert factor in allowed, (quad, factor)
        # Every factor is a difference of B positions, so its sign is fixed
        # on the complete weak-order cell represented by (lv,mv).
        direction = int(s.sign(factor.subs({lam: lv, mu: mv})))
        assert direction
        model.bracket_link(index, key, direction)
        links.append((quad, key, str(factor)))
    assert len(links) == 14 and model.n == 433
    return model, links


def split_formula():
    variables, original, *_ = compiler.base_formula()
    assert original[0] == [1]
    model = Directions(variables, original[1:])
    model.add_trits(('ax', 'ay', 'cx', 'cy', 'dx', 'dy', 'ac', 'ad', 'cd'))
    for prefix in 'acd':
        model.nonzero(prefix)
    pairs = {(0, 1): 1, (0, 2): ('ay', 1), (0, 3): ('cy', 1), (0, 4): ('dy', 1),
             (1, 2): ('ax', -1), (1, 3): ('cx', -1), (1, 4): ('dx', -1),
             (2, 3): ('ac', 1), (2, 4): ('ad', 1), (3, 4): ('cd', 1)}
    model.rank_two_axioms(5, pairs)
    ax, ay, cx, cy, dx, dy, ea, ec, ed, lam = s.symbols('ax ay cx cy dx dy ea ec ed lam')
    points = {0: (0, 0, 0), 1: (ea*ax, ea*ay, 0), 4: (1-ec*cx, -ec*cy, 0),
              5: (1, 0, 0), 2: (0, 0, 1), 3: (0, 1, 1), 6: (0, lam, 1),
              7: (ed*dx, lam+ed*dy, 1)}
    forms = {'ax': ax, 'ay': ay, 'cx': cx, 'cy': cy, 'dx': dx, 'dy': dy,
             'ac': ax*cy-ay*cx, 'ad': ax*dy-ay*dx, 'cd': cx*dy-cy*dx}
    allowed = {s.Integer(1), s.Integer(-1), lam, -lam, lam-1, 1-lam}
    links, constants = [], []
    for index, quad in enumerate(compiler.Q, 1):
        first, *rest = quad
        raw = s.expand(s.Matrix([[points[i][k]-points[first][k] for k in range(3)]
                                 for i in rest]).det())
        constant = raw.subs({ea: 0, ec: 0, ed: 0})
        if constant:
            assert constant in allowed
            model.clauses.append([int(s.sign(constant.subs(lam, s.Rational(1, 2))))*index])
            constants.append((quad, str(constant)))
            continue
        factors = [symbol for edge, symbol in (((0, 1), ea), ((4, 5), ec), ((6, 7), ed))
                   if set(edge) <= set(quad)]
        if not factors:
            continue
        expression = raw
        for symbol in (ea, ec, ed):
            expression = expression.coeff(symbol, 1 if symbol in factors else 0)
        if not expression:
            continue
        matches = []
        for key, form in forms.items():
            factor = s.cancel(expression/form)
            if not factor.has(ax, ay, cx, cy, dx, dy):
                matches.append((key, s.expand(factor)))
        assert len(matches) == 1, (quad, expression)
        key, factor = matches[0]
        assert factor in allowed
        model.bracket_link(index, key, int(s.sign(factor.subs(lam, s.Rational(1, 2)))))
        links.append((quad, key, str(factor)))
    assert len(links) == 40 and len(constants) == 20 and model.n == 427
    return model, links


def certificates():
    cases, links = [], {}
    for case, hierarchy in product(range(5), (-1, 0, 1)):
        model, factored = triple_formula(case, hierarchy)
        name = f'triple_{case}_hierarchy_{hierarchy:+d}'.replace('+', 'p').replace('-', 'm')
        proof = model.clauses
        if case == 0 and hierarchy == 1:
            proof = model.implication({'ax': 0, 'ay': -1, 'bx': -1, 'by': 0}, (0, 1, 4, 5), 1)
        elif case == 2:
            proof = model.implication({'dx': -1, 'dy': 0}, (2, 3, 6, 7), 1)
        elif case in (3, 4) and hierarchy == -1:
            proof = model.implication({'ax': 1, 'ay': 0, 'bx': 0, 'by': 1}, (0, 1, 4, 5), -1)
        assert SAT(model.n, proof).check() == -1, name
        cases.append((name, model.n, proof))
        links[name] = factored
    model, factored = split_formula()
    proof = model.implication({'dx': -1, 'dy': 0}, (2, 3, 6, 7), 1)
    assert SAT(model.n, proof).check() == -1
    cases.append(('split_virtual67', model.n, proof))
    links['split_virtual67'] = factored
    assert len(cases) == 16
    return cases, links


def metric_checks():
    # The existing identities are polynomial at u=0 and u=v, and the
    # relative stress calculation uses neither positive endpoint weight.
    triple.exact_checks()
    # The intrinsic and height coefficient matrices are constant-rank;
    # r=0 in this existing family is the triple cap used in case 2.
    two_single.exact_checks()
    _, _, edges, _, _, kx, ky = load_data()
    x = [s.Integer(0)]+list(s.symbols('x1:8'))
    g = [s.Integer(0)]+list(s.symbols('g1:8'))
    t, u = s.symbols('t u')
    half = s.Rational(1, 2)
    X = lambda i, j: x[j]-x[i]+kx[i, j]
    G = lambda i, j: g[j]-g[i]
    D = lambda i, j: X(i, j)**2+ky[i, j]**2/t+2*ky[i, j]*G(i, j)+t*G(i, j)**2
    stress = [[s.expand(X(a, b)*X(c, d)+t*G(a, b)*G(c, d)
                         -(D(a, d)+D(b, c)-D(a, c)-D(b, d))/2)
               for c, d in zip(B, B[1:]+B[:1])] for a, b in zip(A, A[1:]+A[:1])]

    def check_limit(physical, ha, hb, family_x, family_g, family_zeta=None):
        ea = [physical[A[(i+1) % 4]]-physical[A[i]] for i in range(4)]
        eb = [physical[B[(i+1) % 4]]-physical[B[i]] for i in range(4)]
        residuals = [stress[i][j]-ha[i]*hb[j]+ea[i]*eb[j] for i, j in product(range(4), repeat=2)]
        for cap, weights in ((A, ha), (B, hb)):
            residuals.extend(X(i, j)+weight for (i, j), weight
                             in zip(zip(cap, cap[1:]+cap[:1]), weights))
        matrix, rhs = s.linear_eq_to_matrix(residuals, x[1:]+g[1:])
        assert matrix.shape == (24, 14) and matrix.rank() == 14
        assert all(s.expand(value) == 0 for value in
                   matrix*s.Matrix(list(family_x[1:])+list(family_g[1:]))-rhs)
        if family_zeta is None:
            return
        U = [physical[i]+(family_x[2] if i in B else 0) for i in range(8)]
        H = {0: s.Integer(0), 2: family_g[2], 3: family_g[3]}
        H.update({i: s.Symbol(f'H{i}') for i in two_single.FREE})
        intrinsic = dict(zip(x[1:]+g[1:], list(family_x[1:])+list(family_g[1:])))
        residuals = []
        for i, j in edges:
            ell = int(j in B)-int(i in B)
            if not ell or (i, j) in ((0, 2), (0, 3)):
                continue
            residuals.append(s.expand(((U[j]-U[i])**2-X(i, j)**2
                                         -ell*(H[j]-H[i])-2*ky[i, j]*G(i, j)).subs(intrinsic)))
        matrix, rhs = s.linear_eq_to_matrix(residuals, [H[i] for i in two_single.FREE])
        assert matrix.shape == (14, 5) and matrix.rank() == 5
        assert all(s.expand(value) == 0 for value in
                   matrix*s.Matrix([family_zeta[i] for i in two_single.FREE])-rhs)
        coefficient = half*(family_zeta[6]-family_g[2])+(family_g[3]-family_g[2])*(U[6]-U[2])
        assert s.expand(coefficient+u*(1-2*u)) == 0

    # Reversed dominant A edge, case 0.
    family_x = (0, 0, 0, -u, half, 0, 0, 0)
    family_g = (0, 0, -s.Rational(1, 8), u/2-s.Rational(1, 8), 0,
                s.Rational(1, 4), s.Rational(1, 8), s.Rational(1, 8))
    check_limit((0, 0, 0, -u, 0, half, -half, -half),
                (0, 0, half, half), (u, half-u, 0, half), family_x, family_g)
    beta, gb = -X(1, 4), G(1, 4)
    assert s.expand(gb+beta/2-stress[1][0]) == 0
    relative = beta*(1-2*x[2]+2*x[1])+gb+2*t*(g[2]-g[1])*gb
    assert s.expand(D(1, 4)+D(1, 2)-D(2, 4)-relative) == 0
    rho5 = x[5]+s.Rational(1, 4)+2*x[5]*x[2]+g[5]-2*g[2]+2*t*g[5]*g[2]
    limit = dict(zip(x[1:]+g[1:], family_x[1:]+family_g[1:])) | {t: 0}
    assert s.expand(rho5.subs(limit)-s.Rational(3, 4)) == 0
    assert 2*(s.Rational(1, 2)+2*s.Rational(3, 4)) == 4
    print('PASS reversed dominant-edge height/(t*beta)=4 and cap/(t*alpha*beta)=-8')

    # Split cap A, after the checked canonical marking change.
    family_x = (0, 0, half-u, -u, 0, 0, 0, 0)
    family_g = (0, 0, s.Rational(1, 8)-u/2, s.Rational(3, 8)-u/2,
                s.Rational(1, 4), s.Rational(1, 4), s.Rational(1, 8), s.Rational(1, 8))
    family_zeta = (0, 0, family_g[2], family_g[3], s.Rational(1, 4)-2*u,
                   s.Rational(1, 4)-2*u, 4*u**2-2*u+s.Rational(1, 8),
                   4*u**2-2*u+s.Rational(1, 8))
    check_limit((0, 0, 0, -half, half, half, -u, -u),
                (0, half, 0, half), (half, half-u, 0, u), family_x, family_g, family_zeta)
    print('PASS split-cap metric limits: ranks 14 and 5; same strict B-cap coefficient u*(1-2*u)')


def main():
    if not __debug__:
        raise RuntimeError('run with assertions enabled')
    if len(sys.argv) > 2:
        raise SystemExit(__doc__)
    symmetries = compiler.marked_symmetries()
    variables, clauses, *_ = compiler.base_formula()
    models = compiler.enumerate_models(variables, clauses, symmetries)
    _, zeros = two_line.check(models)
    rows = [row for row in zeros if len(row['zero_a_edges'])+len(row['zero_b_edges']) == 3]
    assert len(rows) == 176
    canonical = canonical_maps(rows, symmetries)
    print('PASS all 176 three-zero two-line orders: five triple families of 32 and one split family of 16', flush=True)
    proofs, links = certificates()
    for name, n, proof in proofs:
        print(f'PASS {name}: UNSAT; {n} variables, {len(proof)} clauses', flush=True)
    metric_checks()
    if len(sys.argv) == 2:
        output = Path(sys.argv[1])
        output.mkdir(parents=True, exist_ok=True)
        for name, n, proof in proofs:
            compiler.write_cnf(output/(name+'.cnf'), n, proof)
        coverage = clauses+[[-(i+1)*value for i, value in enumerate(model)] for model in models]
        compiler.write_cnf(output/'three_zero_model_coverage.cnf', variables, coverage)
        (output/'three_zero_cells.json').write_text(json.dumps({'cells': canonical, 'factored_links': links}, indent=2)+'\n')
    print('Scope: all exactly-three-zero two-line blow-ups; four-zero and other blow-up shapes require separate proofs.')


if __name__ == '__main__':
    main()
