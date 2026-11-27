#!/usr/bin/env python3
"""Finite directional certificates for the canonical one-V cap limit.

Usage: python remaining_one_v.py [OUTPUT_DIRECTORY]

The geometric and metric justification is in remaining_one_collinear.md.
The optional directory receives 25 UNSAT CNFs, including an exhaustive
survivor-pattern check.  Replaying them with the repository's independent
C++ checker verifies the finite Boolean steps.  No edge comparability
between caps, or lower bound on a collapsing edge, is imposed.
"""

from functools import lru_cache
from itertools import combinations, product
import json
from pathlib import Path
import sys

import sympy as s

from direct_metric import load_data
from remaining_one_collinear import write_cnf
from solver_chambers import base_formula, marked_symmetries
from verify_nonparallel_corner import SAT, allowed_sum

QUADS = tuple(combinations(range(8), 4))
QI = {q: i for i, q in enumerate(QUADS, 1)}
SURVIVOR = {'ax': 1, 'ay': 0, 'bx': 0, 'by': 1}


def sign(value):
    return int(bool(value > 0)) - int(bool(value < 0))


@lru_cache(None)
def topology():
    variables, clauses, *_ = base_formula()
    assert clauses[0] == [1]
    # Coordinates are fixed by actual anchors.  Their orientation can
    # be either sign, so remove only the normalization chi0123=+1.
    return variables, tuple(tuple(row) for row in clauses[1:])


class Geometry:
    def __init__(self, chart):
        assert chart in ('independent', 'parallel')
        self.chart = chart
        ax, ay, bx, by, eps = s.symbols('ax ay bx by eps')
        self.ax, self.ay, self.bx, self.by = ax, ay, bx, by
        self.u, self.v, self.lam = s.symbols('u v lambda')
        u, v, lam = self.u, self.v, self.lam
        if chart == 'independent':
            # Anchors 0,2,5,7.  Noncollinearity of the B arms gives u!=0.
            points = {0: (0, 0, 0), 1: (eps*ax, eps*ay, 0),
                      4: (eps*(ax+bx), eps*(ay+by), 0), 5: (1, 0, 0),
                      2: (0, 0, 1), 3: (u, v, 1), 6: (0, 0, 1), 7: (0, 1, 1)}
            self.keys = ('ax', 'ay', 'bx', 'by', 'Ax', 'Ay',
                         'aV', 'aW', 'bV', 'bW', 'AV', 'AW', 'ab')
            forms = {'ax': ax, 'ay': ay, 'bx': bx, 'by': by, 'Ax': ax+bx, 'Ay': ay+by,
                     'aV': ax*v-ay*u, 'aW': ax*(v-1)-ay*u,
                     'bV': bx*v-by*u, 'bW': bx*(v-1)-by*u,
                     'AV': (ax+bx)*v-(ay+by)*u,
                     'AW': (ax+bx)*(v-1)-(ay+by)*u}
            multipliers = (-1, 1)
            constant_forms = (s.Integer(1), u, v, v-1)
        else:
            # Anchors 0,2,5,3.  The other arm is lambda*E, lambda!=0.
            points = {0: (0, 0, 0), 1: (eps*ax, eps*ay, 0),
                      4: (eps*(ax+bx), eps*(ay+by), 0), 5: (1, 0, 0),
                      2: (0, 0, 1), 3: (0, 1, 1), 6: (0, 0, 1), 7: (lam, 0, 1)}
            self.keys = ('ax', 'ay', 'bx', 'by', 'Ax', 'Ay', 'aW', 'bW', 'AW', 'ab')
            forms = {'ax': ax, 'ay': ay, 'bx': bx, 'by': by, 'Ax': ax+bx, 'Ay': ay+by,
                     'aW': -ax-lam*ay, 'bW': -bx-lam*by,
                     'AW': -ax-bx-lam*(ay+by)}
            multipliers = (-1, 1, -lam, lam)
            constant_forms = (s.Integer(1), lam)
        self.constants, self.linear, self.quadratic = [], [], []
        for idx, quad in enumerate(QUADS, 1):
            first, *rest = quad
            polynomial = s.expand(s.Matrix(
                [[points[i][k]-points[first][k] for k in range(3)] for i in rest]).det())
            constant = polynomial.coeff(eps, 0)
            if constant != 0:
                # This check proves that the listed parameter sign cells
                # cover whole intervals.  Their representatives are not
                # numerical samples of an otherwise unconstrained metric.
                assert any(s.expand(constant-direction*form) == 0
                           for direction in (-1, 1) for form in constant_forms)
                self.constants.append((idx, constant))
                continue
            if len(set(quad) & {0, 1, 4}) >= 2:
                linear = s.expand(polynomial.coeff(eps, 1))
                if linear != 0:
                    matches = [(key, factor) for key, form in forms.items() for factor in multipliers
                               if s.expand(linear-factor*form) == 0]
                    assert matches, (quad, linear)
                    key, factor = matches[0]
                    edge = {'a': (0, 1), 'b': (1, 4), 'A': (0, 4)}[key[0]]
                    assert set(edge) <= set(quad)
                    self.linear.append((idx, key, s.sympify(factor), edge))
                    continue
            if set(quad) & {0, 1, 4} == {0, 1, 4} and len(set(quad) & {2, 3, 6, 7}) == 1:
                factor = s.simplify(polynomial.coeff(eps, 2)/(ax*by-ay*bx))
                assert factor in (-1, 1)
                self.quadratic.append((idx, int(factor)))
        assert len(self.linear) == 27 and len(self.quadratic) == 4
        assert len(self.constants) == (23 if chart == 'independent' else 17)

    def model(self, parameter, hierarchy):
        return DirectionalModel(self, parameter, hierarchy)


class DirectionalModel:
    def __init__(self, geometry, parameter, hierarchy):
        assert hierarchy in (-1, 0)
        # -1 means beta/alpha -> 0.  In case 0 both limiting edge
        # directions use their common max(alpha,beta) denominator.
        # The verified mirror reduces second-dominant cases to -1.
        self.n, original = topology()
        self.clauses = [list(row) for row in original]
        self.trits = {}
        for key in geometry.keys:
            self.trits[key] = self.n + 1, self.n + 2
            self.n += 2
            self.clauses.append([-self.n + 1, -self.n])
        for left, right in (('ax', 'ay'), ('bx', 'by')):
            self.clauses.append(list(self.trits[left]) + list(self.trits[right]))
        tails = ('x', 'y', 'V', 'W') if geometry.chart == 'independent' else ('x', 'y', 'W')
        for tail in tails:
            if hierarchy == 0:
                self.clauses.extend(self.sum_clauses('a'+tail, 'b'+tail, 'A'+tail))
            else:
                self.equal('a'+tail, 'A'+tail)

        if geometry.chart == 'independent':
            us, vs = parameter
            assert us in (-1, 1) and vs in (-1, 0, s.Rational(1, 2), 1, 2)
            substitution = {geometry.u: us, geometry.v: vs}
            # W=V-F, hence det(edge,W)+det(edge,F)=det(edge,V).
            for edge in ('a', 'b', 'A'):
                self.clauses.extend(self.sum_clauses(edge+'W', edge+'x', edge+'V'))
            # Six planar vectors E,F,V,W,a,b.  All fixed determinants
            # depend only on sign(u), sign(v), and sign(v-1).
            pairs = {(0, 1): 1, (0, 2): sign(vs), (0, 3): sign(vs-1),
                     (1, 2): -us, (1, 3): -us, (2, 3): -us,
                     (0, 4): ('ay', 1), (1, 4): ('ax', -1),
                     (0, 5): ('by', 1), (1, 5): ('bx', -1),
                     (2, 4): ('aV', -1), (3, 4): ('aW', -1),
                     (2, 5): ('bV', -1), (3, 5): ('bW', -1), (4, 5): ('ab', 1)}
            size = 6
        else:
            assert parameter in (-1, 1)
            substitution = {geometry.lam: parameter}
            # Five vectors E,F,W,a,b, where W=lambda*E-F.
            pairs = {(0, 1): 1, (0, 2): -1, (1, 2): -parameter,
                     (0, 3): ('ay', 1), (1, 3): ('ax', -1),
                     (0, 4): ('by', 1), (1, 4): ('bx', -1),
                     (2, 3): ('aW', -1), (2, 4): ('bW', -1), (3, 4): ('ab', 1)}
            size = 5
        for idx, key, factor, _ in geometry.linear:
            direction = sign(factor.subs(substitution))
            assert direction
            self.bracket_link(idx, key, direction)
        for idx, direction in geometry.quadratic:
            self.bracket_link(idx, 'ab', direction)
        for idx, expression in geometry.constants:
            value = expression.subs(substitution)
            assert not value.free_symbols
            if value:
                self.clauses.append([idx * sign(value)])
        self.rank_two_axioms(size, pairs)

    def deny(self, key, value):
        positive, negative = self.trits[key]
        return [-positive] if value == 1 else [-negative] if value == -1 else [positive, negative]

    def sum_clauses(self, left, right, total):
        return [self.deny(left, a) + self.deny(right, b) + self.deny(total, c)
                for a, b, c in product((-1, 0, 1), repeat=3) if not allowed_sum(a, b, c)]

    def equal(self, left, right):
        self.clauses.extend([[-a, b] for a, b in zip(self.trits[left], self.trits[right])])
        self.clauses.extend([[a, -b] for a, b in zip(self.trits[left], self.trits[right])])

    def bracket_link(self, idx, key, direction):
        positive, negative = self.trits[key]
        self.clauses.extend([[-positive, direction*idx], [-negative, -direction*idx]])

    def rank_two_axioms(self, size, pairs):
        for quad in combinations(range(size), 4):
            entries = [pairs[pair] for pair in combinations(quad, 2)]
            keys = sorted({value[0] for value in entries if isinstance(value, tuple)})
            for values in product((-1, 0, 1), repeat=len(keys)):
                environment = dict(zip(keys, values))
                z = [value[1]*environment[value[0]] if isinstance(value, tuple) else value
                     for value in entries]
                terms = (z[0]*z[5], -z[1]*z[4], z[2]*z[3])
                if any(terms) and (min(terms) >= 0 or max(terms) <= 0):
                    self.clauses.append(sum((self.deny(key, value)
                                             for key, value in environment.items()), []))

    def block_survivor(self):
        self.clauses.append(sum((self.deny(key, value) for key, value in SURVIVOR.items()), []))


def exact_checks():
    symmetries = marked_symmetries()
    mirror = (4, 1, 6, 3, 0, 5, 2, 7)
    assert any(tuple(entry['permutation']) == mirror and entry['phase_preserving']
               for entry in symmetries)
    _, _, _, _, _, kx, ky = load_data()
    x = [s.Integer(0)] + list(s.symbols('x1:8'))
    gamma = [s.Integer(0)] + list(s.symbols('g1:8'))
    t = s.Symbol('t')
    X = lambda i, j: x[j]-x[i]+kx[i, j]
    G = lambda i, j: gamma[j]-gamma[i]
    D = lambda i, j: X(i, j)**2+ky[i, j]**2/t+2*ky[i, j]*G(i, j)+t*G(i, j)**2

    def stress(a, b, c, d):
        return s.expand(X(a, b)*X(c, d)+t*G(a, b)*G(c, d)
                        -(D(a, d)+D(b, c)-D(a, c)-D(b, d))/2)

    alpha = -X(0, 1)
    c0 = -x[2]+s.Rational(1, 4)+2*gamma[2]
    assert s.expand(c0-2*stress(0, 1, 6, 7)-2*stress(0, 1, 7, 2)) == 0
    assert s.expand(stress(0, 1, 3, 6)-alpha/2+G(0, 1)) == 0
    assert s.expand(stress(4, 5, 7, 2)+X(4, 5)/2+G(4, 5)) == 0
    h1 = -c0+(1-2*x[2])*alpha+G(0, 1)+2*t*gamma[2]*G(0, 1)
    h5 = (x[5]+s.Rational(1, 4)+2*x[5]*x[2]+gamma[5]-2*gamma[2]
          +2*t*gamma[5]*gamma[2])
    assert s.expand(D(0, 1)-D(1, 2)+D(0, 2)-h1) == 0
    assert s.expand(D(0, 5)-D(2, 5)+D(0, 2)-h5) == 0
    # The cap-A half-perimeter limit gives h50->1/2 and hence x5->0.
    assert s.expand(-X(5, 0)-x[5]-s.Rational(1, 2)) == 0
    length, dot, x2 = s.symbols('length dot x2')
    g2 = (x2-s.Rational(1, 4))/2
    g5 = s.Rational(1, 4)-length/2-dot
    h1_limit = 2*(-4*length+1-2*x2+s.Rational(1, 2))
    h5_limit = 2*(s.Rational(1, 4)+g5-2*g2)
    axial_limit = s.expand(h1_limit-2*h5_limit)
    assert axial_limit == 4*dot-6*length
    assert s.simplify(-axial_limit/length-(6-4*dot/length)) == 0
    ax, ay, az, bx, by, bz = s.symbols('ax ay az bx by bz')
    bracket = s.Matrix([[ax, ay, az], [ax+bx, ay+by, az+bz], [1, 0, 0]]).det()
    assert s.expand(bracket-ay*bz+az*by) == 0
    print('PASS exact mirror, polarization, axial cancellation, and [0145] identities', flush=True)


def main():
    if not __debug__:
        raise RuntimeError('run with assertions enabled')
    if len(sys.argv) > 2:
        raise SystemExit(__doc__)
    output = Path(sys.argv[1]) if len(sys.argv) == 2 else None
    if output:
        output.mkdir(parents=True, exist_ok=True)
    exact_checks()
    independent = Geometry('independent')
    parallel = Geometry('parallel')
    certificates = []
    vertical_cells = (('negative', -1), ('zero', 0), ('middle', s.Rational(1, 2)),
                      ('one', 1), ('greater', 2))
    for us, (label, vs), hierarchy in product((-1, 1), vertical_cells, (-1, 0)):
        name = f'independent_u{us:+d}_v{label}_h{hierarchy:+d}'.replace('+', 'p').replace('-', 'm')
        model = independent.model((us, vs), hierarchy)
        if (us, vs, hierarchy) == (-1, 0, -1):
            assert SAT(model.n, model.clauses).check() == 1
            blocked = independent.model((us, vs), hierarchy)
            blocked.block_survivor()
            certificates.append((name+'_pattern', blocked))
            # Analytic Section 5 proves this actual bracket strictly
            # positive in every survivor, uniformly in beta/alpha.
            model.clauses.append([QI[(0, 1, 4, 5)]])
            name += '_metric'
        certificates.append((name, model))
    for ls, hierarchy in product((-1, 1), (-1, 0)):
        name = f'parallel_l{ls:+d}_h{hierarchy:+d}'.replace('+', 'p').replace('-', 'm')
        certificates.append((name, parallel.model(ls, hierarchy)))
    assert len(certificates) == 25
    records = []
    for name, model in certificates:
        assert SAT(model.n, model.clauses).check() == -1, name
        print(f'PASS {name}: UNSAT; {model.n} variables, {len(model.clauses)} clauses', flush=True)
        records.append({'name': name, 'variables': model.n, 'clauses': len(model.clauses)})
        if output:
            write_cnf(output/(name+'.cnf'), model.n, model.clauses)
    if output:
        (output/'one_v_certificates.json').write_text(json.dumps(records, indent=2)+'\n')
    print('Scope: the canonical one-V limit at every collapse rate; combine with remaining_one_collinear.py.')


if __name__ == '__main__':
    main()
