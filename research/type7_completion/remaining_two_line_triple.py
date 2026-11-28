#!/usr/bin/env python3
"""Exclude two-line blow-ups with a triple cluster and four positive partner weights.

Usage: python remaining_two_line_triple.py [OUTPUT_DIRECTORY]

The exact order cover contains 288 such cells.  Twenty-eight necessary
sign certificates and one relative-height calculation exclude all of
them, including every relative rate of the two collapsing A edges.
"""

from collections import Counter
from itertools import combinations, product
import json
from pathlib import Path
import sys

import sympy as s

import common_line_edge_collapse as two_line
import exhaustive_collinear_caps as collinear
from direct_metric import load_data
from remaining_flat_blowup import rank_tuple
import remaining_two_line_blowup as one_zero
import solver_chambers as chambers
from verify_nonparallel_corner import SAT, allowed_sum

A, B = collinear.A, collinear.B
KEYS = ((0,), (1,), (2,), (3,), (0, 2), (1, 3), 'ab')
TRITS = {key: (410+2*i, 411+2*i) for i, key in enumerate(KEYS)}
ORDERS = (
    (0, 1, 0, 1), (1, 0, 1, 0), (0, 1, 0, 2), (0, 2, 0, 1),
    (1, 0, 1, 2), (1, 0, 2, 0), (1, 2, 1, 0), (2, 0, 2, 1),
    (2, 1, 2, 0), (1, 2, 3, 0), (1, 3, 2, 0), (2, 0, 3, 1), (2, 1, 3, 0),
)


def canonical_maps(rows, symmetries):
    phase = [entry['permutation'] for entry in symmetries if entry['phase_preserving']]
    seen = set()
    for row in rows:
        values = dict(zip(A, row['a'])) | dict(zip(B, row['b']))
        maps = []
        for permutation, reflection in product(phase, (-1, 1)):
            a = rank_tuple([reflection*values[permutation[i]] for i in A])
            b = rank_tuple([reflection*values[permutation[i]] for i in B])
            if a == (0, 0, 0, 1):
                maps.append((b, permutation, reflection))
        assert maps, row
        b, permutation, reflection = min(maps)
        assert b in ORDERS
        seen.add(b)
        row['canonical_map'] = {'b_order': b, 'permutation': permutation,
                                'horizontal_reflection': reflection}
    assert seen == set(ORDERS)


def direction_formula(lambda_value, mu_value, hierarchy):
    """Necessary virtual-edge formula; -1/0/+1 means a dominates/comparable/b dominates."""
    n, clauses, *_ = chambers.base_formula()
    assert clauses[0] == [1]
    clauses = [list(row) for row in clauses[1:]]  # the four anchors fix the frame orientation
    keys = [(0,), (1,), (2,), (3,), (0, 2), (1, 3), 'ab']
    trits = {key: (n+2*i+1, n+2*i+2) for i, key in enumerate(keys)}
    n += 14
    clauses += [[-p, -m] for p, m in trits.values()]
    for i, j in ((0, 1), (2, 3)):
        clauses.append(list(trits[(i,)]) + list(trits[(j,)]))

    def deny(key, value):
        p, m = trits[key]
        return [-p] if value == 1 else [-m] if value == -1 else [p, m]

    for xa, ya, xb, yb, ab in product((-1, 0, 1), repeat=5):
        terms = [ab, -xa*yb, ya*xb]
        if any(terms) and (all(v >= 0 for v in terms) or all(v <= 0 for v in terms)):
            clauses.append(deny((0,), xa) + deny((1,), ya) + deny((2,), xb)
                           + deny((3,), yb) + deny('ab', ab))
    for i, j in ((0, 2), (1, 3)):
        if hierarchy == 0:
            clauses += [deny((i,), a) + deny((j,), b) + deny((i, j), c)
                        for a, b, c in product((-1, 0, 1), repeat=3) if not allowed_sum(a, b, c)]
        else:
            left = trits[(i if hierarchy == -1 else j,)]
            right = trits[(i, j)]
            clauses += [[-x, y] for x, y in zip(left, right)]
            clauses += [[x, -y] for x, y in zip(left, right)]

    ax, ay, bx, by = xs = s.symbols('ax ay bx by')
    eps, lam, mu = s.symbols('eps lam mu')
    symbolic_points = {
        0: (0, 0, 0), 1: (eps*ax, eps*ay, 0),
        4: (eps*(ax+bx), eps*(ay+by), 0), 5: (1, 0, 0),
        2: (0, 0, 1), 3: (0, lam, 1), 6: (0, mu, 1), 7: (0, 1, 1),
    }
    points = {i: s.Matrix(p).subs({lam: lambda_value, mu: mu_value}) for i, p in symbolic_points.items()}
    base = {i: p.subs(eps, 0) for i, p in points.items()}
    counts = Counter()
    possible_coefficients = {s.expand(x-y) for x, y in product((0, lam, mu, 1), repeat=2) if x != y}
    for idx, quad in enumerate(combinations(range(8), 4), 1):
        a, *rest = quad
        rank = s.Matrix.hstack(*(base[v]-base[a] for v in rest)).rank()
        raw = s.expand(s.Matrix([[symbolic_points[v][k]-symbolic_points[a][k]
                                 for k in range(3)] for v in rest]).det())
        determinant = raw.subs({lam: lambda_value, mu: mu_value})
        if rank == 3:
            symbolic = s.expand(raw.coeff(eps, 0))
            assert symbolic in possible_coefficients
            leading = symbolic.subs({lam: lambda_value, mu: mu_value})
            assert leading != 0
            clauses.append([idx if leading > 0 else -idx])
            counts['constant'] += 1
        elif rank == 2 and len(set(quad) & {0, 1, 4}) >= 2:
            symbolic = s.expand(raw.coeff(eps, 1))
            # Every coefficient is a signed difference of two B positions.
            # Its sign is fixed throughout the entire weak-order cell.
            for _, coefficient in s.Poly(symbolic, *xs).terms():
                assert coefficient in possible_coefficients
            leading = s.expand(symbolic.subs({lam: lambda_value, mu: mu_value}))
            coefficients, indices = [], []
            for powers, coefficient in s.Poly(leading, *xs).terms():
                assert sum(powers) == 1
                indices.append(powers.index(1))
                coefficients.append(coefficient)
            assert len(set(coefficients)) == 1 and coefficients[0] != 0
            key = tuple(sorted(indices))
            p, m = trits[key]
            direction = 1 if coefficients[0] > 0 else -1
            clauses += [[-p, direction*idx], [-m, -direction*idx]]
            counts['linear'] += 1
        elif set(quad) & {0, 1, 4} == {0, 1, 4} and len(set(quad) & set(B)) == 1:
            leading = determinant.coeff(eps, 2)
            ratio = s.cancel(leading/(ax*by-ay*bx))
            assert ratio in (-1, 1)
            p, m = trits['ab']
            clauses += [[-p, int(ratio)*idx], [-m, -int(ratio)*idx]]
            counts['quadratic'] += 1
    return n, clauses, counts


def necessary_cases():
    shapes = sorted({(s.Rational(b[1]-b[0], b[3]-b[0]),
                      s.Rational(b[2]-b[0], b[3]-b[0])) for b in ORDERS})
    assert len(shapes) == 9
    cases = []
    for case_id, (lam, mu) in enumerate(shapes):
        for hierarchy in (-1, 0, 1):
            n, clauses, counts = direction_formula(lam, mu, hierarchy)
            assert n == 423
            name = f'order_{case_id}_hierarchy_{hierarchy:+d}'.replace('+', 'p').replace('-', 'm')
            if (lam, mu, hierarchy) != (-1, -2, -1):
                cases.append((name, n, clauses))
                continue
            # The surviving cell is mu < lam < 0, with a dominant.
            # Its only virtual directions are a=+E, b=+F.
            block = []
            for i, value in enumerate((1, 0, 0, 1)):
                positive, negative = TRITS[(i,)]
                block += [-positive] if value == 1 else [positive, negative]
            cases.append((name+'_direction_blocked', n, clauses+[block]))
            cases.append((name+'_positive_cap', n,
                          clauses+[[abs(chambers.lit((0, 1, 4, 5)))]]))
    assert len(cases) == 28
    return cases


def exact_checks():
    # The rank-14 and rank-5 necessity identities are polynomial in r.
    # Their coefficient matrices are constant, so r=0 is included.
    one_zero.exact_checks()
    _, _, edges, _, _, kx, ky = load_data()
    x = [s.Integer(0)]+list(s.symbols('x1:8'))
    g = [s.Integer(0)]+list(s.symbols('g1:8'))
    t, u, v = s.symbols('t u v')
    X = lambda i, j: x[j]-x[i]+kx[i, j]
    G = lambda i, j: g[j]-g[i]
    D = lambda i, j: X(i, j)**2+ky[i, j]**2/t+2*ky[i, j]*G(i, j)+t*G(i, j)**2
    alpha = -X(0, 1)
    ae, be = [tuple(zip(cap, cap[1:]+cap[:1])) for cap in (A, B)]
    stress = [[s.expand(X(a, b)*X(c, d)+t*G(a, b)*G(c, d)
                         -(D(a, d)+D(b, c)-D(a, c)-D(b, d))/2)
               for c, d in be] for a, b in ae]
    c0 = -x[2]+s.Rational(1, 4)+2*g[2]
    assert s.expand(c0-2*(stress[0][2]+stress[0][3])) == 0
    assert s.expand(G(0, 1)-alpha/2+stress[0][1]) == 0
    rho1 = -c0+(1-2*x[2])*alpha+G(0, 1)+2*t*g[2]*G(0, 1)
    rho5 = x[5]+s.Rational(1, 4)+2*x[5]*x[2]+g[5]-2*g[2]+2*t*g[5]*g[2]
    assert s.expand(D(0, 1)-D(1, 2)+D(0, 2)-rho1) == 0
    assert s.expand(D(0, 5)-D(2, 5)+D(0, 2)-rho5) == 0
    xlim = (0, 0, v, v-u, s.Rational(1, 2), 0, s.Rational(1, 2), 0)
    glim = (0, 0, v/2-s.Rational(1, 8), (v-u)/2-s.Rational(1, 8),
            0, s.Rational(1, 4), -s.Rational(1, 8), s.Rational(1, 8))
    limit = dict(zip(x[1:]+g[1:], xlim[1:]+glim[1:])) | {t: 0}
    assert s.expand(rho5.subs(limit)-(s.Rational(3, 4)-v)) == 0
    ha = (0, 0, s.Rational(1, 2), s.Rational(1, 2))
    hb = (u, v-u, s.Rational(1, 2), s.Rational(1, 2)-v)
    ea = (0, 0, s.Rational(1, 2), -s.Rational(1, 2))
    eb = (u, v-u, -s.Rational(1, 2), s.Rational(1, 2)-v)
    assert all(s.expand(stress[i][j].subs(limit)-ha[i]*hb[j]+ea[i]*eb[j]) == 0
               for i, j in product(range(4), repeat=2))
    # The surviving direction a/alpha is the positive physical unit.
    limits = [s.expand(hb[j]-eb[j]) for j in range(4)]
    assert limits == [0, 0, 1, 0]
    relative_c0, relative_g1 = 2*(limits[2]+limits[3]), s.Rational(1, 2)-limits[1]
    relative_rho1 = s.expand(-relative_c0+(1-2*v)+relative_g1)
    assert relative_rho1 == -s.Rational(1, 2)-2*v
    assert s.expand(2*(relative_rho1-2*(s.Rational(3, 4)-v))) == -4
    print('PASS relative stress limits, rho1/alpha=-1/2-2v, rho5=3/4-v; moving height/(t*alpha)=-4')


def main():
    if not __debug__:
        raise RuntimeError('run with assertions enabled')
    if len(sys.argv) > 2:
        raise SystemExit(__doc__)
    output = Path(sys.argv[1]) if len(sys.argv) == 2 else None
    if output:
        output.mkdir(parents=True, exist_ok=True)
    symmetries = chambers.marked_symmetries()
    variables, clauses, *_ = chambers.base_formula()
    models = chambers.enumerate_models(variables, clauses, symmetries)
    _, zeros = two_line.check(models)
    triples = []
    for row in zeros:
        sizes = len(row['zero_a_edges']), len(row['zero_b_edges'])
        if sorted(sizes) != [0, 2]:
            continue
        clustered = row['a'] if sizes[0] == 2 else row['b']
        if sorted(Counter(clustered).values()) == [1, 3]:
            triples.append(row)
    assert len(triples) == 288
    canonical_maps(triples, symmetries)
    print('PASS all 288 triple-cluster/positive-partner orders: 13 marked forms, 9 normalized B orders', flush=True)
    exact_checks()
    for name, n, necessary in necessary_cases():
        assert SAT(n, necessary).check() == -1, name
        print(f'PASS {name}: UNSAT; {n} variables, {len(necessary)} clauses', flush=True)
        if output:
            chambers.write_cnf(output/(name+'.cnf'), n, necessary)
    if output:
        blocked = clauses+[[-(i+1)*value for i, value in enumerate(model)] for model in models]
        chambers.write_cnf(output/'two_line_triple_model_coverage.cnf', variables, blocked)
        (output/'two_line_triple_cells.json').write_text(json.dumps(triples, indent=2)+'\n')
    print('Scope: two-line limits with a triple cluster and four positive partner weights; other two-zero patterns remain.')


if __name__ == '__main__':
    main()
