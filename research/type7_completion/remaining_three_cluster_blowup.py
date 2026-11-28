#!/usr/bin/env python3
"""Exact exclusion of the 304 mixed triple-cluster three-zero cells.

Usage: python remaining_three_cluster_blowup.py [OUTPUT_DIRECTORY]

Two A weights and one B weight vanish. A third independently normalized
edge direction treats every coincident B pair. Six endpoint metric
arguments complete the cover; see remaining_three_cluster_blowup.md.
"""

import sys, json
from remaining_cluster_blowup import Geometry, Model, cover, product, combinations, s, lit
from verify_linking import SAT

class ThirdGeometry:

    def __init__(self, j):
        k = (j + 1) % 4
        self.edge = (cover.B[j], cover.B[k])
        ax, ay, bx, by, cx, cy, eps, eta = s.symbols('ax ay bx by cx cy eps eta')
        X = s.symbols('X0:4')
        Y = s.symbols('Y0:4')
        P = {0: (0, 0, 0), 1: (eps * ax, eps * ay, 0), 4: (eps * (ax + bx), eps * (ay + by), 0), 5: (1, 0, 0)} | {v: (X[i], Y[i], 1) for i, v in enumerate(cover.B)}
        P[cover.B[k]] = (X[j] + eta * cx, Y[j] + eta * cy, 1)
        sub = {X[k]: X[j], Y[k]: Y[j]}
        forms = {'cy': cy} | {'c' + str(i) + str(l): (cx * (Y[l] - Y[i]) - cy * (X[l] - X[i])).subs(sub) for i, l in cover.PAIRS}
        bilinear = {'ac': ax * cy - ay * cx, 'bc': bx * cy - by * cx, 'Ac': (ax + bx) * cy - (ay + by) * cx}
        self.lin = []
        self.bilin = []
        for q in combinations(range(8), 4):
            if not set(self.edge) <= set(q):
                continue
            f, *rest = q
            D = s.expand(s.Matrix([[P[i][l] - P[f][l] for l in range(3)] for i in rest]).det())
            assert D.coeff(eta, 0) == 0
            v = D.coeff(eta, 1).coeff(eps, 0)
            if v:
                matches = [(name, di) for name, form in forms.items() for di in (-1, 1) if s.expand(v - di * form) == 0]
                assert matches, (q, v)
                self.lin.append((lit(q), *matches[0]))
                continue
            v = D.coeff(eta, 1).coeff(eps, 1)
            if v:
                matches = [(name, di) for name, form in bilinear.items() for di in (-1, 1) if s.expand(v - di * form) == 0]
                assert matches, (q, v)
                self.bilin.append((lit(q), *matches[0]))
        assert (len(self.lin), len(self.bilin)) == (11, 3)

class ThirdModel(Model):

    def __init__(self, G, row, h, T):
        super().__init__(G, row, h)
        for key in ['cx', 'cy', 'ac', 'bc', 'Ac'] + ['c' + str(i) + str(j) for i, j in cover.PAIRS]:
            self.trits[key] = (self.n + 1, self.n + 2)
            self.n += 2
            self.clauses.append([-self.n + 1, -self.n])
        self.clauses.append(list(self.trits['cx']) + list(self.trits['cy']))
        if h == 0:
            self.clauses.extend(self.sum_clauses('ac', 'bc', 'Ac'))
        else:
            self.equal('ac' if h < 0 else 'bc', 'Ac')
        for idx, key, di in T.lin + T.bilin:
            self.bracket_link(idx, key, di)
        self.rank9(row)

    def rank9(self, row):
        entries = {}
        two = {(0, 1): 1, (0, 2): ('ay', 1), (0, 3): ('by', 1), (0, 4): ('cy', 1), (1, 2): ('ax', -1), (1, 3): ('bx', -1), (1, 4): ('cx', -1), (2, 3): ('ab', 1), (2, 4): ('ac', 1), (3, 4): ('bc', 1)}
        for q in combinations(range(9), 3):
            inf = [i for i in q if i < 5]
            bi = [i - 5 for i in q if i >= 5]
            if len(inf) == 3:
                v = 0
            elif len(inf) == 2:
                v = two[tuple(inf)]
            elif len(inf) == 1:
                i, j = bi
                if inf[0] == 0:
                    v = -cover.pair_sign(row['y'], i, j)
                elif inf[0] == 1:
                    v = cover.pair_sign(row['x'], i, j)
                else:
                    v = (('a', 'b', 'c')[inf[0] - 2] + str(i) + str(j), -1)
            else:
                v = row['beta'][cover.TRIPLES.index(tuple(bi))]
            entries[q] = v

        def entry(q):
            di = (-1) ** sum((q[i] > q[j] for i, j in combinations(range(3), 2)))
            v = entries[tuple(sorted(q))]
            return (v[0], di * v[1]) if isinstance(v, tuple) else di * v
        clauses = set()
        for common in range(9):
            for a, b, c, d in combinations([i for i in range(9) if i != common], 4):
                terms = [(1, entry((common, a, b)), entry((common, c, d))), (-1, entry((common, a, c)), entry((common, b, d))), (1, entry((common, a, d)), entry((common, b, c)))]
                terms = [v for v in terms if v[1] != 0 and v[2] != 0]
                keys = sorted({v[0] for q in terms for v in q[1:] if isinstance(v, tuple)})
                for vals in product((-1, 0, 1), repeat=len(keys)):
                    env = dict(zip(keys, vals))

                    def ev(v):
                        return v[1] * env[v[0]] if isinstance(v, tuple) else v
                    termsigns = [di * ev(v) * ev(w) for di, v, w in terms]
                    if any(termsigns) and (min(termsigns) >= 0 or max(termsigns) <= 0):
                        clauses.add(tuple(sum((self.deny(k, v) for k, v in env.items()), [])))
        self.clauses.extend(map(list, sorted(clauses)))


from collections import Counter
from pathlib import Path
import remaining_cluster_blowup as cluster
from solver_chambers import base_formula, enumerate_models, marked_symmetries

A, B, FREE = cover.A, cover.B, cluster.FREE


def normalized_endpoint(row, hierarchy):
    mirrored = tuple(row['y']) == (1, 1, 0, 0)
    if mirrored:
        row, hierarchy = cluster.transform(row, cluster.MIRROR), -hierarchy
    assert tuple(row['y']) == (0, 1, 1, 0) and hierarchy in (-1, 0), (row, hierarchy)
    patterns = {
        ((1, 2, 2, 0), (0, 1, 1, 0)): 'flat_z_half',
        ((2, 1, 1, 0), (0, 1, 1, 0)): 'exceptional_z_a',
        ((0, 2, 1, 0), (1, 0, 0, 1)): 'flat_u_zero',
        ((1, 2, 0, 0), (1, 1, 1, 1)): 'flat_z_zero',
        ((2, 1, 0, 0), (1, 1, 1, 1)): 'exceptional_z_zero',
        ((2, 2, 1, 0), (1, 1, 1, 1)): 'flat_u_half',
    }
    return patterns[tuple(row['x']), tuple(row['beta'])], row, hierarchy, mirrored


def zero_edge(row):
    indices = [i for i in range(4) if row['x'][i] == row['x'][(i+1) % 4]]
    assert len(indices) == 1
    index = indices[0]
    return index, row['y'][index] == row['y'][(index+1) % 4]


def endpoint_implication(geometry, row, hierarchy, third_geometries):
    edge, coincident = zero_edge(row)
    model = (ThirdModel(geometry, row, hierarchy, third_geometries[edge])
             if coincident else Model(geometry, row, hierarchy))
    inverse = {vertex: i for i, vertex in enumerate(cluster.RELABEL)}
    required_literals = [cover.sign(value)*lit(tuple(inverse[i] for i in cluster.QUADS[abs(value)-1]))
                         for value in cluster.flat.REQUIRED]
    required = {'ax': -1, 'bx': 1, 'by': 0}
    if coincident:
        assert edge in (1, 3)
        required |= {'cx': -1 if edge == 1 else 1, 'cy': 0}
    if hierarchy == 0:
        required['a13'] = 1
    violation = [-value for value in required_literals]+[model.trits['ay'][0]]
    violation += sum((model.deny(key, value) for key, value in required.items()), [])
    model.clauses.append(violation)
    assert cluster.proves_unsat(model.n, model.clauses), (row, hierarchy)
    return model.n, model.clauses


def symbolic_metric():
    t, x, g, U, H, Z, variables, edges, equations, kx, ky = cluster.metric_system()
    r, u, a, z, m = s.symbols('r u a z m')
    half = s.Rational(1, 2)
    mu1, mu5 = U[1]-x[1], x[5]+half+U[5]
    length72 = x[7]-x[2]+half
    mu72 = length72+U[7]-U[2]
    length36 = -(x[6]-x[3]+kx[3, 6])
    mu36 = length36+U[6]-U[3]
    length67 = -(x[7]-x[6]+kx[6, 7])
    mu67 = length67-U[7]+U[6]
    equation_map = dict(zip(edges, equations))
    D7, S7 = H[7]-g[7], H[7]+g[7]-2*g[2]
    D6, S6 = H[6]-g[6], H[6]+g[6]-2*g[3]
    C6 = s.Rational(1, 4)-x[6]-2*g[6]
    assert s.expand(equation_map[0, 7]-equation_map[2, 7]
                    -2*x[2]*(mu72-2*length72)+(1-2*t*g[2])*D7) == 0
    assert s.expand(equation_map[0, 6]-equation_map[3, 6]
                    -2*x[3]*mu36-C6+(1-2*t*g[3])*D6) == 0
    assert s.expand(equation_map[2, 7]-Z[7]**2-t*D7*S7+mu72*(2*length72-mu72)) == 0
    assert s.expand(equation_map[3, 6]-Z[6]**2-t*D6*S6+mu36*(2*length36-mu36)) == 0
    D67, S67 = H[7]-H[6]-g[7]+g[6], H[7]-H[6]+g[7]-g[6]
    assert s.expand(equation_map[6, 7]-(Z[7]-Z[6])**2-t*D67*S67
                    +mu67*(2*length67-mu67)) == 0

    flat_P = (0, r, 0, u, half, r, half, z)
    flat_x = (0, -r, 0, -u, 0, r-half, 0, z-half)
    g2, slope = r-s.Rational(1, 8), half-2*r
    flat_g = (0, r/2, g2, g2+slope*u, r-s.Rational(1, 4), r/2,
              g2+slope/2, g2+slope*z)
    exc_P = (0, 0, 0, half, half, 0, a, z)
    exc_x = (0, 0, 0, -half, 0, -half, a-half, z-half)
    exc_g = (0, 0, -s.Rational(1, 8), s.Rational(1, 8), -s.Rational(1, 4), 0,
             a/2-s.Rational(1, 8), z/2-s.Rational(1, 8))
    flat_parameters = {x[1]: -r, x[3]: x[2]-u, x[7]: x[2]+z-half}
    exc_parameters = {x[1]: -r, x[6]: x[2]+a-half, x[7]: x[2]+z-half}
    cases = (
        ('flat_z_zero', False, {r: 0, z: 0}, (2, 7), mu72,
         2048*(2*u-1), (u, 0, -half), 0),
        ('flat_z_half', False, {r: 0, z: half}, (6, 7), mu67,
         2048*(2*u-1), (u, -half, 0), -half),
        ('flat_u_half', False, {r: 0, u: half}, (3, 6), mu36,
         4096*z*(2*z-1), (half, -z, 0), -1/(4*z)),
        ('flat_u_zero', False, {r: 0, u: 0}, None, None,
         -4096*z*(2*z-1), (0, -z), -1/(4*z)),
        ('exceptional_z_zero', True, {r: 0, z: 0}, (2, 7), mu72,
         -4096*a*(2*a-1), (1-a, a-half, -half), 0),
        ('exceptional_z_a', True, {r: 0, z: a}, (6, 7), mu67,
         -4096*a*(2*a-1), (1-a, -half, 0), -1/(4*a)),
    )
    output = {}
    for name, exceptional, endpoint, third, extra_defect, expected_det, expected_coefficients, expected_cubic in cases:
        P, fx, fg = (exc_P, exc_x, exc_g) if exceptional else (flat_P, flat_x, flat_g)
        parameters = exc_parameters if exceptional else flat_parameters
        free = (x[1], x[6], x[7]) if exceptional else (x[1], x[3], x[7])
        family = ({x[i]: fx[i] for i in range(1, 8)} | {g[i]: fg[i] for i in range(1, 8)}
                  | {U[i]: -P[i] for i in FREE} | {H[i]: fg[i] for i in FREE}
                  | {Z[i]: 0 for i in FREE})
        assert all(s.expand(equation.subs(family)) == 0 for equation in equations)
        dependent = [value for value in variables if value not in free]
        indices = [edges.index((0, 1)), edges.index((0, 5))]
        defects = [mu1, mu5]
        if third:
            indices.append(edges.index(third))
            defects.append(extra_defect)
        modified = list(equations)
        for index, defect in zip(indices, defects):
            modified[index] = defect
        modified = [equation.subs(parameters) for equation in modified]
        jacobian = s.Matrix(modified).jacobian(dependent).subs(family).subs(endpoint | {t: 0})
        determinant = s.factor(jacobian.det(method='domain-ge'))
        assert s.simplify(determinant-expected_det) == 0
        inverse = jacobian.inv(method='DM')
        coefficients, beta_coefficients = [], []
        for index, expected in zip(indices, expected_coefficients):
            forcing = s.zeros(21, 1)
            forcing[index] = 1
            jet = inverse*forcing
            coefficient = s.factor(jet[dependent.index(U[1])]-jet[dependent.index(U[5])])
            assert s.simplify(coefficient-expected) == 0
            coefficients.append(str(coefficient))
            beta_coefficients.append(s.factor(jet[dependent.index(x[5])]))
        for position, (coefficient, expected) in enumerate(zip(beta_coefficients, expected_coefficients)):
            offset = -1 if position == 0 else 1 if position == 1 else 0
            assert s.simplify(coefficient-expected-offset) == 0
        normal = s.Matrix([0 if index in indices else (Z[j]-Z[i])**2
                           for index, (i, j) in enumerate(edges)]).subs(
                               {Z[i]: int(i in (6, 7)) for i in FREE})
        quadratic = inverse*(-normal)
        cubic = s.factor(quadratic[dependent.index(U[1])]-quadratic[dependent.index(U[5])])
        assert s.simplify(cubic-expected_cubic) == 0
        assert s.simplify(quadratic[dependent.index(x[5])]-expected_cubic) == 0
        data = {'determinant': str(determinant), 'defect_coefficients': coefficients,
                'cubic': str(cubic), 'beta_defect_coefficients': list(map(str, beta_coefficients))}
        if exceptional:
            forcing = -s.Matrix(modified).diff(r).subs(family).subs(endpoint | {t: 0})
            jet = inverse*forcing
            beta_r = s.factor(jet[dependent.index(x[5])])
            farkas_r = s.factor(jet[dependent.index(U[1])]-jet[dependent.index(U[5])])
            beta_normal = s.factor(quadratic[dependent.index(x[5])])
            assert beta_r == 2*a and farkas_r == 2*a-1
            assert s.simplify(beta_normal-expected_cubic) == 0
            data |= {'beta_r': str(beta_r), 'farkas_r': str(farkas_r), 'beta_normal': str(beta_normal)}
        output[name] = data
        print(f'PASS {name}: determinant {determinant}; defects {coefficients}; cubic {cubic}', flush=True)

    # An exact reference with arbitrary mu36=m removes uncontrolled
    # higher powers of that defect at the u=1/2 boundary.
    aa, beta = (1-m)/2, r*(1-m)
    expanded_P = (0, r, 0, u, half, beta, aa, z)
    expanded_x = (0, -r, 0, -u, 0, beta-half, aa-half, z-half)
    expanded_g = (0, 2*aa*r-r/2, 2*aa*r-s.Rational(1, 8),
                  -4*aa*r*u+2*aa*r+u/2-s.Rational(1, 8),
                  2*aa*r-s.Rational(1, 4), aa*r, aa/2-s.Rational(1, 8),
                  2*aa*r-2*r*z+z/2-s.Rational(1, 8))
    expanded = ({x[i]: expanded_x[i] for i in range(1, 8)}
                | {g[i]: expanded_g[i] for i in range(1, 8)}
                | {U[i]: -expanded_P[i] for i in FREE}
                | {H[i]: expanded_g[i] for i in FREE})
    zero_normals = {Z[i]: 0 for i in FREE}
    assert s.expand(mu36.subs(expanded)-m) == 0
    assert s.expand(mu1.subs(expanded)) == 0 and s.expand(mu5.subs(expanded)) == 0
    for equation, edge in zip(equations, edges):
        expected = m*(2*u-1) if edge == (3, 6) else 0
        assert s.expand(equation.subs(expanded).subs(zero_normals)-expected) == 0
    levels = {i: int(i in B) for i in range(8)}
    points = {i: (-U[i], Z[i], levels[i]-2*t*H[i]) for i in range(8)}
    forms = []
    for literal in cluster.flat.REQUIRED:
        first, *rest = cluster.QUADS[abs(literal)-1]
        forms.append(cover.sign(literal)*s.Matrix(
            [[points[i][k]-points[first][k] for k in range(3)] for i in rest]).det())
    numerator, denominator = 4+t*(4*r-1)**2, 4+t*(32*r*u-8*r-8*u+1)
    functional = s.expand(sum(weight*form for weight, form in zip(
        ((1-2*u)*numerator, 2*u*numerator, numerator, denominator), forms)).subs(expanded))
    old = -4*r*(half-r)*u*t*numerator*Z[6]
    extra = s.cancel((functional-old)/m)
    assert s.expand(extra.subs(t, 0)-2*(-Z[1]+2*r*Z[4]+Z[5]-2*r*Z[6])) == 0
    for vertex in (4, 6, 7):
        assert s.expand(extra).coeff(Z[vertex]).subs(r, 0) == 0
    assert s.simplify(s.expand(extra).coeff(Z[1]).subs(r, 0)+(t+4)**2/8) == 0
    assert s.simplify(s.expand(extra).coeff(Z[5]).subs(r, 0)+(t+4)*(8*t*u-t-4)/8) == 0
    output['expanded_mu36_reference'] = {
        'P': list(map(str, expanded_P)), 'x': list(map(str, expanded_x)),
        'gamma_equals_zeta': list(map(str, expanded_g)),
        'Farkas_extra_numerator': str(s.factor(extra)),
    }
    print('PASS exact relative defect identities and all-parameter mu36 reference', flush=True)
    return output


def main():
    if not __debug__:
        raise RuntimeError('run with assertions enabled')
    if len(sys.argv) > 2:
        raise SystemExit(__doc__)
    output = Path(sys.argv[1]) if len(sys.argv) == 2 else None
    if output:
        output.mkdir(parents=True, exist_ok=True)
    symmetries = marked_symmetries()
    variables, clauses, *_ = base_formula()
    models = enumerate_models(variables, clauses, symmetries)
    all_cells, _ = cluster.flat.degenerate_cover(models)
    rows = [row for row in all_cells
            if sum(row['a'][i] == row['a'][(i+1) % 4] for i in range(4)) == 2
            and sum(row['x'][i] == row['x'][(i+1) % 4] for i in range(4)) == 1]
    canonical = [row for row in rows if tuple(row['a']) == (0, 0, 0, 1)]
    assert (len(rows), len(canonical)) == (304, 38)
    cluster.canonical_maps(rows, canonical, symmetries)
    geometry = Geometry()
    third_geometries = {index: ThirdGeometry(index) for index in range(4)}
    records, implications, counts = [], {}, Counter()
    for index, row in enumerate(canonical):
        for hierarchy in (-1, 0, 1):
            model = Model(geometry, row, hierarchy)
            record = {'cell': index, 'hierarchy': hierarchy}
            if cluster.proves_unsat(model.n, model.clauses):
                counts['direct_unsat'] += 1
                record['kind'] = 'direct_unsat'
                if output:
                    cover.write_cnf(output/f'three_cluster_cell_{index:02d}_ratio_{hierarchy+1}.cnf',
                                    model.n, model.clauses)
                records.append(record)
                continue
            edge, coincident = zero_edge(row)
            if coincident:
                model = ThirdModel(geometry, row, hierarchy, third_geometries[edge])
                if cluster.proves_unsat(model.n, model.clauses):
                    counts['third_direction_unsat'] += 1
                    record['kind'] = 'third_direction_unsat'
                    if output:
                        cover.write_cnf(output/f'three_cluster_third_{index:02d}_ratio_{hierarchy+1}.cnf',
                                        model.n, model.clauses)
                    records.append(record)
                    continue
            kind, transformed, ratio, mirrored = normalized_endpoint(row, hierarchy)
            key = (kind, ratio)
            if key not in implications:
                proof_n, proof_c = endpoint_implication(geometry, transformed, ratio, third_geometries)
                name = f'three_cluster_implication_{kind}_ratio_{ratio+1}.cnf'
                implications[key] = name
                if output:
                    cover.write_cnf(output/name, proof_n, proof_c)
            record |= {'kind': kind, 'mirrored': mirrored, 'implication': implications[key]}
            counts[kind] += 1
            records.append(record)
    expected = Counter(direct_unsat=78, third_direction_unsat=12,
                       flat_z_half=4, exceptional_z_a=4, flat_u_zero=4,
                       flat_z_zero=4, exceptional_z_zero=4, flat_u_half=4)
    assert counts == expected, counts
    assert len(implications) == 12
    print('PASS 304 cells -> 38 shapes x 3 ratios: 78 direct, 12 third-direction exclusions, 24 metric cases', flush=True)
    print('PASS 12 combined directional/sign implications, including all leading-zero boundaries', flush=True)
    cluster.symbolic_metric()
    identities = symbolic_metric()
    if output:
        coverage = clauses+[[-(i+1)*value for i, value in enumerate(model)] for model in models]
        cover.write_cnf(output/'three_cluster_model_coverage.cnf', variables, coverage)
        (output/'three_cluster_blowup_cells.json').write_text(json.dumps({
            'cells': rows, 'canonical_cells': canonical, 'cases': records,
            'counts': dict(counts), 'identities': identities,
        }, indent=2)+'\n')
    print('Scope: exactly two adjacent A weights and one B weight vanish; other five weights stay positive.')


if __name__ == '__main__':
    main()
