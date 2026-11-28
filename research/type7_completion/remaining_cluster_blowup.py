#!/usr/bin/env python3
"""Exact certificates for a triple cluster facing a positive-weight cap.

Usage: python remaining_cluster_blowup.py [OUTPUT_DIRECTORY]

The first normal blow-up has collinear A and noncollinear B. Exactly
its two adjacent A edges have zero physical weights. All 544 cells
are excluded by the proof in remaining_cluster_blowup.md. Generated
certificates belong outside the repository.
"""

import sys
import sympy as s
from itertools import combinations, product
from functools import lru_cache
import json, time, collections
from remaining_one_v import topology, DirectionalModel
import remaining_one_collinear as cover
from remaining_one_collinear import write_cnf
from verify_linking import SAT, lit

class Geometry:
    """Factored leading determinants with arbitrary affine B coordinates."""

    def __init__(self):
        self.keys = ['ax', 'ay', 'bx', 'by', 'ab', 'Ax', 'Ay'] + [e + str(i) + str(j) for e in ('a', 'b', 'A') for i, j in cover.PAIRS]
        ax, ay, bx, by, eps = s.symbols('ax ay bx by eps')
        X = s.symbols('X0:4')
        Y = s.symbols('Y0:4')
        p = {0: (0, 0, 0), 1: (eps * ax, eps * ay, 0), 4: (eps * (ax + bx), eps * (ay + by), 0), 5: (1, 0, 0)} | {v: (X[i], Y[i], 1) for i, v in enumerate(cover.B)}
        forms = {'ax': ax, 'ay': ay, 'bx': bx, 'by': by, 'Ax': ax + bx, 'Ay': ay + by}
        for e, v in [('a', (ax, ay)), ('b', (bx, by)), ('A', (ax + bx, ay + by))]:
            for i, j in cover.PAIRS:
                forms[e + str(i) + str(j)] = v[0] * (Y[j] - Y[i]) - v[1] * (X[j] - X[i])
        cf = {('y', i, j): Y[j] - Y[i] for i, j in cover.PAIRS}
        for k, (i, j, l) in enumerate(cover.TRIPLES):
            cf['beta', k] = (X[j] - X[i]) * (Y[l] - Y[i]) - (Y[j] - Y[i]) * (X[l] - X[i])
        self.const = []
        self.lin = []
        self.quad = []
        for q in combinations(range(8), 4):
            first, *rest = q
            idx = lit(q)
            f = s.expand(s.Matrix([[p[i][k] - p[first][k] for k in range(3)] for i in rest]).det())
            con = f.coeff(eps, 0)
            if con:
                match = [(key, di) for key, v in cf.items() for di in (-1, 1) if s.expand(con - di * v) == 0]
                assert match, (q, con)
                self.const.append((idx, *match[0]))
                continue
            lin = f.coeff(eps, 1)
            if lin:
                match = [(key, di) for key, v in forms.items() for di in (-1, 1) if s.expand(lin - di * v) == 0]
                assert match, (q, lin)
                key, di = match[0]
                pair = {'a': (0, 1), 'b': (1, 4), 'A': (0, 4)}[key[0]]
                assert set(pair) <= set(q)
                self.lin.append((idx, key, di))
                continue
            quad = f.coeff(eps, 2)
            if quad:
                di = s.simplify(quad / (ax * by - ay * bx))
                assert di in (-1, 1)
                self.quad.append((idx, int(di)))
        assert (len(self.const), len(self.lin), len(self.quad)) == (34, 30, 4)

class Model(DirectionalModel):
    """Necessary rank-three signs of E,F,a,b at infinity and four B points."""

    def __init__(self, G, row, hierarchy):
        self.n, orig = topology()
        self.clauses = [list(v) for v in orig]
        self.trits = {}
        for key in G.keys:
            self.trits[key] = (self.n + 1, self.n + 2)
            self.n += 2
            self.clauses.append([-self.n + 1, -self.n])
        for e in ('a', 'b'):
            self.clauses.append(list(self.trits[e + 'x']) + list(self.trits[e + 'y']))
        for tail in ('x', 'y') + tuple((str(i) + str(j) for i, j in cover.PAIRS)):
            if hierarchy == 0:
                self.clauses.extend(self.sum_clauses('a' + tail, 'b' + tail, 'A' + tail))
            else:
                self.equal(('a' if hierarchy < 0 else 'b') + tail, 'A' + tail)
        for idx, key, di in G.lin:
            self.bracket_link(idx, key, di)
        for idx, di in G.quad:
            self.bracket_link(idx, 'ab', di)
        for idx, key, di in G.const:
            value = cover.pair_sign(row['y'], key[1], key[2]) if key[0] == 'y' else row['beta'][key[1]]
            if value:
                self.clauses.append([idx * di * value])
        self.rank_three(row)

    def rank_three(self, row):
        entries = {}
        twoinf = {(0, 1): 1, (0, 2): ('ay', 1), (0, 3): ('by', 1), (1, 2): ('ax', -1), (1, 3): ('bx', -1), (2, 3): ('ab', 1)}
        for q in combinations(range(8), 3):
            inf = [i for i in q if i < 4]
            bi = [i - 4 for i in q if i >= 4]
            if len(inf) == 3:
                val = 0
            elif len(inf) == 2:
                val = twoinf[tuple(inf)]
            elif len(inf) == 1:
                i, j = bi
                if inf[0] == 0:
                    val = -cover.pair_sign(row['y'], i, j)
                elif inf[0] == 1:
                    val = cover.pair_sign(row['x'], i, j)
                else:
                    val = (('a' if inf[0] == 2 else 'b') + str(i) + str(j), -1)
            else:
                val = row['beta'][cover.TRIPLES.index(tuple(bi))]
            entries[q] = val

        def ent(q):
            di = (-1) ** sum((q[i] > q[j] for i, j in combinations(range(3), 2)))
            v = entries[tuple(sorted(q))]
            return (v[0], di * v[1]) if isinstance(v, tuple) else di * v
        clauses = set()
        for common in range(8):
            for a, b, c, d in combinations([i for i in range(8) if i != common], 4):
                terms = [(1, ent((common, a, b)), ent((common, c, d))), (-1, ent((common, a, c)), ent((common, b, d))), (1, ent((common, a, d)), ent((common, b, c)))]
                terms = [z for z in terms if z[1] != 0 and z[2] != 0]
                keys = sorted({v[0] for z in terms for v in z[1:] if isinstance(v, tuple)})
                for values in product((-1, 0, 1), repeat=len(keys)):
                    env = dict(zip(keys, values))

                    def evaluate(v):
                        return v[1] * env[v[0]] if isinstance(v, tuple) else v
                    ts = [di * evaluate(v) * evaluate(w) for di, v, w in terms]
                    if any(ts) and (min(ts) >= 0 or max(ts) <= 0):
                        clauses.add(tuple(sum((self.deny(key, v) for key, v in env.items()), [])))
        self.clauses.extend(map(list, sorted(clauses)))


from collections import Counter
from pathlib import Path
import remaining_flat_blowup as flat
from direct_metric import load_data
from solver_chambers import base_formula, enumerate_models, marked_symmetries

A, B, FREE = cover.A, cover.B, flat.FREE
QUADS = tuple(combinations(range(8), 4))
MIRROR = (4, 1, 6, 3, 0, 5, 2, 7)
RELABEL = (5, 0, 3, 6, 1, 4, 7, 2)


def proves_unsat(variables, clauses):
    solver = SAT(variables, clauses)
    try:
        return solver.check() == -1
    finally:
        # Hundreds of independent cells should not retain hundreds of
        # native Z3 contexts until the producer exits.
        solver.z.Z3_del_context.restype = None
        solver.z.Z3_del_context.argtypes = [solver.P]
        solver.z.Z3_del_context(solver.ctx)


def cell_key(row):
    return tuple(tuple(row[key]) for key in ('a', 'x', 'y', 'beta'))


def transform(row, permutation, sx=1, sy=1):
    ai = [A.index(permutation[i]) for i in A]
    bi = [B.index(permutation[i]) for i in B]
    result = {key: flat.rank_tuple([direction*row[key][i] for i in indices])
              for key, direction, indices in (('a', sx, ai), ('x', sx, bi), ('y', sy, bi))}
    result['beta'] = []
    for triple in cover.TRIPLES:
        mapped = [bi[i] for i in triple]
        parity = (-1)**sum(mapped[i] > mapped[j] for i, j in combinations(range(3), 2))
        result['beta'].append(sx*sy*parity*row['beta'][cover.TRIPLES.index(tuple(sorted(mapped)))])
    return result


def canonical_maps(rows, canonical, symmetries):
    index = {cell_key(row): i for i, row in enumerate(canonical)}
    entries = [entry for entry in symmetries
               if {entry['permutation'][i] for i in A} == set(A)]
    assert all(entry['phase_preserving'] for entry in entries)
    permutations = [entry['permutation'] for entry in entries]
    assert MIRROR in map(tuple, permutations) and RELABEL in map(tuple, permutations)
    for row in rows:
        maps = []
        for permutation, sx, sy in product(permutations, (-1, 1), (-1, 1)):
            transformed = transform(row, permutation, sx, sy)
            if cell_key(transformed) in index:
                maps.append({'cell': index[cell_key(transformed)], 'permutation': permutation,
                             'horizontal_reflection': sx, 'normal_reflection': sy})
        assert maps, row
        row['canonical_map'] = maps[0]


def normalized_survivor(row, hierarchy):
    y, beta = tuple(row['y']), tuple(row['beta'])
    mirror = ((y == (0, 0, 0, 1) and hierarchy == 1)
              or y in ((1, 1, 0, 1), (1, 1, 0, 0)))
    if mirror:
        row, hierarchy = transform(row, MIRROR), -hierarchy
        y, beta = tuple(row['y']), tuple(row['beta'])
    x = row['x']
    if (y == (0, 0, 0, 1) and beta == (0, -1, 0, 1)
            and x[0] == x[2] and x[1] < x[0] and hierarchy == -1):
        kind = 'opposite_v'
    elif (y == (0, 1, 1, 1) and beta == (-1, 0, 1, 0)
          and x[1] == x[3] and x[1] < min(x[0], x[2]) and hierarchy == 1):
        kind = 'complementary_v'
    elif (y == (0, 1, 1, 0) and beta == (1, 1, 1, 1)
          and x[3] < x[2] < x[1] and x[3] < x[0] and hierarchy in (-1, 0)):
        kind = 'flat_endpoint' if x[1] > x[0] else 'exceptional_endpoint'
    else:
        return None
    return kind, row, hierarchy, mirror


def implication_certificate(geometry, kind, row, hierarchy):
    model = Model(geometry, row, hierarchy)
    cap = lit((0, 1, 4, 5))
    if kind == 'opposite_v':
        required = {'ax': 1, 'ay': 0, 'b03': 0, 'by': 1}
        violation = [cap]
    elif kind == 'complementary_v':
        required = {'bx': -1, 'by': 0, 'a01': 0, 'ay': -1}
        violation = [-cap]
    else:
        inverse = {vertex: i for i, vertex in enumerate(RELABEL)}
        required_literals = [cover.sign(value)*lit(tuple(inverse[i] for i in QUADS[abs(value)-1]))
                             for value in flat.REQUIRED]
        assert required_literals == [53, 46, -3, 28]
        violation = [-value for value in required_literals]
        required = {'bx': 1, 'by': 0}
        if kind == 'exceptional_endpoint':
            required['ax'] = -1
            # This forbids a positive LIMIT ay. In the comparable
            # branch the a13 zero trit is explicitly forbidden too.
            violation.append(model.trits['ay'][0])
            if hierarchy == 0:
                required['a13'] = 1
    violation += sum((model.deny(key, value) for key, value in required.items()), [])
    model.clauses.append(violation)
    assert proves_unsat(model.n, model.clauses), (kind, row, hierarchy)
    return model.n, model.clauses


def metric_system():
    _, _, edges, _, _, kx, ky = load_data()
    t = s.Symbol('t')
    x = [s.Integer(0)]+list(s.symbols('x1:8'))
    g = [s.Integer(0)]+list(s.symbols('g1:8'))
    U = {0: s.Integer(0), 2: x[2], 3: x[3]}
    H = {0: s.Integer(0), 2: g[2], 3: g[3]}
    Z = {0: s.Integer(0), 2: s.Integer(0), 3: s.Integer(0)}
    for i in FREE:
        U[i], H[i], Z[i] = s.symbols(f'U{i} H{i} Z{i}')
    variables = x[1:]+g[1:]+[U[i] for i in FREE]+[H[i] for i in FREE]
    levels = {i: int(i in B) for i in range(8)}
    metric_edges = [edge for edge in edges if edge not in ((0, 2), (0, 3), (2, 3))]
    equations = []
    for i, j in metric_edges:
        du, dz = U[j]-U[i], Z[j]-Z[i]
        dx, dg, dh = x[j]-x[i]+kx[i, j], g[j]-g[i], H[j]-H[i]
        ell = levels[j]-levels[i]
        equations.append(s.expand(du**2+dz**2-dx**2-ell*dh-2*ky[i, j]*dg+t*(dh**2-dg**2)))
    return t, x, g, U, H, Z, variables, metric_edges, equations, kx, ky


def symbolic_metric():
    t, x, g, U, H, Z, variables, edges, equations, kx, ky = metric_system()
    r, u, a, z = s.symbols('r u a z')
    half = s.Rational(1, 2)
    equation_map = dict(zip(edges, equations))
    mu1 = U[1]-x[1]
    beta5 = x[5]+half
    mu5 = beta5+U[5]
    assert s.expand(equation_map[1, 3]-equation_map[0, 1]
                    -(1-2*t*g[3])*(H[1]-g[1])+2*x[3]*mu1) == 0
    assert s.expand(equation_map[0, 5]-Z[5]**2-t*(H[5]-g[5])*(H[5]+g[5])
                    +mu5*(beta5-U[5])) == 0
    indices = [edges.index((0, 1)), edges.index((0, 5))]
    mode = {Z[i]: int(i in (6, 7)) for i in FREE}
    levels = {i: int(i in B) for i in range(8)}
    points = {i: (-U[i], Z[i], levels[i]-2*t*H[i]) for i in range(8)}
    forms = []
    for literal in flat.REQUIRED:
        first, *rest = QUADS[abs(literal)-1]
        forms.append(cover.sign(literal)*s.Matrix(
            [[points[i][k]-points[first][k] for k in range(3)] for i in rest]).det())
    assert s.expand(sum(weight*form for weight, form in zip((1-2*u, 2*u, 1, 1), forms))
                    .subs(t, 0).subs(mode)-U[1]+U[5]) == 0

    flat_P = (0, r, 0, u, half, r, half, z)
    flat_x = (0, -r, 0, -u, 0, r-half, 0, z-half)
    slope, g2 = half-2*r, r-s.Rational(1, 8)
    flat_g = (0, r/2, g2, g2+slope*u, r-s.Rational(1, 4), r/2,
              g2+slope/2, g2+slope*z)
    exceptional_P = (0, 0, 0, half, half, 0, a, z)
    exceptional_x = (0, 0, 0, -half, 0, -half, a-half, z-half)
    exceptional_g = (0, 0, -s.Rational(1, 8), s.Rational(1, 8), -s.Rational(1, 4), 0,
                     a/2-s.Rational(1, 8), z/2-s.Rational(1, 8))
    cases = (
        ('flat_endpoint', flat_P, flat_x, flat_g,
         {x[1]: -r, x[3]: x[2]-u, x[7]: x[2]+z-half}, (x[1], x[3], x[7]),
         4096*z*(2*u-1)*(2*z-1), (u, -z)),
        ('exceptional_endpoint', exceptional_P, exceptional_x, exceptional_g,
         {x[1]: -r, x[6]: x[2]+a-half, x[7]: x[2]+z-half}, (x[1], x[6], x[7]),
         -8192*z*(z-a)*(2*a-1), (1-a, a-z-half)),
    )
    output = {}
    necessity_matrices = []
    for kind, P, family_x, family_g, parameters, free, expected_det, expected_defects in cases:
        family = ({x[i]: family_x[i] for i in range(1, 8)}
                  | {g[i]: family_g[i] for i in range(1, 8)}
                  | {U[i]: -P[i] for i in FREE}
                  | {H[i]: family_g[i] for i in FREE}
                  | {Z[i]: 0 for i in FREE})
        assert all(s.expand(equation.subs(family)) == 0 for equation in equations)
        # Verify uniqueness of the actual limiting intrinsic and axial
        # data, rather than merely exhibiting a reference solution.
        intrinsic_x = lambda i, j: x[j]-x[i]+kx[i, j]
        intrinsic_g = lambda i, j: g[j]-g[i]
        distance = lambda i, j: intrinsic_x(i, j)**2+2*ky[i, j]*intrinsic_g(i, j)
        weight = lambda i, j: -s.sympify(family_x[j]-family_x[i]+kx[i, j]).subs(r, 0)
        physical = lambda i, j: s.sympify(P[j]-P[i]).subs(r, 0)
        stress_equations = []
        for ai, aj in zip(A, A[1:]+A[:1]):
            for bi, bj in zip(B, B[1:]+B[:1]):
                stress = (intrinsic_x(ai, aj)*intrinsic_x(bi, bj)
                          -(distance(ai, bj)+distance(aj, bi)-distance(ai, bi)-distance(aj, bj))/2)
                target = weight(ai, aj)*weight(bi, bj)-physical(ai, aj)*physical(bi, bj)
                stress_equations.append(s.expand(stress-target))
        for cap in (A, B):
            stress_equations.extend(intrinsic_x(i, j)+weight(i, j)
                                    for i, j in zip(cap, cap[1:]+cap[:1]))
        matrix, rhs = s.linear_eq_to_matrix(stress_equations, x[1:]+g[1:])
        assert matrix.shape == (24, 14) and matrix.rank() == 14
        values = s.Matrix(list(family_x[1:])+list(family_g[1:])).subs(r, 0)
        assert all(s.expand(value) == 0 for value in matrix*values-rhs)
        fixed = {key: value for key, value in family.items() if key not in {H[i] for i in FREE}}
        height_equations = [s.expand(equation.subs(t, 0).subs(fixed).subs(r, 0))
                            for equation, (i, j) in zip(equations, edges) if levels[i] != levels[j]]
        height_matrix, height_rhs = s.linear_eq_to_matrix(height_equations, [H[i] for i in FREE])
        assert height_matrix.shape == (14, 5) and height_matrix.rank() == 5
        assert all(s.expand(value) == 0 for value in
                   height_matrix*s.Matrix([family_g[i] for i in FREE]).subs(r, 0)-height_rhs)
        necessity_matrices.append((matrix, height_matrix))
        dependent = [value for value in variables if value not in free]
        modified = list(equations)
        modified[indices[0]], modified[indices[1]] = mu1, mu5
        modified = [equation.subs(parameters) for equation in modified]
        jacobian = s.Matrix(modified).jacobian(dependent).subs(family).subs({t: 0, r: 0})
        determinant = s.factor(jacobian.det(method='domain-ge'))
        assert s.expand(determinant-expected_det) == 0
        inverse = jacobian.inv(method='DM')
        defect_coefficients, beta_coefficients = [], []
        for index, expected in zip(indices, expected_defects):
            forcing = s.zeros(21, 1)
            forcing[index] = 1
            linear = inverse*forcing
            coefficient = s.factor(linear[dependent.index(U[1])]-linear[dependent.index(U[5])])
            assert s.simplify(coefficient-expected) == 0
            defect_coefficients.append(str(coefficient))
            beta_coefficients.append(s.factor(linear[dependent.index(x[5])]))
        normal_forcing = s.Matrix([
            0 if index in indices else (Z[j]-Z[i])**2
            for index, (i, j) in enumerate(edges)
        ]).subs(mode)
        quadratic = inverse*(-normal_forcing)
        cubic = s.factor(quadratic[dependent.index(U[1])]-quadratic[dependent.index(U[5])])
        assert s.simplify(cubic+1/(4*z)) == 0
        data = {'determinant': str(determinant), 'defect_coefficients': defect_coefficients,
                'cubic_coefficient': str(cubic)}
        if kind == 'exceptional_endpoint':
            forcing = -s.Matrix(modified).diff(r).subs(family).subs({t: 0, r: 0})
            linear = inverse*forcing
            r_coefficient = s.factor(linear[dependent.index(U[1])]-linear[dependent.index(U[5])])
            beta_r = s.factor(linear[dependent.index(x[5])])
            beta_normal = s.factor(quadratic[dependent.index(x[5])])
            assert (r_coefficient, beta_r, beta_normal) == (2*a-1, 2*a, -1/(4*z))
            assert all(s.simplify(actual-expected) == 0
                       for actual, expected in zip(beta_coefficients, (-a, a-z+half)))
            numerator, denominator = 4+t, 4-3*t
            family_without_normals = {key: value for key, value in family.items() if key not in Z.values()}
            baseline = s.expand((numerator*forms[1]+numerator*forms[2]+denominator*forms[3])
                                .subs(family_without_normals))
            expected = (2*a-1)*(t+4)*((t+4)*Z[1]+(3*t-4)*Z[5])/8
            assert s.expand(baseline-expected) == 0
            data |= {'r_coefficient': str(r_coefficient), 'beta_r': str(beta_r),
                     'beta_defects': list(map(str, beta_coefficients)),
                     'beta_normal': str(beta_normal), 'reference_farkas_numerator': str(expected)}
        output[kind] = data
        print(f'PASS {kind}: determinant {determinant}; defects {defect_coefficients}; cubic {cubic}', flush=True)

    assert necessity_matrices[0] == necessity_matrices[1]
    print('PASS both endpoint necessity systems: identical constant ranks 14 and 5', flush=True)

    intrinsic_x = lambda i, j: x[j]-x[i]+kx[i, j]
    intrinsic_g = lambda i, j: g[j]-g[i]
    distance = lambda i, j: (intrinsic_x(i, j)**2+ky[i, j]**2/t
                              +2*ky[i, j]*intrinsic_g(i, j)+t*intrinsic_g(i, j)**2)
    stress = lambda i, j, k, l: s.expand(
        intrinsic_x(i, j)*intrinsic_x(k, l)+t*intrinsic_g(i, j)*intrinsic_g(k, l)
        -(distance(i, l)+distance(j, k)-distance(i, k)-distance(j, l))/2)
    c0 = -x[2]+s.Rational(1, 4)+2*g[2]
    assert s.expand(c0-2*stress(0, 1, 6, 7)-2*stress(0, 1, 7, 2)) == 0
    assert s.expand(stress(0, 1, 3, 6)+x[1]/2+g[1]) == 0
    beta, q, length, horizontal = s.symbols('beta q length horizontal')
    difference = s.expand((distance(2, 4)-distance(1, 2)).subs(
        {x[4]: x[1]+half-beta, g[4]: g[1]+q*beta})/beta)
    assert s.expand(difference-(-q+2*x[2]-1)).subs({t: 0, beta: 0, x[1]: 0}) == 0
    rho5 = s.Rational(3, 4)-x[2]
    complementary_height = s.expand(2*((half-2*x[2])+2*rho5)).subs(x[2], half-length)
    assert s.expand(complementary_height-8*length) == 0
    assert s.simplify((-1/length)*complementary_height+8) == 0
    opposite_height = 2*horizontal-6*length
    assert {s.simplify(-opposite_height.subs(horizontal, direction*length)/length)
            for direction in (-1, 1)} == {s.Integer(4), s.Integer(8)}
    eta = s.Symbol('eta')
    # a13=det(a,B7-B3), after dividing a by its positive physical
    # weight and applying the normal stretch.
    assert s.det(s.Matrix([[-1, -eta], [-a, -1]])) == 1-a*eta
    print('PASS exact defect identities, V relative heights, and exceptional slope equality', flush=True)
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
    all_cells, _ = flat.degenerate_cover(models)
    rows = [row for row in all_cells
            if sum(row['a'][i] == row['a'][(i+1) % 4] for i in range(4)) == 2
            and all(row['x'][i] != row['x'][(i+1) % 4] for i in range(4))]
    canonical = [row for row in rows if tuple(row['a']) == (0, 0, 0, 1)]
    assert len(rows) == 544 and len(canonical) == 61
    canonical_maps(rows, canonical, symmetries)
    geometry = Geometry()
    records, implications, counts = [], {}, Counter()
    for index, row in enumerate(canonical):
        for hierarchy in (-1, 0, 1):
            survivor = normalized_survivor(row, hierarchy)
            record = {'cell': index, 'hierarchy': hierarchy}
            if survivor is None:
                model = Model(geometry, row, hierarchy)
                assert proves_unsat(model.n, model.clauses), record
                counts['direct_unsat'] += 1
                if output:
                    cover.write_cnf(output/f'cluster_cell_{index:02d}_ratio_{hierarchy+1}.cnf', model.n, model.clauses)
            else:
                kind, transformed, ratio, mirror = survivor
                key = (kind, cell_key(transformed), ratio)
                if key not in implications:
                    proof_n, proof_c = implication_certificate(geometry, kind, transformed, ratio)
                    name = f'cluster_implication_{len(implications):02d}_{kind}.cnf'
                    implications[key] = name
                    if output:
                        cover.write_cnf(output/name, proof_n, proof_c)
                record |= {'kind': kind, 'mirrored': mirror, 'implication': implications[key]}
                counts[kind] += 1
            records.append(record)
    assert counts == Counter(direct_unsat=153, opposite_v=8, complementary_v=6,
                             flat_endpoint=12, exceptional_endpoint=4), counts
    assert len(implications) == 15
    print('PASS 544 cells -> 61 shapes x 3 ratios: 153 direct exclusions and 30 metric cases', flush=True)
    print('PASS 15 directional/sign implications, retaining every leading-zero boundary', flush=True)
    flat.symbolic_metric()
    identities = symbolic_metric()
    if output:
        coverage = clauses+[[-(i+1)*value for i, value in enumerate(model)] for model in models]
        cover.write_cnf(output/'cluster_model_coverage.cnf', variables, coverage)
        (output/'cluster_blowup_cells.json').write_text(json.dumps({
            'cells': rows, 'canonical_cells': canonical, 'cases': records,
            'counts': dict(counts), 'identities': identities,
        }, indent=2)+'\n')
    print('Scope: exactly the two cluster edges vanish; all four partner weights stay positive.')


if __name__ == '__main__':
    main()
