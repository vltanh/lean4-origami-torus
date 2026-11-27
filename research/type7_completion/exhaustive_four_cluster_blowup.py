#!/usr/bin/env python3
"""Exact finite cover and metric checks for all 300 mixed four-zero cells.

Usage: python exhaustive_four_cluster_blowup.py [OUTPUT_DIRECTORY]

The analytic exclusions are in exhaustive_four_cluster_blowup.md and
exhaustive_four_cluster_v.md.  Generated certificates belong outside
the repository.  This is an asymptotic exclusion, not a height bound.
"""

from collections import Counter
from pathlib import Path
import json
import sys

import sympy as s

import remaining_cluster_blowup as cluster
import remaining_three_cluster_blowup as three
import exhaustive_four_cluster_v as vertical
from solver_chambers import base_formula, enumerate_models, marked_symmetries, write_cnf
from verify_linking import lit


_rank_three_cache = {}
_rank_nine_cache = {}


def append_cached(model, row, cache, method):
    """The rank-sign clauses are identical in all three A hierarchies."""
    key = cluster.cell_key(row)
    if key in cache:
        model.clauses.extend(map(list, cache[key]))
        return
    start = len(model.clauses)
    method(model, row)
    cache[key] = tuple(map(tuple, model.clauses[start:]))


class Model(cluster.Model):
    def rank_three(self, row):
        append_cached(self, row, _rank_three_cache, cluster.Model.rank_three)


class ThirdModel(three.ThirdModel):
    def rank_three(self, row):
        append_cached(self, row, _rank_three_cache, cluster.Model.rank_three)

    def rank9(self, row):
        append_cached(self, row, _rank_nine_cache, three.ThirdModel.rank9)


def zero_edges(row, key):
    return [i for i in range(4) if row[key][i] == row[key][(i+1) % 4]]


def coincident_edge(row):
    found = [i for i in zero_edges(row, 'x')
             if row['y'][i] == row['y'][(i+1) % 4]]
    assert len(found) <= 1, row
    return found[0] if found else None


def normalize(row, hierarchy):
    y = tuple(row['y'])
    mirrored = ((y == (0, 0, 0, 1) and hierarchy == 1)
                or y in ((0, 1, 1, 1), (1, 1, 0, 0)))
    if mirrored:
        row, hierarchy = cluster.transform(row, cluster.MIRROR), -hierarchy
    if cluster.cell_key(row) == cluster.cell_key(vertical.ROWS['opposite']):
        assert hierarchy == -1
        return 'opposite_v', row, hierarchy, mirrored
    if cluster.cell_key(row) == cluster.cell_key(vertical.ROWS['complementary']):
        assert hierarchy == -1
        return 'complementary_v', row, hierarchy, mirrored
    assert tuple(row['y']) == (0, 1, 1, 0) and hierarchy in (-1, 0), (row, hierarchy)
    kinds = {
        ((1, 0, 0, 0), (0, 1, 1, 0)): 'exceptional_zero_zero',
        ((1, 1, 1, 0), (0, 1, 1, 0)): 'flat_half_half',
        ((0, 1, 0, 0), (1, 0, 0, 1)): 'flat_zero_zero',
        ((1, 1, 0, 0), (1, 1, 1, 1)): 'flat_half_zero',
    }
    return kinds[tuple(row['x']), tuple(row['beta'])], row, hierarchy, mirrored


def endpoint_implication(geometry, kind, row, hierarchy, thirds):
    if kind.endswith('_v'):
        return vertical.sign_implication(geometry, kind[:-2])
    edge = coincident_edge(row)
    model = (ThirdModel(geometry, row, hierarchy, thirds[edge]) if edge is not None
             else Model(geometry, row, hierarchy))
    inverse = {vertex: i for i, vertex in enumerate(cluster.RELABEL)}
    required_literals = [cluster.cover.sign(value)*lit(tuple(
        inverse[i] for i in cluster.QUADS[abs(value)-1])) for value in cluster.flat.REQUIRED]
    assert required_literals == [53, 46, -3, 28]
    required = {'bx': 1, 'by': 0}
    violation = [-value for value in required_literals]+[model.trits['ay'][0]]
    if kind == 'exceptional_zero_zero' and hierarchy == -1:
        # The pure vertical a direction is a genuine surviving branch.
        violation.append(model.trits['ax'][0])
    else:
        required['ax'] = -1
    if edge is not None:
        assert edge in (1, 3)
        required |= {'cx': -1 if edge == 1 else 1, 'cy': 0}
    if hierarchy == 0:
        required['a13'] = 1
    violation += sum((model.deny(key, value) for key, value in required.items()), [])
    model.clauses.append(violation)
    assert cluster.proves_unsat(model.n, model.clauses), (kind, hierarchy)
    return model.n, model.clauses


def corner_metric_checks():
    t, x, g, U, H, Z, variables, edges, equations, kx, ky = cluster.metric_system()
    r, u, a, z, m = s.symbols('r u a z m')
    half = s.Rational(1, 2)
    beta = x[5]+half
    p, q = U[1]-x[1], beta+U[5]
    h36 = -(x[6]-x[3]+kx[3, 6])
    h67 = -(x[7]-x[6]+kx[6, 7])
    h72 = x[7]-x[2]+half
    mu36, mu67, mu72 = h36+U[6]-U[3], h67-U[7]+U[6], h72+U[7]-U[2]
    flat_P = (0, r, 0, u, half, r, half, z)
    flat_x = (0, -r, 0, -u, 0, r-half, 0, z-half)
    g2, slope = r-s.Rational(1, 8), half-2*r
    flat_g = (0, r/2, g2, g2+slope*u, r-s.Rational(1, 4), r/2,
              g2+slope/2, g2+slope*z)
    flat_params = {x[1]: -r, x[3]: x[2]-u, x[7]: x[2]+z-half}
    exc_P = (0, r, 0, half, half, 2*a*r, a, z)
    exc_x = (0, -r, 0, -half, 0, 2*a*r-half, a-half, z-half)
    exc_g = (0, 2*a*r-r/2, 2*a*r-s.Rational(1, 8), s.Rational(1, 8),
             2*a*r-s.Rational(1, 4), a*r, a/2-s.Rational(1, 8),
             2*a*r-2*r*z+z/2-s.Rational(1, 8))
    exc_params = {x[1]: -r, x[6]: x[2]+a-half, x[7]: x[2]+z-half}
    cases = (
        ('flat_zero_zero', False, {r: 0, u: 0, z: 0},
         (((2, 7), mu72),), -2048, (0, 0, -half), 0),
        ('flat_half_half', False, {r: 0, u: half, z: half},
         (((3, 6), mu36), ((6, 7), mu67)), 2048, (half, -half, 0, 0), -half),
        ('flat_half_zero', False, {r: 0, u: half, z: 0},
         (((3, 6), mu36), ((2, 7), mu72)), 2048, (half, 0, 0, -half), 0),
        ('exceptional_zero_zero', True, {r: 0, a: 0, z: 0},
         (((6, 7), mu67), ((2, 7), mu72)), -2048, (1, -half, 0, -half), 0),
    )
    records = {}
    for name, exceptional, endpoint, extras, expected_det, expected_coeffs, expected_cubic in cases:
        P, fx, fg, params = (exc_P, exc_x, exc_g, exc_params) if exceptional else (
            flat_P, flat_x, flat_g, flat_params)
        family = ({x[i]: fx[i] for i in range(1, 8)} | {g[i]: fg[i] for i in range(1, 8)}
                  | {U[i]: -P[i] for i in cluster.FREE}
                  | {H[i]: fg[i] for i in cluster.FREE} | {Z[i]: 0 for i in cluster.FREE})
        assert all(s.expand(eq.subs(family)) == 0 for eq in equations)
        defects = (((0, 1), p), ((0, 5), q))+extras
        indices = [edges.index(edge) for edge, _ in defects]
        modified = list(equations)
        for index, (_, defect) in zip(indices, defects):
            modified[index] = defect
            assert s.expand(defect.subs(family)) == 0
        modified = [eq.subs(params) for eq in modified]
        dependent = [v for v in variables if v not in params]
        jacobian = s.Matrix(modified).jacobian(dependent).subs(family).subs(t, 0).subs(endpoint)
        determinant = jacobian.det(method='domain-ge')
        assert determinant == expected_det, (name, determinant)
        inverse = jacobian.inv(method='DM')
        F = s.Matrix([[int(v == U[1])-int(v == U[5]) for v in dependent]])
        beta_gradient = s.Matrix([beta]).jacobian(dependent)
        coefficients, beta_coefficients = [], []
        for index, expected in zip(indices, expected_coeffs):
            force = s.zeros(21, 1)
            force[index] = 1
            jet = inverse*force
            coefficient = s.factor((F*jet)[0])
            assert coefficient == expected
            coefficients.append(str(coefficient))
            beta_coefficients.append(s.factor((beta_gradient*jet)[0]))
        normal = s.Matrix([0 if index in indices else (Z[j]-Z[i])**2
                           for index, (i, j) in enumerate(edges)]).subs(
                               {Z[i]: int(i in (6, 7)) for i in cluster.FREE})
        normal_jet = -inverse*normal
        cubic = s.factor((F*normal_jet)[0])
        beta_normal = s.factor((beta_gradient*normal_jet)[0])
        assert cubic == expected_cubic and beta_normal == expected_cubic
        if exceptional:
            assert tuple(beta_coefficients) == (0, half, 0, -half)
            assert s.expand((h67+h72).subs(params)-a) == 0
            assert s.expand((-U[6]+U[2]-(a-mu67-mu72)).subs(params)) == 0
        records[name] = {'determinant': int(determinant), 'functional_defect_coefficients': coefficients,
                         'beta_defect_coefficients': list(map(str, beta_coefficients)),
                         'cubic': str(cubic), 'beta_normal': str(beta_normal)}
        print(f'PASS {name}: determinant {determinant}, exact defect and normal coefficients', flush=True)

    # The exact expanded reference simultaneously handles 36 and either
    # 67 or72.  No uncontrolled power of mu36 remains in a Taylor error.
    aa, beta0 = (1-m)/2, r*(1-m)
    P = (0, r, 0, u, half, beta0, aa, z)
    fx = (0, -r, 0, -u, 0, beta0-half, aa-half, z-half)
    fg = (0, 2*aa*r-r/2, 2*aa*r-s.Rational(1, 8),
          -4*aa*r*u+2*aa*r+u/2-s.Rational(1, 8),
          2*aa*r-s.Rational(1, 4), aa*r, aa/2-s.Rational(1, 8),
          2*aa*r-2*r*z+z/2-s.Rational(1, 8))
    expanded = ({x[i]: fx[i] for i in range(1, 8)} | {g[i]: fg[i] for i in range(1, 8)}
                | {U[i]: -P[i] for i in cluster.FREE} | {H[i]: fg[i] for i in cluster.FREE})
    normals = {Z[i]: 0 for i in cluster.FREE}
    for defect in (p, q, mu67, mu72):
        assert s.expand(defect.subs(expanded)) == 0
    assert s.expand(mu36.subs(expanded)-m) == 0
    for edge, eq in zip(edges, equations):
        expected = m*(2*u-1) if edge == (3, 6) else 0
        assert s.expand(eq.subs(expanded).subs(normals)-expected) == 0
    levels = {i: int(i in cluster.B) for i in range(8)}
    points = {i: (-U[i], Z[i], levels[i]-2*t*H[i]) for i in range(8)}
    forms = []
    for literal in cluster.flat.REQUIRED:
        first, *rest = cluster.QUADS[abs(literal)-1]
        forms.append(cluster.cover.sign(literal)*s.Matrix([
            [points[i][j]-points[first][j] for j in range(3)] for i in rest]).det())
    N, D = 4+t*(4*r-1)**2, 4+t*(32*r*u-8*r-8*u+1)
    functional = s.expand(sum(weight*form for weight, form in zip(
        ((1-2*u)*N, 2*u*N, N, D), forms)).subs(expanded))
    old = -4*r*(half-r)*u*t*N*Z[6]
    extra = s.cancel((functional-old)/m)
    assert s.expand(extra.subs(t, 0)-2*(-Z[1]+2*r*Z[4]+Z[5]-2*r*Z[6])) == 0
    for vertex in (4, 6, 7):
        assert s.expand(extra).coeff(Z[vertex]).subs(r, 0) == 0
    assert s.simplify(s.expand(extra).coeff(Z[1]).subs(r, 0)+(t+4)**2/8) == 0
    assert s.simplify(s.expand(extra).coeff(Z[5]).subs(r, 0)+(t+4)*(8*t*u-t-4)/8) == 0
    records['expanded_reference_functional'] = str(s.factor(extra))

    # Exact determinant used at exceptional00.  Its second and third
    # rows are the actual A-path15 and B-path26, not absolute errors.
    lp, lz, lh, dp, dz, dh, cp, cz, ch = s.symbols('lp lz lh dp dz dh cp cz ch')
    determinant = s.Matrix([[lp, lz, 1-2*t*lh], [dp, dz, -2*t*dh],
                            [cp, cz, -2*t*ch]]).det()
    factored = ((1-2*t*lh)*(dp*cz-dz*cp)+2*t*dh*(lp*cz-lz*cp)
                -2*t*ch*(lp*dz-lz*dp))
    assert s.expand(determinant-factored) == 0
    print('PASS simultaneous exact expanded references, Farkas factors, and exceptional bracket identity', flush=True)
    return records


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
    rows = [row for row in all_cells if len(zero_edges(row, 'a'))+len(zero_edges(row, 'x')) == 4]
    assert all(len(zero_edges(row, 'a')) == len(zero_edges(row, 'x')) == 2 for row in rows)
    canonical = [row for row in rows if tuple(row['a']) == (0, 0, 0, 1)]
    assert (len(rows), len(canonical)) == (300, 35)
    cluster.canonical_maps(rows, canonical, symmetries)
    geometry = cluster.Geometry()
    thirds = {index: three.ThirdGeometry(index) for index in range(4)}
    records, implications, counts = [], {}, Counter()
    for index, row in enumerate(canonical):
        for hierarchy in (-1, 0, 1):
            model = Model(geometry, row, hierarchy)
            record = {'cell': index, 'hierarchy': hierarchy}
            if cluster.proves_unsat(model.n, model.clauses):
                kind = 'direct_unsat'
                name = f'four_cluster_cell_{index:02d}_ratio_{hierarchy+1}.cnf'
            else:
                edge = coincident_edge(row)
                model = (ThirdModel(geometry, row, hierarchy, thirds[edge])
                         if edge is not None else model)
                if edge is not None and cluster.proves_unsat(model.n, model.clauses):
                    kind = 'third_direction_unsat'
                    name = f'four_cluster_third_{index:02d}_ratio_{hierarchy+1}.cnf'
                else:
                    kind, transformed, ratio, mirrored = normalize(row, hierarchy)
                    key = (kind, ratio)
                    if key not in implications:
                        n, proof = endpoint_implication(geometry, kind, transformed, ratio, thirds)
                        filename = f'four_cluster_implication_{kind}_ratio_{ratio+1}.cnf'
                        implications[key] = filename
                        if output:
                            write_cnf(output/filename, n, proof)
                    record |= {'kind': kind, 'mirrored': mirrored,
                               'normalized_hierarchy': ratio, 'implication': implications[key]}
                    counts[kind] += 1
                    records.append(record)
                    continue
            record['kind'] = kind
            counts[kind] += 1
            records.append(record)
            if output:
                write_cnf(output/name, model.n, model.clauses)
        if index % 7 == 6:
            print(f'PASS directional cover through canonical shape {index+1}/35', flush=True)
    expected = Counter(direct_unsat=73, third_direction_unsat=12, opposite_v=2,
                       complementary_v=2, exceptional_zero_zero=4, flat_half_half=4,
                       flat_zero_zero=4, flat_half_zero=4)
    assert counts == expected, counts
    assert len(implications) == 10
    identities = corner_metric_checks()
    identities['vertical_V'] = {kind: vertical.metric_checks(kind) for kind in vertical.ROWS}
    if output:
        coverage = clauses+[[-(i+1)*value for i, value in enumerate(model)] for model in models]
        write_cnf(output/'four_cluster_model_coverage.cnf', variables, coverage)
        (output/'four_cluster_blowup_cells.json').write_text(json.dumps({
            'cells': rows, 'canonical_cells': canonical, 'cases': records,
            'counts': dict(counts), 'identities': identities,
        }, indent=2)+'\n')
    print('PASS all300 mixed four-zero cells:73 direct+12 virtual-edge exclusions+20 metric cases')
    print('PASS ten zero-retaining directional/sign implications;96 CNFs including model coverage')
    print('Scope: this asymptotic stratum only; no fixed-height or Lean theorem.')


if __name__ == '__main__':
    main()
