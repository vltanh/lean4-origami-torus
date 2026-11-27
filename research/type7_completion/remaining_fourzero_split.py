#!/usr/bin/env python3
"""Exclude the 32 four-zero triple/split two-line blow-up orders.

Usage: python remaining_fourzero_split.py [OUTPUT_DIRECTORY]

The four-defect chart is regular even when all four edge weights vanish.
Its exact planar reference family has coincident vertices 0 and 4.  The
normal-square correction gives their nonedge a necessary direction that
contradicts all three relative-scale orientation formulas.  The proof is
in remaining_fourzero_split.md; no explicit height bound is claimed.
"""

from collections import Counter
from itertools import combinations, product
import json
from pathlib import Path
import sys

import sympy as s

import common_line_edge_collapse as two_line
from direct_metric import load_data
import remaining_fourzero_blowup as fourzero
from remaining_one_v import DirectionalModel
import solver_chambers as chambers
from verify_linking import SAT
from verify_nonparallel_corner import allowed_sum

A, B = (0, 1, 4, 5), (2, 3, 6, 7)
FREE = (1, 4, 5, 6, 7)
HALF = s.Rational(1, 2)
DEFECTS = ((0, 1, 1), (1, 4, -1), (3, 6, 1), (2, 7, 1))


def required_directions(hierarchy):
    """Reconstruct valid height cuts, then prove the required directions."""
    model, counts = fourzero.build(2, hierarchy, 0)
    selector = SAT(model.n, model.clauses)
    patterns = []
    while selector.check() == 1:
        values = selector.model(model.n)
        pattern = {
            key: 1 if values[model.trits[key][0]-1] > 0 else
            -1 if values[model.trits[key][1]-1] > 0 else 0
            for key in fourzero.components}
        patterns.append(pattern)
        selector.add(sum((model.deny(key, value) for key, value in pattern.items()), []))
    macro = dict(zip(A, (0, 0, 0, 1))) | dict(zip(B, (0, 1, 1, 0)))
    maps = [(permutation, reflection)
            for permutation, reflection in product(fourzero.phase, (-1, 1))
            if fourzero.rank_tuple([reflection*macro[permutation[i]] for i in A])
            == (0, 0, 0, 1)]
    proofs = []
    for pattern in patterns:
        for permutation, reflection in maps:
            proof = fourzero.lemma(2, pattern, permutation, reflection)
            if proof is None:
                continue
            model.clauses.append(
                sum((model.deny(key, value) for key, value in pattern.items()), [])
                + [proof['sign']*abs(chambers.lit(proof['quad']))])
            proofs.append({'pattern': pattern, 'height_certificate': proof})
    # Negate: ax <= 0, ay <= 0, b=+E, c=-E, d=+E.
    failed = [model.trits['ax'][0], model.trits['ay'][0]]
    expected = {'bx': 1, 'by': 0, 'cx': -1, 'cy': 0, 'dx': 1, 'dy': 0}
    failed += sum((model.deny(key, value) for key, value in expected.items()), [])
    model.clauses.append(failed)
    assert SAT(model.n, model.clauses).check() == -1
    return model.n, model.clauses, dict(counts), proofs


def nonedge_formula(hierarchy):
    """Retain 01 and the newly normalized nonedge 04 at every scale."""
    assert hierarchy in (-1, 0, 1)
    model = DirectionalModel.__new__(DirectionalModel)
    model.n, original, *_ = chambers.base_formula()
    assert original[0] == [1]
    model.clauses = [list(row) for row in original[1:]]
    model.trits = {}
    ax, ay, ex, ey = s.symbols('ax ay ex ey')
    variables = (ax, ay, ex, ey)

    def entry(expression):
        expression = s.expand(expression)
        if not expression:
            return 0
        if not expression.free_symbols:
            return int(s.sign(expression))
        coefficient = s.Poly(expression, *variables).terms()[0][1]
        direction = 1 if coefficient > 0 else -1
        canonical = s.expand(expression/coefficient)
        key = str(canonical)
        if key not in model.trits:
            model.trits[key] = model.n+1, model.n+2
            model.n += 2
            model.clauses.append([-model.n+1, -model.n])
        return key, direction

    def exclude(expression, value):
        atom = entry(expression)
        if isinstance(atom, int):
            if atom == value:
                model.clauses.append([])
            return
        model.clauses.append(model.deny(atom[0], value*atom[1]))

    def fixed(expression, value):
        for other in (-1, 0, 1):
            if other != value:
                exclude(expression, other)

    def sum_law(left, right, total):
        assert s.expand(left+right-total) == 0
        entries = [entry(expression) for expression in (left, right, total)]
        keys = sorted({atom[0] for atom in entries if isinstance(atom, tuple)})
        for values in product((-1, 0, 1), repeat=len(keys)):
            environment = dict(zip(keys, values))
            signs = [environment[atom[0]]*atom[1] if isinstance(atom, tuple) else atom
                     for atom in entries]
            if not allowed_sum(*signs):
                model.clauses.append(sum((model.deny(key, value)
                                          for key, value in environment.items()), []))

    aa, ee = s.Matrix([ax, ay]), s.Matrix([ex, ey])
    bb = -aa if hierarchy < 0 else ee if hierarchy > 0 else ee-aa
    vectors = [s.Matrix([1, 0]), s.Matrix([0, 1]), aa, ee, bb, s.Matrix([1, -1])]
    pairs = {(i, j): entry(fourzero.det(vectors[i], vectors[j]))
             for i, j in combinations(range(len(vectors)), 2)}
    model.rank_two_axioms(len(vectors), pairs)
    for vector in (aa, ee):
        model.clauses.append(sum((list(model.trits[entry(value)[0]]) for value in vector), []))
    exclude(ax, 1)
    exclude(ay, 1)
    exclude(ex+ey, -1)
    sum_law(ex, ey, ex+ey)
    fixed(bb[0], 1)
    fixed(bb[1], 0)
    if hierarchy == 0:
        for vector in vectors:
            sum_law(fourzero.det(aa, vector), fourzero.det(bb, vector),
                    fourzero.det(ee, vector))
        sum_law(ax, bb[0], ex)
        sum_law(ay, bb[1], ey)

    epsilon, kappa, zeta, eta, small, partner = s.symbols(
        'epsilon kappa zeta eta small partner')
    points = {
        0: s.Matrix([0, 0, 0]), 1: s.Matrix([epsilon*ax, epsilon*ay, 0]),
        4: s.Matrix([kappa*ex, kappa*ey, 0]), 5: s.Matrix([1, 0, 0]),
        2: s.Matrix([0, 0, 1]), 3: s.Matrix([0, 1, 1]),
        6: s.Matrix([-zeta, 1, 1]), 7: s.Matrix([-eta, 0, 1]),
    }
    allowed = set(model.trits)
    counts = Counter()
    for index, quad in enumerate(chambers.Q, 1):
        first, *rest = quad
        polynomial = s.expand(s.Matrix.hstack(
            *(points[i]-points[first] for i in rest)).det())
        vertices = set(quad)
        for scale, pair in ((epsilon, {0, 1}), (kappa, {0, 4}),
                            (zeta, {3, 6}), (eta, {2, 7})):
            if pair <= vertices:
                polynomial = s.cancel(polynomial/scale)
        cluster = int({1, 4} <= vertices and 0 not in vertices)
        polynomial = s.cancel(polynomial.subs({
            epsilon: small*int(hierarchy <= 0), kappa: small*int(hierarchy >= 0),
            zeta: partner, eta: partner})/small**cluster)
        assert polynomial.is_polynomial(small, partner, *variables), (quad, polynomial)
        leading = s.expand(polynomial.subs({small: 0, partner: 0}))
        atom = entry(leading)
        assert not isinstance(atom, tuple) or atom[0] in allowed, (quad, leading)
        if atom == 0:
            counts['zero'] += 1
        elif isinstance(atom, int):
            model.clauses.append([index*atom])
            counts['constant'] += 1
        else:
            model.bracket_link(index, *atom)
            counts['direction'] += 1
    assert SAT(model.n, model.clauses).check() == -1
    return model.n, model.clauses, dict(counts)


def exact_checks():
    """Audit the all-t family, corner necessity, and exact quadratic jet."""
    _, _, edges, xb, yb, kx, ky = load_data()
    a, cc, dd, t = s.symbols('a c d t')
    r, u, z = a, HALF-cc, dd
    old_p = (0, r, 0, u, HALF, r, HALF, z)
    old_x = (0, -r, 0, -u, 0, r-HALF, 0, z-HALF)
    g2, slope = r-s.Rational(1, 8), HALF-2*r
    old_g = (0, r/2, g2, g2+slope*u, r-s.Rational(1, 4), r/2,
             g2+slope/2, g2+slope*z)
    permutation = (1, 0, 7, 6, 5, 4, 3, 2)
    symmetry = next(row for row in chambers.marked_symmetries()
                    if tuple(row['permutation']) == permutation)
    assert symmetry['phase_preserving'] and symmetry['matrix'] == ((-1, 0), (0, -1))
    gauge = symmetry['gauge']
    fx = [s.expand(-old_x[permutation[i]]-xb[permutation[i]]
                   -gauge[i][0]-HALF*gauge[i][1]
                   +old_x[permutation[0]]+xb[permutation[0]]-xb[i]) for i in range(8)]
    fg = [s.expand(old_g[permutation[0]]-old_g[permutation[i]]) for i in range(8)]
    assert all(-yb[permutation[i]]-gauge[i][1]+yb[permutation[0]]-yb[i] == 0
               for i in range(8))
    source = [s.Matrix([-old_p[permutation[i]]+old_p[permutation[0]],
                         -int(i in B)*HALF+t*(old_g[permutation[i]]-old_g[permutation[0]])])
              for i in range(8)]
    target = [s.Matrix([fx[i], -HALF+t*fg[i]]) for i in (2, 3)]
    rotation = (s.Matrix.hstack(*target)*s.Matrix.hstack(source[2], source[3]).inv()).applyfunc(s.cancel)
    denominator = 4+t*(4*a-1)**2
    expected_rotation = s.Matrix([[4-t*(4*a-1)**2, 4*(4*a-1)],
                                  [-4*t*(4*a-1), 4-t*(4*a-1)**2]])/denominator
    assert all(s.cancel(value) == 0 for value in rotation-expected_rotation)
    metric = s.diag(1, 1/t)
    assert all(s.cancel(value) == 0 for value in rotation.T*metric*rotation-metric)
    rotated = [(rotation*point).applyfunc(s.cancel) for point in source]
    fu = [s.factor(point[0]) for point in rotated]
    fh = [s.factor((rotated[i][1]+int(i in B)*HALF)/t) for i in range(8)]
    assert fu[0] == fh[0] == fu[4] == fh[4] == 0

    x = [s.Integer(0)] + list(s.symbols('x1:8'))
    g = [s.Integer(0)] + list(s.symbols('g1:8'))
    U, H, Z = {0: s.Integer(0), 2: x[2], 3: x[3]}, {0: s.Integer(0), 2: g[2], 3: g[3]}, {0: 0, 2: 0, 3: 0}
    for i in FREE:
        U[i], H[i], Z[i] = s.symbols(f'U{i} H{i} Z{i}')
    X = lambda i, j: x[j]-x[i]+kx[i, j]
    family = dict(zip(x, fx)) | dict(zip(g, fg)) | {
        U[i]: fu[i] for i in FREE} | {H[i]: fh[i] for i in FREE} | {Z[i]: 0 for i in FREE}
    equations = []
    for i, j in edges:
        ell = int(j in B)-int(i in B)
        du, dz, dh, dg = U[j]-U[i], Z[j]-Z[i], H[j]-H[i], g[j]-g[i]
        expression = s.expand(du**2+dz**2-X(i, j)**2-ell*dh-2*ky[i, j]*dg+t*(dh**2-dg**2))
        assert s.cancel(expression.subs(family)) == 0, (i, j)
        equations.append(expression)
    expected_defects = [8*a*a*t*(4*a-1)/denominator]*2 + [s.Integer(0)]*2
    for (i, j, direction), expected in zip(DEFECTS, expected_defects):
        weight = X(i, j) if (i, j) == (2, 7) else -X(i, j)
        reference_weight = s.expand(weight.subs(family))
        expected_weight = a if (i, j) in ((0, 1), (1, 4)) else cc if (i, j) == (3, 6) else dd
        assert reference_weight == expected_weight
        defect = weight-direction*(U[j]-U[i])
        assert s.cancel(defect.subs(family)-expected) == 0
        # Relative bounds extend smoothly even when an individual weight
        # tends to zero faster than the other three parameters.
        for expression in (H[j]-H[i], g[j]-g[i], defect):
            ratio = s.cancel(expression.subs(family)/reference_weight)
            assert s.denom(ratio).subs({a: 0, cc: 0, dd: 0, t: 0}) != 0
        dg, dh, du, dz = g[j]-g[i], H[j]-H[i], U[j]-U[i], Z[j]-Z[i]
        assert ky[i, j] == 0
        removed = du**2+dz**2-weight**2+t*(dh**2-dg**2)
        assert s.expand(defect*(2*weight-defect)-dz**2-t*(dh-dg)*(dh+dg)+removed) == 0

    variables = x[1:]+g[1:]+[U[i] for i in FREE]+[H[i] for i in FREE]
    dependent = [value for value in variables if value not in (x[1], x[6], x[7])]
    parameters = {x[1]: -a, x[6]: x[3]+HALF-cc, x[7]: x[2]-HALF+dd}
    metric_edges = [edge for edge in edges if edge not in ((0, 2), (0, 3), (2, 3))]
    regular = [equations[edges.index(edge)] for edge in metric_edges]
    for i, j, direction in DEFECTS:
        weight = X(i, j) if (i, j) == (2, 7) else -X(i, j)
        regular[metric_edges.index((i, j))] = weight-direction*(U[j]-U[i])
    regular = [s.expand(expression.subs(parameters)) for expression in regular]
    corner = {key: s.sympify(value).subs({a: 0, cc: 0, dd: 0, t: 0})
              for key, value in family.items()}
    jacobian = s.Matrix(regular).jacobian(dependent).subs(corner).subs({a: 0, cc: 0, dd: 0, t: 0})
    assert jacobian.shape == (21, 21) and jacobian.det() == 2048
    inverse = jacobian.inv()
    collapsed = {(i, j) for i, j, _ in DEFECTS}
    mode = {Z[i]: int(i == 5) for i in FREE}
    forcing = s.Matrix([0 if edge in collapsed else (Z[edge[1]]-Z[edge[0]])**2
                        for edge in metric_edges]).subs(mode)
    response = -inverse*forcing
    for expression, expected in ((U[4], -HALF), (H[4], -s.Rational(1, 4)),
                                 (g[4], -s.Rational(1, 4)), (-X(1, 4), HALF)):
        gradient = s.Matrix([expression.subs(parameters)]).jacobian(dependent)
        assert s.expand((gradient*response)[0]-expected) == 0

    # Force the intrinsic and height corner data independently of the family.
    _, _, _, intrinsic = fourzero.calc((0, 1, 1, 0))
    assert tuple(corner[key] for key in x[1:]+g[1:]) == intrinsic
    cross = [expression for edge, expression in zip(edges, equations)
             if (edge[0] in B) != (edge[1] in B)]
    without_heights = {key: value for key, value in corner.items()
                       if key not in {H[i] for i in FREE}}
    matrix, rhs = s.linear_eq_to_matrix(
        [s.expand(expression.subs(without_heights).subs(t, 0)) for expression in cross],
        [H[i] for i in FREE])
    assert matrix.rank() == 5 and not matrix.free_symbols
    assert all(s.expand(value) == 0 for value in matrix*s.Matrix([corner[H[i]] for i in FREE])-rhs)
    print('PASS exact all-t planar family, relative bounds, and necessary corner ranks 14/5')
    print('PASS determinant 2048 and nonedge04 normal-square response (-1/2,-1/4)')


def main():
    if len(sys.argv) > 2:
        raise SystemExit(__doc__)
    output = Path(sys.argv[1]) if len(sys.argv) == 2 else None
    if output:
        output.mkdir(parents=True, exist_ok=True)
    n, clauses, *_ = chambers.base_formula()
    models = chambers.enumerate_models(n, clauses, chambers.marked_symmetries())
    _, zeros = two_line.check(models)
    cells = fourzero.order_cover(zeros)[2]
    assert len(cells) == 32
    fourzero.relative_identities()
    records = []
    for hierarchy in (-1, 0, 1):
        variables, necessary, counts, proofs = required_directions(hierarchy)
        name = f'fourzero_split_directions_{hierarchy:+d}'.replace('+', 'p').replace('-', 'm')
        records.append({'name': name, 'hierarchy': hierarchy, 'height_certificates': proofs,
                        'counts': counts, 'variables': variables, 'clauses': len(necessary)})
        if output:
            chambers.write_cnf(output/(name+'.cnf'), variables, necessary)
        print(f'PASS {name}: UNSAT, {len(proofs)} exact height implications', flush=True)
    exact_checks()
    for hierarchy in (-1, 0, 1):
        variables, necessary, counts = nonedge_formula(hierarchy)
        name = f'fourzero_split_nonedge04_{hierarchy:+d}'.replace('+', 'p').replace('-', 'm')
        records.append({'name': name, 'hierarchy': hierarchy, 'counts': counts,
                        'variables': variables, 'clauses': len(necessary)})
        if output:
            chambers.write_cnf(output/(name+'.cnf'), variables, necessary)
        print(f'PASS {name}: UNSAT, all zero boundaries retained', flush=True)
    if output:
        (output/'fourzero_split_cells.json').write_text(json.dumps(cells, indent=2)+'\n')
        (output/'fourzero_split_proofs.json').write_text(json.dumps(records, indent=2)+'\n')
        blocked = clauses+[[-(i+1)*value for i, value in enumerate(model)] for model in models]
        chambers.write_cnf(output/'fourzero_split_model_coverage.cnf', n, blocked)
    print('PASS 32 four-zero triple/split orders; together with the separate 48-order proof, all 80')
    print('Scope: unbounded-sequence blow-up exclusion; no explicit height or full marking exclusion')


if __name__ == '__main__':
    if not __debug__:
        raise RuntimeError('run with assertions enabled')
    main()
