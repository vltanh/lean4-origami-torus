#!/usr/bin/env python3
"""Project regular C0 endpoint-cap topology onto 18 planar angle chambers.

Usage: python exhaustive_c0_angles.py OUTPUT_DIRECTORY

Assumes noncollinear endpoint triangles123 and067, and0<u,v<1/2.
Actual anchor minors remain weak; the signs belong to a generic
completion. Outputs three UNSAT coverage/sign formulas for independent replay.
This does not assert metric infeasibility of any angular chamber.
"""

import argparse
from itertools import combinations
import json
from pathlib import Path

import solver_remaining_chambers as common
from solver_sat import FastSAT
from solver_chambers import write_cnf

PAIRS = tuple(combinations(range(2, 8), 2))
ANCHORS = tuple(common.common.lit((0, 1)+pair) for pair in PAIRS)
EXPECTED = {
    '+-------------+', '+------------++', '+----------+-++',
    '+--------+----+', '+--------+-+--+', '+--------+-+-++',
    '+--+-+-+-+-++-+', '+--+-+-+++--+-+', '+--+-+-+++-++-+',
    '+-+------+----+', '+-+------+-+--+', '+-+--+-+++--+-+',
    '+-++-+-+++--+-+', '+-++-+-+++-++-+', '++------------+',
    '++-----------++', '+++-----------+', '+++------+----+',
}
EXTRA_SIGNS = (((0, 1, 2, 7), -1), ((0, 1, 3, 5), -1),
               ((0, 1, 4, 6), -1), ((0, 2, 3, 4), 1),
               ((1, 5, 6, 7), -1), ((3, 4, 5, 6), -1))


def cap_units(lower_orientation):
    assert lower_orientation in (-1, 1)
    units = []
    for triangle, sign in (((1, 2, 3), -1), ((0, 6, 7), lower_orientation)):
        for vertex in range(8):
            if vertex not in triangle:
                units.append([sign*common.common.lit(triangle+(vertex,))])
    return units


def verify_closed_boundary_counterexample():
    """Replay an exact degenerate family with T36<0 in every weak chamber.

    This is a witness for the closed limiting metric relaxation, not an
    embedding or a counterexample to the regular-cap research target.
    """
    import sympy as sym
    import solver_remaining_limit as reduction

    a = sym.Symbol('a')
    half = sym.Rational(1, 2)
    h = [half, half, half-a, half, half, half, half, a]
    x = [0, -half, 0, a-half, a-1, a, a-half, a]
    p = [0, 0, half, a, half, 0, half-a, -a]
    values = [half, half, half, sym.Rational(3, 4), -sym.Rational(1, 4), 0]
    intrinsic = reduction.locus.vertex_values(values)
    shifts, faces, edges = reduction.axis.case_data(1)

    def horizontal(i, j):
        return sym.expand(x[j]-x[i]+shifts[i, j][0]+sym.Rational(shifts[i, j][1], 2))

    def vertical(i, j):
        return sym.expand(intrinsic[j]-intrinsic[i]+shifts[i, j][1])

    assert sym.expand(sum(h)-sym.Rational(7, 2)) == 0
    assert all(sym.expand(horizontal(i, (i+1) % 8)+h[i]) == 0 for i in range(8))
    for i, j in edges:
        # Affine functions attain their extrema at the two endpoints.
        for endpoint in (0, half):
            assert abs(horizontal(i, j).subs(a, endpoint)) <= half
        assert abs(vertical(i, j)) <= half
    for i, j, k in faces:
        area = sym.expand(horizontal(i, j)*vertical(i, k)-horizontal(i, k)*vertical(i, j))
        assert sym.degree(area, a) <= 1
        assert all(area.subs(a, endpoint) >= 0 for endpoint in (0, half))
        assert area.subs(a, sym.Rational(1, 4)) > 0

    residuals = sym.Matrix([sym.expand((p[j]-p[i])**2-horizontal(i, j)**2)
                           for i, j in edges])
    rows = reduction.closed_c0_rows()[:, :24].subs(
        {reduction.A: sym.Rational(3, 4), reduction.B: -sym.Rational(1, 4)})
    assert all(sym.expand(value) == 0 for value in rows*residuals)
    auxiliaries = sym.Matrix([
        sym.Rational(1, 4), -sym.Rational(1, 4), -(4*a-1)/4,
        (8*a*a-12*a+1)/4, (8*a*a-4*a+1)/4,
        (4*a-3)*(4*a-1)/8, a, (16*a*a-8*a-1)/8,
        (4*a-1)/8, a*(4*a-5)/2, (2*a-1)*(4*a-1)/4,
        (2*a-1)*(4*a-1)/4, -(4*a-1)**2/8, -(4*a-1)**2/8,
    ])
    full_residuals = reduction.original_system(values)*auxiliaries+residuals.col_join(sym.zeros(5, 1))
    assert all(sym.expand(value) == 0 for value in full_residuals)
    assert sym.factor(residuals[edges.index((3, 6))]) == 2*a*(2*a-1)
    assert all(p[i]*0-0*p[j] == 0 for i, j in PAIRS)
    return {'parameter': '0<a<1/2', 'u': '1/4', 'v': '1/4',
            'h': list(map(str, h)), 'collinear_P': list(map(str, p)),
            'T36': '2*a*(2*a-1)', 'all_anchor_cross_products': 0,
            'both_cap_areas': 0, 'full_limit_metric_rows_checked': 29,
            'actual_embedding_claimed': False}


def verify_regular_angular_counterexample():
    """The anchor projection is insufficient even with two regular caps."""
    import sympy as sym
    import solver_remaining_limit as reduction

    q = sym.Rational
    X, Y, R, Z, L = q(41, 100), 3*sym.sqrt(5)/25, q(43, 200), sym.sqrt(14)/20, q(1, 10)
    p = [(0, 0), (0, 0), (X, -Y), (L, 0), (R, -Z), (-R, -Z), (-L, 0), (-X, -Y)]
    h = [q(89, 250), q(49, 100), q(41, 100), q(457, 1000),
         q(43, 100), q(457, 1000), q(41, 100), q(49, 100)]
    x = [0, -h[0], 1-sum(h[:2]), 1-sum(h[:3]), 1-sum(h[:4]),
         q(5, 2)-sum(h[:5]), q(5, 2)-sum(h[:6]), q(7, 2)-sum(h[:7])]
    values = [q(1, 2), q(1, 2), q(1, 2), q(3, 4), -q(1, 4), 0]
    intrinsic = reduction.locus.vertex_values(values)
    shifts, faces, edges = reduction.axis.case_data(1)

    def horizontal(i, j):
        return x[j]-x[i]+shifts[i, j][0]+q(shifts[i, j][1], 2)

    def vertical(i, j):
        return intrinsic[j]-intrinsic[i]+shifts[i, j][1]

    assert sum(h) == q(7, 2) and all(0 < value < q(1, 2) for value in h)
    assert all(horizontal(i, (i+1) % 8) == -h[i] for i in range(8))
    assert all(abs(horizontal(i, j)) <= q(1, 2) and abs(vertical(i, j)) <= q(1, 2)
               for i, j in edges)
    assert all(horizontal(i, j)*vertical(i, k)-horizontal(i, k)*vertical(i, j) > 0
               for i, j, k in faces)
    residuals = sym.Matrix([sym.expand(sum((p[j][k]-p[i][k])**2 for k in range(2))
                                      -horizontal(i, j)**2) for i, j in edges])
    rows = reduction.closed_c0_rows()[:, :24].subs({reduction.A: q(3, 4), reduction.B: -q(1, 4)})
    assert all(sym.simplify(value) == 0 for value in rows*residuals)
    auxiliaries = sym.Matrix([
        q(7921, 62500), -q(3381, 15625), q(3471, 62500), -q(16607, 62500),
        q(18653, 62500), q(121, 5000), q(4289, 12500), -q(47, 1000),
        -q(103, 1000), -q(3, 20), -q(19, 125)+3*sym.sqrt(70)/250,
        -q(19, 125)+3*sym.sqrt(70)/250, -q(21, 200)+3*sym.sqrt(70)/250,
        -q(21, 200)+3*sym.sqrt(70)/250,
    ])
    assert all(sym.simplify(value) == 0 for value in
               reduction.original_system(values)*auxiliaries+residuals.col_join(sym.zeros(5, 1)))
    cross = {(i, j): sym.expand(p[i][0]*p[j][1]-p[i][1]*p[j][0]) for i, j in PAIRS}
    # The only difference of positive radicals reduces to this rational comparison.
    assert sym.expand((X*Z)**2-(R*Y)**2) > 0
    assert all(cross[pair] <= 0 for pair in PAIRS if pair not in ((2, 3), (6, 7)))
    assert cross[2, 3] == cross[6, 7] == 3*sym.sqrt(5)/250
    assert cross[3, 6] == 0
    assert residuals[edges.index((3, 6))] == -q(1224, 15625)
    levels = [0, q(1, 2), q(1, 2), q(1, 2), q(1, 4), q(1, 4), 0, 0]
    points = [sym.Matrix([*point, level]) for point, level in zip(p, levels)]
    bracket = sym.simplify(sym.Matrix.hstack(*(points[i]-points[3] for i in (4, 5, 6))).det())
    assert bracket == 43*sym.sqrt(14)/4000 and bracket > 0
    return {'u': '1/4', 'v': '1/4', 'h': list(map(str, h)),
            'P': [[str(value) for value in point] for point in p],
            'weak_anchor_pattern': '+-------------+', 'zero_anchor_pairs': [[3, 6]],
            'both_cap_areas': '3*sqrt(5)/250', 'T36': '-1224/15625',
            'violated_necessary_bracket': '[3456]<=0', 'bracket3456': str(bracket),
            'full_limit_metric_rows_checked': 29, 'actual_embedding_claimed': False}


def verify_extra_sign_geometry():
    """Exact planar forms of the three signs outside the anchor projection."""
    import sympy as sym

    u, v = sym.symbols('u v')
    p = [sym.zeros(2, 1), sym.zeros(2, 1)]
    p.extend(sym.Matrix(sym.symbols(f'p{i}x p{i}y')) for i in range(2, 8))
    levels = [0, sym.Rational(1, 2), sym.Rational(1, 2), sym.Rational(1, 2), u, v, 0, 0]
    points = [point.col_join(sym.Matrix([level])) for point, level in zip(p, levels)]

    def cross(a, b):
        return sym.det(sym.Matrix.hstack(a, b))

    def bracket(quad):
        i, *rest = quad
        return sym.det(sym.Matrix.hstack(*(points[j]-points[i] for j in rest)))

    q4 = p[4]-2*u*p[3]-(1-2*u)*p[6]
    q5 = p[5]-2*v*p[3]-(1-2*v)*p[6]
    assert sym.expand(2*bracket((0, 2, 3, 4))-cross(p[3]-p[2], (1-2*u)*p[6]+q4)) == 0
    assert sym.expand(2*bracket((1, 5, 6, 7))+cross(p[7]-p[6], 2*v*p[3]+q5)) == 0
    assert sym.expand(2*bracket((3, 4, 5, 6))+cross(q4, q5)) == 0


def build(directory):
    n, base, *_ = common.base_formula()
    negative = base+cap_units(-1)
    with FastSAT(n, negative) as solver:
        assert solver.check() == -1
    positive = base+cap_units(1)
    patterns = []
    with FastSAT(n, positive) as solver:
        while solver.check() == 1:
            model = solver.model()
            values = tuple(model[variable-1] for variable in ANCHORS)
            patterns.append(values)
            solver.add([-variable*value for variable, value in zip(ANCHORS, values)])
        assert solver.check() == -1
    words = {''.join('+' if value > 0 else '-' for value in row) for row in patterns}
    assert words == EXPECTED and len(patterns) == 18
    patterns.sort()
    models, full_models, witnessed_literals = [], [], set()
    with FastSAT(n, positive) as solver:
        while solver.check() == 1:
            values = tuple(solver.model())
            models.append(values)
            literals = {(i+1)*value for i, value in enumerate(values)}
            if literals-witnessed_literals:
                assignment = solver.model(n)
                assert tuple(assignment[:70]) == values
                assert all(any(assignment[abs(literal)-1]*(1 if literal > 0 else -1) > 0
                               for literal in clause) for clause in positive)
                full_models.append(assignment)
                witnessed_literals |= literals
            solver.add([-(i+1)*value for i, value in enumerate(values)])
        assert solver.check() == -1
    assert len(models) == 669
    common_literals = {(i+1)*models[0][i] for i in range(70)
                       if all(row[i] == models[0][i] for row in models)}
    cap_literals = {clause[0] for clause in cap_units(1)}
    extra_literals = [sign*common.common.lit(quad) for quad, sign in EXTRA_SIGNS]
    assert common_literals-cap_literals == set(extra_literals)
    # Checked SAT assignments prove that there are no further unanimous
    # signs. This needs no trust in an exhaustive model-count claim.
    variable_common = {abs(literal) for literal in common_literals}
    uncovered = {sign*i for i in range(1, 71) if i not in variable_common for sign in (-1, 1)}
    nonunanimity_witnesses = []
    while uncovered:
        witness = max(full_models, key=lambda row: len(uncovered & {
            (i+1)*value for i, value in enumerate(row[:70])}))
        covered = uncovered & {(i+1)*value for i, value in enumerate(witness[:70])}
        assert covered
        nonunanimity_witnesses.append(witness)
        uncovered -= covered
    coverage = positive+[[-variable*value for variable, value in zip(ANCHORS, row)]
                         for row in patterns]
    extra_coverage = positive+[[-literal for literal in extra_literals]]
    with FastSAT(n, extra_coverage) as solver:
        assert solver.check() == -1
    directory.mkdir(parents=True, exist_ok=True)
    write_cnf(directory/'c0_opposite_cap_orientation.cnf', n, negative)
    write_cnf(directory/'c0_anchor_coverage.cnf', n, coverage)
    write_cnf(directory/'c0_extra_signs.cnf', n, extra_coverage)
    verify_extra_sign_geometry()
    result = {'pairs': PAIRS, 'anchor_variables': ANCHORS,
              'patterns': [''.join('+' if value > 0 else '-' for value in row) for row in patterns],
              'cap_units': {'negative': cap_units(-1), 'positive': cap_units(1)},
              'assumptions': ['noncollinear projected123 and067', '0<u,v<1/2'],
              'actual_minor_semantics': 'weak signs of a generic completion',
              'extra_necessary_signs': [{'quad': quad, 'sign': sign} for quad, sign in EXTRA_SIGNS],
              'generic_cap_models': len(models), 'generic_cap_sign_models': models,
              'nonunanimity_full_boolean_witnesses': nonunanimity_witnesses,
              'closed_boundary_counterexample': verify_closed_boundary_counterexample(),
              'regular_angular_counterexample': verify_regular_angular_counterexample(),
              'metric_exclusion': False}
    (directory/'c0_anchor_chambers.json').write_text(json.dumps(result, indent=2)+'\n')
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('output', type=Path)
    args = parser.parse_args()
    result = build(args.output)
    print(json.dumps({'angular_chambers': len(result['patterns']),
                      'independent_coverage_formulas': 3,
                      'metric_exclusion': False}), flush=True)


if __name__ == '__main__':
    if not __debug__:
        raise RuntimeError('run with assertions enabled')
    main()
