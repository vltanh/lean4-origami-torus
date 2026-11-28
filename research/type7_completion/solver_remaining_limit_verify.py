#!/usr/bin/env python3
"""Independent coefficient replay of the six-component limit reducer.

Usage: python solver_remaining_limit_verify.py OUTPUT_JSON

Rebuilds the original 29-by-14 matrix directly, checks every polynomial
row combination and rank witness, and checks every feasible pivot-zero
child by exact polygon intersection. No producer nullspace computation,
floating arithmetic, SAT solver, or nonlinear solver is used.
"""

import ast
from itertools import combinations
import json
from pathlib import Path
import sys

import sympy as sym

import exhaustive_remaining_axis as axis
import exhaustive_remaining_locus as locus

A, B = locus.A, locus.B
PARAMETERS = (A, B)
VERTICAL = locus.VARIABLES
X = (sym.Integer(0),)+sym.symbols('x1:8')
H = (sym.Integer(0),)+sym.symbols('H1:8')
W = sym.Symbol('w')
QS = sym.symbols('q05 q14 q24 q25 q47 q57')
AUXILIARIES = H[1:]+(W,)+QS
SHIFTS, FACES, EDGES = axis.case_data(1)
NAMES = {str(value): value for value in (A, B)+VERTICAL+X[1:]+AUXILIARIES}
NAMES.update({f'D{i}{j}': sym.Symbol(f'D{i}{j}') for i, j in EDGES})


def polynomial(text):
    """Small arithmetic-only parser; a proof file cannot execute Python."""
    def visit(node):
        if isinstance(node, ast.Constant) and isinstance(node.value, int) and not isinstance(node.value, bool):
            return sym.Integer(node.value)
        if isinstance(node, ast.Name):
            assert node.id in NAMES
            return NAMES[node.id]
        if isinstance(node, ast.UnaryOp) and isinstance(node.op, (ast.USub, ast.UAdd)):
            value = visit(node.operand)
            return -value if isinstance(node.op, ast.USub) else value
        assert isinstance(node, ast.BinOp)
        left, right = visit(node.left), visit(node.right)
        if isinstance(node.op, ast.Add):
            return left+right
        if isinstance(node.op, ast.Sub):
            return left-right
        if isinstance(node.op, ast.Mult):
            return left*right
        if isinstance(node.op, ast.Div):
            assert right.is_Rational and right != 0
            return left/right
        if isinstance(node.op, ast.Pow):
            assert right.is_Integer and 0 <= right <= 100
            return left**right
        raise AssertionError(ast.dump(node))
    value = sym.expand(visit(ast.parse(text, mode='eval').body))
    assert value.is_polynomial(*NAMES.values())
    return value


def matrix(rows, columns):
    assert all(len(row) == columns for row in rows)
    return sym.Matrix([[polynomial(value) for value in row] for row in rows]) if rows else sym.zeros(0, columns)


def original_matrix(values):
    v1, v2, v3, v4, v5, v7 = values
    v = [0, v1, v2, v3, v4, v5, v3-sym.Rational(1, 2), v7]
    z = list(v)
    z[4], z[5] = 2*v3-v4, 2*v3-v5-1
    result = sym.zeros(29, 14)
    q_indices = {edge: 8+i for i, edge in enumerate(axis.PRODUCT_EDGES)}
    for row, (i, j) in enumerate(EDGES):
        difference = z[j]-z[i]
        if j:
            result[row, j-1] += 2*difference
        if i:
            result[row, i-1] -= 2*difference
        vertical = v[j]-v[i]+SHIFTS[i, j][1]
        result[row, 7] = -2*vertical*(int(j == 6)-int(i == 6))
        if (i, j) in q_indices:
            result[row, q_indices[i, j]] = 1
    f, a, c, d, b, e = 2*v3-1, v1-v3, v2-v3, v3-v4, 2*v3-2*v5-1, 2*v3-2*v7-1
    result[24, 9], result[24, 10] = -c, a
    result[25, 10], result[25, 11] = 1-b, 2*d
    result[26, 8], result[26, 13] = -e, f
    result[27, 10], result[27, 11], result[27, 12], result[27, 13] = e, -e, 2*c, -2*c
    result[28, 12], result[28, 13] = -b, 2*d+1
    return result


def verify_limit_origin():
    """Check the exact finite-t identity before passing to bounded limits."""
    v = locus.vertex_values(VERTICAL)
    z = list(v)
    z[4], z[5] = 2*v[3]-v[4], 2*v[3]-v[5]-1
    t, distance, horizontal = sym.symbols('t distance horizontal')
    products = axis.product_polynomials(v)
    original = original_matrix(VERTICAL)
    for row, (i, j) in enumerate(EDGES):
        dz, dh = z[j]-z[i], H[j]-H[i]
        vertical = v[j]-v[i]+SHIFTS[i, j][1]
        dw = W*(int(j == 6)-int(i == 6))
        q = QS[axis.PRODUCT_EDGES.index((i, j))] if (i, j) in axis.PRODUCT_EDGES else 0
        physical = t*(distance-horizontal**2)+(dz+t*dh)**2-(vertical+t*dw)**2
        compact = t*(distance-horizontal**2+(original[row, :]*sym.Matrix(AUXILIARIES))[0]
                     +t*(dh**2-dw**2))
        assert sym.expand(physical-compact-products.get((i, j), 0)+t*q) == 0
    substitutions = {q: products[edge] for q, edge in zip(QS, axis.PRODUCT_EDGES)}
    for row in range(24, 29):
        identity = (original[row, :]*sym.Matrix(AUXILIARIES))[0]
        assert sym.expand(identity.subs(substitutions, simultaneous=True)) == 0


def intersection_vertices(root_vertices, equations):
    if not equations:
        return sorted(root_vertices)
    coefficients, rhs = sym.linear_eq_to_matrix(equations, PARAMETERS)
    augmented, pivots = coefficients.row_join(rhs).rref()
    assert 2 not in pivots
    rank = len(pivots)
    if rank == 2:
        point = (augmented[0, 2], augmented[1, 2])
        # The caller checks the polygon inequalities.
        return [point]
    assert rank == 1
    expression = augmented[0, 0]*A+augmented[0, 1]*B-augmented[0, 2]
    values = [expression.subs(dict(zip(PARAMETERS, point))) for point in root_vertices]
    points = {point for point, value in zip(root_vertices, values) if value == 0}
    for i, j in combinations(range(len(root_vertices)), 2):
        if values[i]*values[j] < 0:
            ratio = values[i]/(values[i]-values[j])
            points.add(tuple(sym.expand((1-ratio)*left+ratio*right)
                             for left, right in zip(root_vertices[i], root_vertices[j])))
    return [] if not points else sorted({min(points), max(points)})


def actual_domain(root_vertices, facets, equations):
    if equations:
        coefficients, rhs = sym.linear_eq_to_matrix(equations, PARAMETERS)
        _, pivots = coefficients.row_join(rhs).rref()
        if 2 in pivots:
            return []
    points = intersection_vertices(root_vertices, equations)
    return sorted(point for point in points if all(
        value.subs(dict(zip(PARAMETERS, point))) >= 0 for value in facets))


def check_witness(value, witness):
    rows, columns = witness['rows'], witness['columns']
    assert len(rows) == len(columns) and len(rows) == len(set(rows)) == len(set(columns))
    assert all(isinstance(i, int) and 0 <= i < value.rows for i in rows)
    assert all(isinstance(i, int) and 0 <= i < value.cols for i in columns)
    expected = value[rows, columns].det() if rows else sym.Integer(1)
    determinant = polynomial(witness['determinant'])
    assert determinant != 0 and sym.expand(expected-determinant) == 0
    return determinant


def conditions_cover_determinant(determinant, factors):
    remainder = sym.Poly(determinant, A, B, domain=sym.QQ)
    for factor in factors:
        divisor = sym.Poly(factor, A, B, domain=sym.QQ)
        while remainder.total_degree() >= divisor.total_degree():
            quotient, residue = remainder.div(divisor)
            if not residue.is_zero:
                break
            remainder = quotient
    assert remainder.total_degree() == 0 and not remainder.is_zero


def main(path):
    source = json.loads(path.read_text())
    assert source['auxiliaries'] == list(map(str, AUXILIARIES))
    assert source['vertical_variables'] == list(map(str, VERTICAL))
    assert source['edges'] == list(map(list, EDGES))
    universal = original_matrix(VERTICAL)
    assert all(sym.expand(value) == 0 for value in matrix(source['matrix'], 14)-universal)
    assert universal.shape == (29, 14)
    verify_limit_origin()
    for mark in (1, 2):
        shifts, _, edges = axis.case_data(mark)
        assert edges == EDGES
        assert all(shifts[edge][1] == SHIFTS[edge][1] for edge in EDGES)
        expected = [NAMES[f'D{i}{j}']-(X[j]-X[i]+shifts[i, j][0]
                                     +sym.Rational(shifts[i, j][1], 2))**2
                    for i, j in EDGES]+[sym.Integer(0)]*5
        assert all(sym.expand(polynomial(value)-rhs) == 0
                   for value, rhs in zip(source['constant_terms'][str(mark)], expected))
        assert len(source['constant_terms'][str(mark)]) == 29
    total = stresses = exceptional = 0
    assert len(source['components']) == 6
    for recorded, component in zip(source['components'], locus.components()):
        assert recorded['id'] == component['id']
        assert list(map(polynomial, recorded['values'])) == list(map(sym.sympify, component['values']))
        facets = list(map(polynomial, recorded['facets']))
        assert facets == list(component['facets'])
        root_vertices = locus.polygon_vertices(facets)
        strata = recorded['strata']
        assert strata and strata[0]['equations'] == [] and strata[0]['dimension'] == 2
        for index, row in enumerate(strata):
            restrictions = list(map(polynomial, row['equations']))
            points = actual_domain(root_vertices, facets, restrictions)
            claimed = sorted(tuple(map(polynomial, point)) for point in row['vertices'])
            assert points == claimed and points
            dimension = 0 if len(points) == 1 else 1 if restrictions else 2
            assert row['dimension'] == dimension
            solutions = sym.linsolve(restrictions, PARAMETERS) if restrictions else {(A, B)}
            solution = next(iter(solutions))
            substitution = dict(zip(PARAMETERS, solution))
            values = [sym.sympify(value).subs(substitution, simultaneous=True) for value in component['values']]
            assert len(row['values']) == 6
            assert all(sym.expand(value-polynomial(old)) == 0 for value, old in zip(values, row['values']))
            original = original_matrix(values)
            right = matrix(row['auxiliary_right_nullspace'], 14)
            assert all(sym.expand(value) == 0 for value in original*right.T)
            assert row['auxiliary_rank']+right.rows == 14
            syzygies = original[24:, 8:]
            syzygy_right = matrix(row['syzygy_right_nullspace'], 6)
            assert all(sym.expand(value) == 0 for value in syzygies*syzygy_right.T)
            assert row['syzygy_rank']+syzygy_right.rows == 6
            certificates = matrix(row['certificates'], 29)
            assert all(sym.expand(value) == 0 for value in certificates*original)
            assert certificates.rows == row['stress_count'] == 24-row['auxiliary_rank']+row['syzygy_rank']
            witnesses = row['witnesses']
            matrices = {'auxiliary_rank': original, 'auxiliary_nullspace_rank': right,
                        'syzygy_rank': syzygies, 'syzygy_nullspace_rank': syzygy_right,
                        'stress_rank': certificates[:, :24]}
            assert set(witnesses) == set(matrices)
            assert len(witnesses['auxiliary_rank']['rows']) == row['auxiliary_rank']
            assert len(witnesses['auxiliary_nullspace_rank']['rows']) == right.rows
            assert len(witnesses['syzygy_rank']['rows']) == row['syzygy_rank']
            assert len(witnesses['syzygy_nullspace_rank']['rows']) == syzygy_right.rows
            assert len(witnesses['stress_rank']['rows']) == certificates.rows
            determinants = [check_witness(value, witnesses[name]) for name, value in matrices.items()]
            factors = list(map(polynomial, row['nonzero_conditions']))
            assert len(factors) == len(set(factors))
            assert all(sym.Poly(value, A, B).total_degree() == 1 for value in factors)
            for determinant in determinants:
                conditions_cover_determinant(determinant, factors)
            children = {polynomial(child['factor']): child['stratum']
                        for child in row['zero_condition_children']}
            assert len(children) == len(row['zero_condition_children']) and set(children) <= set(factors)
            for factor in factors:
                zero_points = actual_domain(root_vertices, facets, restrictions+[factor])
                if not zero_points:
                    assert factor not in children
                    continue
                assert factor in children
                child_index = children[factor]
                assert isinstance(child_index, int) and 0 <= child_index < len(strata)
                child = strata[child_index]
                assert child['dimension'] < dimension
                assert sorted(tuple(map(polynomial, point)) for point in child['vertices']) == zero_points
            total += 1
            stresses += certificates.rows
            exceptional += certificates.rows == 11
    print('PASS original 29-by-14 system, all finite-t cancellation identities and five q syzygies', flush=True)
    print(f'PASS {total} parameter strata and {stresses} denominator-cleared projected identities for both markings', flush=True)
    print(f'PASS exact rank witnesses and complete feasible pivot-zero cover; {exceptional} corner records have 11 stresses', flush=True)
    print('These are necessary limit identities, not finite-height exclusions or realizability certificates.')


if __name__ == '__main__':
    if not __debug__:
        raise RuntimeError('run with assertions enabled')
    if len(sys.argv) != 2:
        raise SystemExit(__doc__)
    main(Path(sys.argv[1]))
