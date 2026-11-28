#!/usr/bin/env python3
"""Exact auxiliary elimination on all six bounded-axis limit components.

Usage: python solver_remaining_limit.py OUTPUT_JSON

The 24 metric equations and five universal q syzygies form a 29-by-14
linear system in H1,...,H7,w and all six q scales. No q is discarded.
Polynomial row-combination certificates survive zero parameters. Feasible
pivot-zero loci are separately reduced, including interior exceptional
lines, to retain the extra equations at rank drops.
"""

import argparse
from functools import lru_cache
from itertools import combinations
import json
from math import gcd, lcm
from pathlib import Path
import time

import sympy as sym
from sympy.polys.matrices import DomainMatrix

import exhaustive_remaining_axis as axis
import exhaustive_remaining_locus as locus

A, B = locus.A, locus.B
PARAMETERS = (A, B)
H = (sym.Integer(0),)+sym.symbols('H1:8')
W = sym.Symbol('w')
QS = sym.symbols('q05 q14 q24 q25 q47 q57')
AUXILIARIES = H[1:]+(W,)+QS
QMAP = dict(zip(axis.PRODUCT_EDGES, QS))
SHIFTS, FACES, EDGES = axis.case_data(1)


def original_system(values):
    """Constant terms are T_ij=|Pj-Pi|²-Xij² on the first 24 rows."""
    v = locus.vertex_values(values)
    intrinsic, spatial = axis.baselines(v)
    rows = []
    for i, j in EDGES:
        dz = spatial[j]-spatial[i]
        vertical = intrinsic[j]-intrinsic[i]+SHIFTS[i, j][1]
        rows.append(QMAP.get((i, j), 0)+2*dz*(H[j]-H[i])
                    -2*vertical*W*(int(j == 6)-int(i == 6)))
    rows.extend(locus.q_syzygies(v, QMAP))
    matrix, zero = sym.linear_eq_to_matrix(rows, AUXILIARIES)
    assert matrix.shape == (29, 14) and not any(zero)
    return matrix


def affine_key(expressions):
    if not expressions:
        return ()
    matrix, rhs = sym.linear_eq_to_matrix(expressions, PARAMETERS)
    reduced, pivots = matrix.row_join(rhs).rref()
    if 2 in pivots:
        return None
    return tuple(tuple(row) for row in reduced.tolist() if any(row))


def equations(key):
    return [row[0]*A+row[1]*B-row[2] for row in key]


def parameterization(key):
    substitution = {A: A, B: B}
    pivots = []
    for row in key:
        pivot = next(i for i in range(2) if row[i])
        assert row[pivot] == 1
        pivots.append(pivot)
        substitution[PARAMETERS[pivot]] = row[2]-sum(row[j]*PARAMETERS[j]
                                                     for j in range(pivot+1, 2))
    free = tuple(PARAMETERS[i] for i in range(2) if i not in pivots)
    return substitution, free


def feasible_domain(key, facets):
    """Exact intersection of a closed bounded polygon with an affine plane."""
    if key is None:
        return None
    substitution, free = parameterization(key)
    cuts = [sym.expand(sym.sympify(cut).subs(substitution, simultaneous=True)) for cut in facets]
    if any(cut < 0 for cut in cuts if not cut.free_symbols):
        return None
    if not free:
        vertices = [tuple(substitution[variable] for variable in PARAMETERS)]
    elif len(free) == 1:
        variable = free[0]
        lower = upper = None
        for cut in cuts:
            coefficient = cut.coeff(variable)
            constant = cut.subs(variable, 0)
            assert not coefficient.free_symbols and not constant.free_symbols
            if coefficient > 0:
                bound = -constant/coefficient
                lower = bound if lower is None else max(lower, bound)
            elif coefficient < 0:
                bound = -constant/coefficient
                upper = bound if upper is None else min(upper, bound)
        assert lower is not None and upper is not None
        if lower > upper:
            return None
        if lower == upper:
            return feasible_domain(affine_key(equations(key)+[variable-lower]), facets)
        vertices = [tuple(value.subs(variable, bound) for value in substitution.values())
                    for bound in (lower, upper)]
    else:
        vertices = locus.polygon_vertices(cuts)
        assert len(vertices) >= 3  # Every root component is two-dimensional.
    return {'key': key, 'substitution': substitution, 'free': free, 'vertices': vertices}


def primitive_vector(vector):
    """Clear every denominator, then divide a common polynomial factor."""
    values = [sym.cancel(value) for value in vector]
    denominator = sym.lcm([sym.fraction(value)[1] for value in values])
    values = [sym.cancel(denominator*value) for value in values]
    common = sym.gcd_list([value for value in values if value])
    values = [sym.cancel(value/common) for value in values]
    polynomials = [sym.Poly(value, A, B, domain=sym.QQ) for value in values]
    scale = lcm(*(int(coefficient.q) for poly in polynomials for coefficient in poly.coeffs()))
    values = [sym.expand(scale*value) for value in values]
    integer_gcd = gcd(*(int(coefficient) for value in values
                        for coefficient in sym.Poly(value, A, B).coeffs()))
    values = [sym.expand(value/integer_gcd) for value in values]
    first = next(value for value in values if value)
    if sym.Poly(first, A, B).LC() < 0:
        values = [-value for value in values]
    return values


def nullspace_rows(matrix):
    result = DomainMatrix.from_Matrix(matrix).to_field().nullspace().to_Matrix()
    if not result.rows:
        return sym.zeros(0, matrix.cols)
    return sym.Matrix([primitive_vector(result[row, :]) for row in range(result.rows)])


def matrix_witness(matrix):
    _, columns = DomainMatrix.from_Matrix(matrix).to_field().rref()
    _, rows = DomainMatrix.from_Matrix(matrix.T).to_field().rref()
    assert len(rows) == len(columns)
    determinant = sym.factor(matrix[list(rows), list(columns)].det()) if rows else sym.Integer(1)
    assert determinant != 0
    return {'rows': list(rows), 'columns': list(columns), 'determinant': determinant}


def nonzero_factors(expressions):
    factors = set()
    for expression in expressions:
        for factor, _ in sym.factor_list(expression, A, B)[1]:
            # Preserve the zero locus: remove only rational content here.
            poly = sym.Poly(factor, A, B, domain=sym.QQ)
            _, primitive = poly.clear_denoms(convert=True)
            primitive = primitive.primitive()[1]
            if primitive.LC() < 0:
                primitive = -primitive
            factors.add(primitive.as_expr())
    return sorted(factors, key=str)


@lru_cache(maxsize=1)
def closed_c0_rows():
    """A sparse uniform basis suggested by the projected circle identities."""
    u, v = 1-A, -B
    lu, lv = 1-2*u, 1-2*v
    symbols = sym.symbols('T0:24')
    T = dict(zip(EDGES, symbols))
    expressions = [T[edge] for edge in ((0, 6), (0, 7), (1, 2), (1, 3), (2, 3), (6, 7))]
    expressions += [T[0, 1]-T[0, 2]-T[1, 7]+T[2, 7],
                    2*u*T[3, 4]+lu*T[4, 6]-2*u*lu*T[3, 6],
                    2*v*T[3, 5]+lv*T[5, 6]-2*v*lv*T[3, 6],
                    T[4, 5]-2*u*T[3, 5]-lu*T[5, 6]-2*v*T[3, 4]-lv*T[4, 6]
                    +(2*u*lv+2*v*lu)*T[3, 6],
                    lv*(T[2, 4]-T[3, 4])-lu*(T[2, 5]-T[3, 5]),
                    v*(T[4, 7]-T[4, 6])-u*(T[5, 7]-T[5, 6])]
    rows = []
    for index, expression in enumerate(expressions):
        row = [sym.diff(expression, variable) for variable in symbols]+[sym.Integer(0)]*5
        if index == 10:
            row[25] = -1
        elif index == 11:
            row[28] = sym.Rational(1, 2)
        rows.append(primitive_vector(row))
    result = sym.Matrix(rows)
    original = original_system(locus.components()[0]['values'])
    assert result.shape == (12, 29)
    assert all(sym.expand(value) == 0 for value in result*original)
    return result


@lru_cache(maxsize=1)
def closed_c1_rows():
    """Uniform C1 rows; the exceptional q24 factor vanishes only at one corner."""
    symbols = sym.symbols('T0:24')
    T = dict(zip(EDGES, symbols))
    v = 2*B+1
    expressions = [T[edge] for edge in ((0, 6), (0, 7), (2, 3), (3, 4), (6, 7))]
    expressions += [(2*A-1)*(T[0, 1]-2*A*T[0, 2])-2*A*T[1, 2],
                    (2*A-1)*(T[0, 1]-2*A*T[0, 3])-2*A*T[1, 3],
                    T[0, 1]-2*A*T[0, 2]-T[1, 7]+2*A*T[2, 7],
                    T[3, 5]-v*T[3, 6]-T[4, 5]+v*T[4, 6],
                    2*B*T[3, 5]-2*B*v*T[3, 6]-v*T[5, 6],
                    (1-A+B)*T[2, 4],
                    T[5, 7]-T[5, 6]+2*B*(T[4, 7]-T[4, 6])]
    rows = []
    for index, expression in enumerate(expressions):
        row = [sym.diff(expression, variable) for variable in symbols]+[sym.Integer(0)]*5
        if index == 10:
            row[24], row[25] = 1, -sym.Rational(1, 2)
        elif index == 11:
            row[28] = -1
        rows.append(primitive_vector(row))
    result = sym.Matrix(rows)
    original = original_system(locus.components()[1]['values'])
    assert result.shape == (12, 29)
    assert all(sym.expand(value) == 0 for value in result*original)
    return result


def reduce_stratum(component, domain):
    substitution = domain['substitution']
    values = [sym.sympify(value).subs(substitution, simultaneous=True) for value in component['values']]
    matrix = original_system(values)
    matrix_rank = matrix_witness(matrix)
    right = nullspace_rows(matrix)
    right_rank = matrix_witness(right)
    assert len(matrix_rank['rows'])+right.rows == 14
    assert all(sym.expand(value) == 0 for value in matrix*right.T)
    syzygies = matrix[24:, 8:]
    syzygy_rank = matrix_witness(syzygies)
    syzygy_right = nullspace_rows(syzygies)
    syzygy_right_rank = matrix_witness(syzygy_right)
    assert len(syzygy_rank['rows'])+syzygy_right.rows == 6
    assert all(sym.expand(value) == 0 for value in syzygies*syzygy_right.T)
    preferred = {0: closed_c0_rows, 1: closed_c1_rows}
    left = (preferred[component['id']]().subs(substitution, simultaneous=True)
            if component['id'] in preferred else nullspace_rows(matrix.T))
    _, chosen = DomainMatrix.from_Matrix(left[:, :24].T).to_field().rref()
    certificates = left[list(chosen), :] if chosen else sym.zeros(0, 29)
    assert all(sym.expand(value) == 0 for value in certificates*matrix)
    stress_rank = matrix_witness(certificates[:, :24])
    expected = 24-len(matrix_rank['rows'])+len(syzygy_rank['rows'])
    assert certificates.rows == expected == len(stress_rank['rows'])
    witnesses = {'auxiliary_rank': matrix_rank, 'auxiliary_nullspace_rank': right_rank,
                 'syzygy_rank': syzygy_rank, 'syzygy_nullspace_rank': syzygy_right_rank,
                 'stress_rank': stress_rank}
    factors = nonzero_factors([value['determinant'] for value in witnesses.values()])
    assert all(sym.Poly(value, A, B).total_degree() == 1 for value in factors)
    return {'component': component['id'],
            'equations': list(map(str, equations(domain['key']))),
            'values': list(map(str, values)), 'dimension': len(domain['free']),
            'vertices': [[str(value) for value in point] for point in domain['vertices']],
            'auxiliary_rank': len(matrix_rank['rows']), 'syzygy_rank': len(syzygy_rank['rows']),
            'stress_count': certificates.rows,
            'witnesses': {name: dict(value, determinant=str(value['determinant']))
                          for name, value in witnesses.items()},
            'auxiliary_right_nullspace': [[str(value) for value in right[row, :]] for row in range(right.rows)],
            'syzygy_right_nullspace': [[str(value) for value in syzygy_right[row, :]]
                                      for row in range(syzygy_right.rows)],
            'certificates': [[str(value) for value in certificates[row, :]]
                             for row in range(certificates.rows)],
            'nonzero_conditions': list(map(str, factors))}, factors


def compile_component(component):
    facets = component['facets']
    pending = [()]
    pending += [affine_key([cut]) for cut in facets]
    pending += [affine_key(pair) for pair in combinations(facets, 2)]
    known, records, links = {}, [], []
    while pending:
        domain = feasible_domain(pending.pop(0), facets)
        if domain is None or domain['key'] in known:
            continue
        index = len(records)
        known[domain['key']] = index
        record, factors = reduce_stratum(component, domain)
        records.append(record)
        children = []
        for factor in factors:
            child = feasible_domain(affine_key(equations(domain['key'])+[factor]), facets)
            if child is not None:
                assert len(child['free']) < len(domain['free'])
                pending.append(child['key'])
                children.append((str(factor), child['key']))
        links.append(children)
    for record, children in zip(records, links):
        record['zero_condition_children'] = [{'factor': factor, 'stratum': known[key]}
                                              for factor, key in children]
    return records


def full_record():
    universal = original_system(locus.VARIABLES)
    x = (sym.Integer(0),)+sym.symbols('x1:8')
    constants = {}
    for mark in (1, 2):
        shifts, _, edges = axis.case_data(mark)
        assert edges == EDGES and all(shifts[edge][1] == SHIFTS[edge][1] for edge in EDGES)
        constants[str(mark)] = [str(sym.Symbol(f'D{i}{j}')-(x[j]-x[i]+shifts[i, j][0]
                                                       +sym.Rational(shifts[i, j][1], 2))**2)
                                for i, j in EDGES]+['0']*5
    return {'auxiliaries': list(map(str, AUXILIARIES)), 'vertical_variables': list(map(str, locus.VARIABLES)),
            'edges': EDGES, 'matrix': [[str(value) for value in universal[row, :]] for row in range(29)],
            'constant_terms': constants,
            'components': [{'id': component['id'], 'values': list(map(str, component['values'])),
                            'facets': list(map(str, component['facets'])),
                            'strata': compile_component(component)} for component in locus.components()]}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('output', type=Path)
    args = parser.parse_args()
    start = time.monotonic()
    result = full_record()
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, separators=(',', ':'))+'\n')
    for component in result['components']:
        strata = component['strata']
        print(json.dumps({'component': component['id'], 'strata': len(strata),
                          'generic_auxiliary_rank': strata[0]['auxiliary_rank'],
                          'generic_stresses': strata[0]['stress_count'],
                          'boundary_rank_range': [min(row['auxiliary_rank'] for row in strata),
                                                  max(row['auxiliary_rank'] for row in strata)],
                          'projected_stress_range': [min(row['stress_count'] for row in strata),
                                                     max(row['stress_count'] for row in strata)]}), flush=True)
    print(f'Generated exact denominator-cleared certificates in {time.monotonic()-start:.3f}s')
    print('Identities are necessary everywhere; linear-equation equivalence requires the recorded nonzero conditions.')


if __name__ == '__main__':
    if not __debug__:
        raise RuntimeError('run with assertions enabled')
    main()
