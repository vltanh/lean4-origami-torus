#!/usr/bin/env python3
"""Exclude the complete interior ray-2 C1 EA and EC order orbits.

Exact positive linear identities close the normal-sign relaxation.  The
producer verifies each identity from the original normal and independently
normalized 23 determinants; every exported CNF requires independent RUP.
No floating-point optimization or solver arithmetic is trusted here.
"""

import argparse
from functools import lru_cache
import json
from pathlib import Path
import time

import sympy as S

import remaining_c1_single_zero_scalar as scalar
from solver_chambers import write_cnf
from solver_sat import FastSAT

A, B, K, R = scalar.positive.PARAMETERS
HALF = S.Rational(1, 2)
VIRTUAL_Y = S.Symbol('virtual_y')


@lru_cache(maxsize=None)
def factor_sign(expression):
    """Strict rational sign, using checked multilinear factor signs."""
    expression = S.factor(expression)
    if expression == 0:
        return 0
    numerator, denominator = S.fraction(expression)
    result = 1
    for polynomial in (numerator, denominator):
        constant, factors = S.factor_list(polynomial)
        result *= int(S.sign(constant))
        for factor, exponent in factors:
            try:
                sign = scalar.positive.coefficient_sign(factor)
            except AssertionError:
                return None
            if sign is None:
                return None
            result *= sign**exponent
    return result


def scalar_families():
    families = {}
    for order, k in (('EA', K), ('EC', HALF)):
        p = (HALF-(1-A)*k)/A
        for epsilon, r, suffix in ((-1, B/2, 'opposite'),
                                  (1, S.Integer(0), 'same_left'),
                                  (1, R, 'same_interior'),
                                  (1, HALF, 'same_right')):
            weights = [HALF-k, HALF, 0, HALF, HALF-r, r, HALF, k]
            points = [S.Integer(0), S.Integer(0), p, p, p+epsilon*HALF,
                      B*p+(1-B)*(k-HALF)+epsilon*r, k-HALF, k]
            assert S.cancel(sum(weights)-S.Rational(5, 2)) == 0
            assert S.cancel(A*p-HALF+(1-A)*k) == 0
            assert S.cancel(points[5]-B*points[3]-(1-B)*points[6]-epsilon*r) == 0
            assert S.expand((HALF-r-(1-B)/2)*(epsilon-1)) == 0
            horizontal = scalar.positive.metric.horizontal_displacements(weights)
            residuals = S.Matrix([(points[j]-points[i])**2-horizontal[i, j]**2
                                  for i, j in scalar.positive.source_metric.EDGES]+[0]*5)
            stresses = scalar.positive.source_metric.closed_c1_rows().subs(
                {scalar.positive.source_metric.A: A/2,
                 scalar.positive.source_metric.B: -B/2})
            assert all(S.cancel(value) == 0 for value in stresses*residuals)
            families[order+'_'+suffix] = {'order': order, 'epsilon': epsilon,
                                         'k': k, 'r': r, 'weights': weights,
                                         'points': points}
    assert len(families) == 8
    return families


def forced_zero_indices(family):
    # NORMAL_VERTICES=(2,4,5,6,7).  EC additionally forces N6=0.
    return (0, 3) if family['order'] == 'EC' else (0,)


def virtual_model(family, horizontal, substitution=None):
    """Necessary source with one independently normalized edge 32."""
    assert horizontal in (-1, 0, 1)
    substitution = substitution or {}
    model = scalar.NormalModel(family)
    x, macro_rows, _ = scalar.geometry(family)
    for index in forced_zero_indices(family):
        model.clauses.extend([[-bit] for bit in model.normal_bits[index]])
    normal_indices = (1, 2, 4) if family['order'] == 'EC' else (1, 2, 3, 4)
    variables = tuple(scalar.NORMALS[i] for i in normal_indices)+(VIRTUAL_Y,)
    virtual_bits = model.new_trit()
    bits = tuple(model.normal_bits[i] for i in normal_indices)+(virtual_bits,)
    if horizontal == 0:
        model.clauses.append(list(virtual_bits))

    rows = {}
    for quad, row in zip(scalar.QUADS, macro_rows):
        reduced = tuple(row[i].subs(substitution, simultaneous=True)
                        for i in normal_indices)+(S.Integer(0),)
        rows[quad, False] = reduced

    levels = (0, A, 1, 1, 1, B, 0, 0)
    normals = dict(zip(scalar.NORMAL_VERTICES, scalar.NORMALS))
    for index in forced_zero_indices(family):
        normals[scalar.NORMAL_VERTICES[index]] = S.Integer(0)
    points = [S.Matrix([x[i], normals.get(i, 0), levels[i]]) for i in range(8)]
    edge, t, axial = S.symbols('edge t axial')
    points[2] = points[3]+edge*S.Matrix([horizontal, VIRTUAL_Y, t*axial])
    for quad in scalar.QUADS:
        if not {2, 3} <= set(quad):
            continue
        divided = S.cancel(S.det(S.Matrix.hstack(*(points[i]-points[quad[0]]
                                                  for i in quad[1:])))/edge)
        assert edge not in divided.free_symbols
        limit = S.expand(divided.subs(t, 0))
        assert S.cancel(divided-limit).subs(t, 0) == 0
        row = tuple(limit.coeff(variable) for variable in variables)
        assert S.expand(limit-sum(value*variable for value, variable in zip(row, variables))) == 0
        rows[quad, True] = tuple(value.subs(substitution, simultaneous=True) for value in row)
    assert len(rows) == 85

    omitted = 0
    for (quad, virtual), row in rows.items():
        signs = tuple(factor_sign(value) for value in row)
        if None in signs:
            omitted += 1
            continue
        if virtual:
            actual = model.new_trit()
            literal = scalar.shared.common.lit(quad)
            model.clauses.extend(([-actual[0], literal], [-actual[1], -literal]))
        else:
            actual = model.trits[quad]
        model.sumzero([actual[::-1]]+[
            pair if sign > 0 else pair[::-1]
            for pair, sign in zip(bits, signs) if sign])
    model.eaec_record = {'variables': list(map(str, variables)),
                         'parameter_substitution': {str(key): str(value) for key, value in substitution.items()},
                         'omitted_coefficient_sign_rows': omitted}
    return model, rows, variables, bits


def positive_identities(family, horizontal, substitution):
    """Fixed symbolic certificates discovered separately from this checker."""
    if horizontal != -family['epsilon']:
        return []
    if family['epsilon'] == 1 and family['r'] != 0:
        k, r = family['k'], family['r']
        shared_rows = (((0, 1, 2, 7), False, -1),
                       ((2, 4, 5, 7), False, 1),
                       ((1, 2, 3, 5), True, 1),
                       ((2, 3, 4, 5), True, 1))
        shared_weights = ((1-A)/(1-2*(1-A)*k), (1-A)/(1-B),
                          1/(1-B), (A*(1-B)+2*r*(1-A))/(1-B)**2)
        identities = [(shared_rows, shared_weights)]
        if family['order'] == 'EC':
            identities.insert(0, (
                (((0, 1, 2, 7), False, -1),
                 ((1, 2, 3, 5), True, 1),
                 ((2, 3, 4, 7), True, 1),
                 ((2, 3, 5, 7), True, 1)),
                ((1-A)/A, 1/(1-B), S.Integer(1), (1-A)/(1-B))))
        return identities
    if family['order'] == 'EC' and family['epsilon'] == -1 and substitution == {A: A*B}:
        return [(
            (((0, 2, 5, 7), False, -1),
             ((2, 4, 5, 7), False, 1),
             ((1, 2, 3, 5), True, 1),
             ((2, 3, 4, 5), True, 1)),
            ((1-A)/A, B*(1-A)/(A*(1-B)),
             1/(A*(1-B)), (B-A)/(A*(1-B)**2)))]
    return []


def add_positive_identities(model, rows, variables, bits, family, horizontal, substitution):
    records = []
    for signed_rows, weights in positive_identities(family, horizontal, substitution):
        weights = tuple(S.factor(value.subs(substitution, simultaneous=True)) for value in weights)
        assert all(factor_sign(value) == 1 for value in weights)
        total = [S.Integer(0)]*len(variables)
        for (quad, virtual, sign), weight in zip(signed_rows, weights):
            for column, value in enumerate(rows[quad, virtual]):
                total[column] += sign*weight*value
        target = variables.index(scalar.NORMALS[1])
        assert all(S.cancel(value+(1 if column == target else 0)) == 0
                   for column, value in enumerate(total))
        # If each signed generic bracket holds, its signed limiting form
        # is nonnegative.  Their positive sum equals -N4.  It is therefore
        # incompatible with the independently represented premise N4>0.
        required = sorted({sign*scalar.shared.common.lit(quad) for quad, _, sign in signed_rows})
        clause = [-literal for literal in required]+[-bits[target][0]]
        model.clauses.append(clause)
        records.append({'target': 'n4>0', 'sum_equals': '-n4',
                        'signed_rows': [{'quad': quad, 'virtual_32': virtual, 'sign': sign,
                                         'coefficients': list(map(str, rows[quad, virtual]))}
                                        for quad, virtual, sign in signed_rows],
                        'strictly_positive_weights': list(map(str, weights)), 'clause': clause})
    return records


def build(directory):
    started = time.monotonic()
    directory.mkdir(parents=True, exist_ok=True)
    relative_checks = scalar.short_edges.relative_metric_checks()
    families = scalar_families()
    obligations, records = [], []

    def export(model, filename, clauses=None, **metadata):
        clauses = model.clauses if clauses is None else clauses
        with FastSAT(model.n, clauses) as solver:
            assert solver.check() == -1, (filename, metadata)
        write_cnf(directory/filename, model.n, clauses)
        obligations.append({'file': filename, 'variables': model.n,
                            'clauses': len(clauses), **metadata})

    for name, family in families.items():
        macro = scalar.NormalModel(family)
        direct = name in ('EA_opposite', 'EA_same_left')
        if direct:
            export(macro, f'c1_eaec_{name}_macro.cnf', family=name, claim='macro exclusion')
        else:
            forced = forced_zero_indices(family)
            nonzero = [bit for index in forced for bit in macro.normal_bits[index]]
            export(macro, f'c1_eaec_{name}_forced_zero.cnf', macro.clauses+[nonzero],
                   family=name, claim='forced macro zeros',
                   zero_normals=[str(scalar.NORMALS[index]) for index in forced])
            for horizontal in (-1, 0, 1):
                cells = [('all', {})]
                if name == 'EC_opposite' and horizontal == 1:
                    cells = [('height_lt', {A: A*B}), ('height_eq', {A: B}),
                             ('height_gt', {A: B+(1-B)*A})]
                for cell, substitution in cells:
                    model, rows, variables, bits = virtual_model(family, horizontal, substitution)
                    identities = add_positive_identities(model, rows, variables, bits,
                                                          family, horizontal, substitution)
                    export(model, f'c1_eaec_{name}_virtual_{horizontal}_{cell}.cnf',
                           family=name, virtual_horizontal=horizontal, parameter_cell=cell,
                           positive_linear_identities=identities, **model.eaec_record)
        records.append({'family': name, 'order': family['order'], 'epsilon': family['epsilon'],
                        'weights': list(map(str, family['weights'])),
                        'points': list(map(str, family['points'])),
                        'direct_normal_exclusion': direct, 'excluded': True})
    assert len(obligations) == 28
    packet = {'domain': 'ray2 C1; interior heights; complete EA and EC order orbits',
              'relative_short_edge_source_checks': relative_checks,
              'scalar_families': records,
              'source_checks_per_family': {'closed_projected_stresses': 12,
                                           'macro_determinants': 70, 'projected_relations': 560},
              'source_checks_per_virtual_case': {'independent_edge_determinants': 15},
              'height_cell_cover': {'lt': 'alpha=beta*u, 0<u<1', 'eq': 'alpha=beta',
                                    'gt': 'alpha=beta+(1-beta)*u, 0<u<1'},
              'unsat_obligations': obligations, 'remaining_families': [],
              'relative_rate_assumptions': [], 'seconds': time.monotonic()-started}
    (directory/'c1_ea_ec_scalar.json').write_text(json.dumps(packet, indent=2)+'\n')
    return packet


if __name__ == '__main__':
    if not __debug__:
        raise RuntimeError('run with assertions enabled')
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('output', type=Path)
    result = build(parser.parse_args().output)
    print(json.dumps({'scalar_families': len(result['scalar_families']),
                      'unsat_obligations': len(result['unsat_obligations']),
                      'remaining_families': result['remaining_families'],
                      'seconds': result['seconds']}))
