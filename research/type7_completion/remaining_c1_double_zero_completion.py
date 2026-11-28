#!/usr/bin/env python3
"""Complete the interior ray-2 C1 EF and endpoint-EE scalar exclusions.

The adjacent JSON contains positive integer polynomial identities.  This
checker rebuilds every determinant and every positive basis product, then
checks all five coefficient columns exactly.  No numerical optimizer,
linear-programming result, or stored polynomial expression is trusted.
All eighty exported CNFs require independent RUP replay.
"""

import argparse
from functools import lru_cache
from itertools import product
import json
from pathlib import Path
import time

import sympy as S

import remaining_c1_double_zero_endpoints as endpoints
import remaining_c1_single_zero_scalar as scalar
from solver_chambers import write_cnf
from solver_sat import FastSAT

A, B, X, Y = scalar.positive.PARAMETERS
HALF = S.Rational(1, 2)
D2, D7 = S.symbols('d2 d7')
VARIABLES = (scalar.NORMALS[1], scalar.NORMALS[2], scalar.NORMALS[3], D2, D7)
PARAMETERS = (A, B, X, Y)
UNIT = {A: A, B: B, X: 2*X, Y: 2*Y}
DATA_FILE = Path(__file__).with_suffix('.json')


@lru_cache(maxsize=1)
def families():
    source = endpoints.families()
    result = {}
    for eta in (-1, 1):
        base = f'EF_eta{eta}_epsilon-1'
        for r, suffix in ((S.Integer(0), 'left'), (X, 'interior'), (HALF, 'right')):
            result[base+'_'+suffix] = {
                key: [value.subs(X, r) for value in source[base][key]]
                for key in ('points', 'weights')}
    for name in ('EF_eta1_epsilon1', 'EE_h00_epsilon-1'):
        result[name] = source[name]
    assert len(result) == 8
    # Bind each specialized stratum back to the original metric source.
    for family in result.values():
        points, weights = family['points'], family['weights']
        assert S.cancel(sum(weights)-S.Rational(5, 2)) == 0
        horizontal = scalar.positive.metric.horizontal_displacements(weights)
        residuals = S.Matrix([(points[j]-points[i])**2-horizontal[i, j]**2
                              for i, j in scalar.positive.source_metric.EDGES]+[0]*5)
        stresses = scalar.positive.source_metric.closed_c1_rows().subs(
            {scalar.positive.source_metric.A: A/2,
             scalar.positive.source_metric.B: -B/2})
        assert all(S.cancel(value) == 0 for value in stresses*residuals)
    return result


@lru_cache(maxsize=None)
def geometry(name):
    return scalar.geometry(families()[name])


def symmetry_checks():
    source = endpoints.families()
    marked = scalar.short_edges.symmetry_and_orbits()
    permutation = tuple((i+4) % 8 for i in range(8))
    assert any(tuple(row['permutation']) == permutation and row['mark'] == 2
               for row in marked['marked_symmetries'])
    epsilon = -1
    right, left = source['EE_h01/2_epsilon-1'], source['EE_h00_epsilon-1']
    points = right['points']
    levels = (0, A/2, HALF, HALF, HALF, B/2, 0, 0)
    slope = S.cancel((points[5]-points[4])/(levels[5]-levels[4]))
    assert S.cancel(slope+(1+A)/A) == 0
    transformed = [-epsilon*(points[permutation[i]]-points[4]
                             -slope*(levels[permutation[i]]-levels[4])) for i in range(8)]
    substitution = {A: 1-B, B: 1-A}
    for i in range(8):
        assert S.cancel(transformed[i]
                        -left['points'][i].subs(substitution, simultaneous=True)) == 0
        assert S.cancel(HALF-levels[permutation[i]]
                        -S.sympify(levels[i]).subs(substitution, simultaneous=True)) == 0
        assert S.cancel(right['weights'][permutation[i]]
                        -left['weights'][i].subs(substitution, simultaneous=True)) == 0
    return {'marked_cap_swap': permutation, 'height_map': ['1-beta', '1-alpha'],
            'EE_right_opposite_maps_to_left': True,
            'coordinate_weight_and_height_identities': 24}


def macro_nonzero_clause(model, name):
    if name.startswith('EF'):
        return list(model.normal_bits[0])+list(model.normal_bits[4])
    # In EE, equality N6=N7 follows from this actual determinant zero,
    # not merely from agreement of their two normal signs.
    _, rows, _ = geometry(name)
    assert rows[scalar.QUAD_INDEX[(0, 1, 6, 7)]] == (0, 0, 0, -A, A)
    return list(model.normal_bits[0])+list(model.trits[(0, 1, 6, 7)])


@lru_cache(maxsize=None)
def source_rows(name, horizontal23, horizontal_lower):
    assert horizontal23 in (-1, 0, 1) and horizontal_lower in (-1, 0, 1)
    x, macro, _ = geometry(name)
    ef = name.startswith('EF')
    rows = {}
    for quad, row in zip(scalar.QUADS, macro):
        reduced = (row[1], row[2], row[3]+(0 if ef else row[4]),
                   S.Integer(0), S.Integer(0))
        original = sum(coefficient*normal for coefficient, normal in zip(row, scalar.NORMALS))
        original = original.subs({scalar.NORMALS[0]: 0,
                                  scalar.NORMALS[4]: 0 if ef else scalar.NORMALS[3]})
        assert S.expand(original-sum(coefficient*normal
                                     for coefficient, normal in zip(reduced, VARIABLES))) == 0
        rows[quad, False] = reduced

    normal = (0, 0, 0, 0, VARIABLES[0], VARIABLES[1], VARIABLES[2],
              0 if ef else VARIABLES[2])
    levels = (0, A, 1, 1, 1, B, 0, 0)
    points = [S.Matrix([x[i], normal[i], levels[i]]) for i in range(8)]
    ep, eq, t, axial23, axial_lower = S.symbols('ep eq t axial23 axial_lower')
    lower = 0 if ef else 6
    points[2] = points[3]-ep*S.Matrix([horizontal23, D2, t*axial23])
    points[7] = points[lower]+eq*S.Matrix([horizontal_lower, D7, t*axial_lower])
    virtual_count = double_count = 0
    for quad in scalar.QUADS:
        upper = {2, 3} <= set(quad)
        bottom = {lower, 7} <= set(quad)
        if not (upper or bottom):
            continue
        determinant = S.expand(S.det(S.Matrix.hstack(*(points[i]-points[quad[0]]
                                                       for i in quad[1:]))))
        factor = (ep if upper else 1)*(eq if bottom else 1)
        divided = S.cancel(determinant/factor)
        # Polynomial divisibility checks both short edges before any limit.
        S.Poly(divided, ep, eq, t)
        assert S.expand(determinant-factor*divided) == 0
        without_axial = S.expand(divided.subs(t, 0))
        assert S.cancel(divided-without_axial).subs(t, 0) == 0
        limit = S.expand(without_axial.subs({ep: 0, eq: 0}))
        row = tuple(limit.coeff(variable) for variable in VARIABLES)
        assert S.expand(limit-sum(coefficient*variable
                                  for coefficient, variable in zip(row, VARIABLES))) == 0
        rows[quad, True] = row
        virtual_count += 1
        double_count += int(upper and bottom)
    assert virtual_count == 29 and double_count == 1 and len(rows) == 99
    return rows


def virtual_model(name, horizontal23, horizontal_lower):
    model = scalar.NormalModel(families()[name])
    for bit in model.normal_bits[0]:
        model.clauses.append([-bit])
    if name.startswith('EF'):
        for bit in model.normal_bits[4]:
            model.clauses.append([-bit])
    else:
        for bit in model.trits[(0, 1, 6, 7)]:
            model.clauses.append([-bit])
        model.sumzero((model.normal_bits[3], model.normal_bits[4][::-1]))
    virtual_bits = (model.new_trit(), model.new_trit())
    for horizontal, bits in zip((horizontal23, horizontal_lower), virtual_bits):
        if horizontal == 0:
            model.clauses.append(list(bits))
    bits = (model.normal_bits[1], model.normal_bits[2], model.normal_bits[3])+virtual_bits
    rows = source_rows(name, horizontal23, horizontal_lower)
    omitted = 0
    for (quad, virtual), row in rows.items():
        if not virtual:
            continue
        signs = tuple(scalar.positive.coefficient_sign(value) for value in row)
        if None in signs:
            omitted += 1
            continue
        actual = model.new_trit()
        literal = scalar.shared.common.lit(quad)
        model.clauses.extend(([-actual[0], literal], [-actual[1], -literal]))
        model.sumzero([actual[::-1]]+[
            pair if sign > 0 else pair[::-1]
            for pair, sign in zip(bits, signs) if sign])
    model.double_record = {'variables': list(map(str, VARIABLES)),
                           'virtual_determinants': 29, 'independently_double_divided': 1,
                           'omitted_virtual_coefficient_sign_rows': omitted}
    return model, rows


def read_certificates():
    data = json.loads(DATA_FILE.read_text())
    assert data['schema'] == 1
    cases = {}
    for case in data['cases']:
        key = case['family'], case['horizontal_23'], case['horizontal_lower']
        assert key not in cases and key[0] in families()
        assert key[1] in (-1, 0, 1) and key[2] in (-1, 0, 1)
        cases[key] = case['certificates']
    assert len(cases) == 13
    return cases


@lru_cache(maxsize=None)
def basis(parameters, degree, powers):
    assert len(parameters) == len(powers)
    assert all(type(power) is int and 0 <= power <= degree for power in powers)
    assert all(parameter in PARAMETERS for parameter in parameters)
    # Each factor is strictly positive on its original open parameter box.
    expression = S.prod(UNIT[parameter]**power*(1-UNIT[parameter])**(degree-power)
                        for parameter, power in zip(parameters, powers))
    return S.Poly(expression, *parameters, domain=S.QQ)


def add_certificate(model, rows, certificate):
    parameters = tuple(parameter for parameter in PARAMETERS
                       if any(value.has(parameter) for row in rows.values() for value in row))
    assert list(map(str, parameters)) == certificate['parameters']
    degree = certificate['degree']
    assert type(degree) is int and degree in (1, 2)
    vertex, target_sign = certificate['target_vertex'], certificate['target_sign']
    assert vertex in (4, 5, 6) and target_sign in (-1, 1)
    column = (4, 5, 6).index(vertex)
    total = [S.Poly(0, *parameters, domain=S.QQ) for _ in VARIABLES]
    target_polynomial = S.Poly(0, *parameters, domain=S.QQ)
    guards = {}
    assert certificate['row_terms'] and certificate['target_terms']
    for term in certificate['row_terms']:
        quad, virtual, sign = tuple(term['quad']), term['virtual'], term['sign']
        assert quad in scalar.QUAD_INDEX and type(virtual) is bool and sign in (-1, 1)
        row = rows[quad, virtual]
        assert any(value != 0 for value in row)
        coefficient = S.Integer(term['coefficient'])
        assert coefficient > 0
        positive_basis = basis(parameters, degree, tuple(term['powers']))
        if quad in guards:
            assert guards[quad] == sign
        guards[quad] = sign
        for i, value in enumerate(row):
            total[i] += positive_basis*S.Poly(value, *parameters, domain=S.QQ)*coefficient*sign
    for term in certificate['target_terms']:
        coefficient = S.Integer(term['coefficient'])
        assert coefficient > 0
        target_polynomial += coefficient*basis(parameters, degree+1, tuple(term['powers']))
    assert not target_polynomial.is_zero
    total[column] += target_sign*target_polynomial
    assert all(polynomial.is_zero for polynomial in total)
    required = sorted(sign*scalar.shared.common.lit(quad) for quad, sign in guards.items())
    normal_bits = model.normal_bits[scalar.NORMAL_VERTICES.index(vertex)]
    strict_normal = normal_bits[0 if target_sign > 0 else 1]
    clause = [-literal for literal in required]+[-strict_normal]
    model.clauses.append(clause)
    return {'target_vertex': vertex, 'target_sign': target_sign,
            'degree': degree, 'parameters': list(map(str, parameters)),
            'positive_target_polynomial': str(S.factor(target_polynomial.as_expr())),
            'row_terms': len(certificate['row_terms']),
            'positive_target_terms': len(certificate['target_terms']),
            'exact_zero_coefficient_columns': 5, 'clause': clause}


def build(directory):
    started = time.monotonic()
    directory.mkdir(parents=True, exist_ok=True)
    relative_checks = scalar.short_edges.relative_metric_checks()
    cap_swap = symmetry_checks()
    source = families()
    certificates = read_certificates()
    used, obligations, strata = set(), [], []
    identity_count = term_count = 0

    def export(model, filename, clauses=None, **metadata):
        clauses = model.clauses if clauses is None else clauses
        with FastSAT(model.n, clauses) as solver:
            assert solver.check() == -1, filename
        write_cnf(directory/filename, model.n, clauses)
        obligations.append({'file': filename, 'variables': model.n,
                            'clauses': len(clauses), **metadata})

    for name, family in source.items():
        macro = scalar.NormalModel(family)
        export(macro, f'c1_double_complete_{name}_macro_zero.cnf',
               macro.clauses+[macro_nonzero_clause(macro, name)], family=name,
               claim='N2=N7=0' if name.startswith('EF') else 'N2=0 and D0167=0, hence N6=N7')
        for horizontal23, horizontal_lower in product((-1, 0, 1), repeat=2):
            model, rows = virtual_model(name, horizontal23, horizontal_lower)
            key = name, horizontal23, horizontal_lower
            records = []
            for certificate in certificates.get(key, []):
                records.append(add_certificate(model, rows, certificate))
                identity_count += 1
                term_count += len(certificate['row_terms'])+len(certificate['target_terms'])
            if key in certificates:
                used.add(key)
            export(model, f'c1_double_complete_{name}_virtual_{horizontal23}_{horizontal_lower}.cnf',
                   family=name, horizontal_23=horizontal23, horizontal_lower=horizontal_lower,
                   positive_polynomial_identities=records, **model.double_record)
        strata.append({'family': name, 'weights': list(map(str, family['weights'])),
                       'points': list(map(str, family['points'])), 'excluded': True})
    assert used == set(certificates)
    assert len(obligations) == 80 and identity_count == 39 and term_count == 989
    packet = {'domain': 'ray2 C1; interior heights; remaining EF and endpoint EE scalar families',
              'scalar_strata': strata, 'relative_short_edge_checks': relative_checks,
              'cap_swap_checks': cap_swap,
              'source_checks_per_stratum': {'closed_projected_stresses': 12,
                                             'macro_determinants': 70, 'projected_relations': 560},
              'positive_polynomial_data': DATA_FILE.name,
              'positive_polynomial_identity_count': identity_count,
              'positive_integer_basis_terms': term_count,
              'unsat_obligations': obligations,
              'additional_symmetry_exclusion': 'EE_h01/2_epsilon-1',
              'earlier_endpoint_package': 'remaining_c1_double_zero_endpoints',
              'remaining_EF_or_EE_endpoint_families': [], 'relative_rate_assumptions': [],
              'seconds': time.monotonic()-started}
    (directory/'c1_double_zero_completion.json').write_text(json.dumps(packet, indent=2)+'\n')
    return packet


if __name__ == '__main__':
    if not __debug__:
        raise RuntimeError('run with assertions enabled')
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('output', type=Path)
    result = build(parser.parse_args().output)
    print(json.dumps({'scalar_strata': len(result['scalar_strata']),
                      'unsat_obligations': len(result['unsat_obligations']),
                      'positive_polynomial_identities': result['positive_polynomial_identity_count'],
                      'remaining_families': result['remaining_EF_or_EE_endpoint_families'],
                      'seconds': result['seconds']}))
