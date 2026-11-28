#!/usr/bin/env python3
"""Exclude the h1=0 and h7=0 common-line endpoints of interior ray-1 C0.

Relative short-edge control and a nontrivial normal stretch leave two
virtual-direction cases. Both require independently replayed CNFs.
"""

import argparse
import json
from pathlib import Path
import time

import sympy as s

import remaining_c0_short_edges as short_edges
import solver_remaining_c0_flat_stretch as stretch
from solver_chambers import write_cnf
from solver_sat import FastSAT


def endpoint_model():
    return stretch.NormalModel('endpoint_ba', s.Integer(1))


def virtual_model(horizontal):
    assert horizontal in (0, -1)
    model = endpoint_model()
    for vertex in (2, 6):
        model.clauses.extend([[-bit] for bit in model.normal_bits[vertex]])
    normals = {i: s.Symbol('n'+str(i)) for i in (3, 4, 5)}
    Y, epsilon = s.symbols('Y epsilon')
    direction_normal = model.new_trit()
    if horizontal == 0:
        model.clauses.append(list(direction_normal))
    _, x, levels = stretch.coordinates('endpoint_ba')
    points = [s.Matrix((s.expand(x[i].subs(stretch.T, 1)),
                        normals.get(i, 0), levels[i])) for i in range(8)]
    points[2] = points[1]+epsilon*s.Matrix((horizontal, Y, 0))
    variables = {**{normals[i]: model.normal_bits[i] for i in normals},
                 Y: direction_normal}
    count = 0
    for quad in stretch.QUADS:
        if not {1, 2} <= set(quad):
            continue
        determinant = s.det(s.Matrix.hstack(*(points[i]-points[quad[0]]
                                              for i in quad[1:])))
        expression = s.expand(determinant/epsilon)
        assert not expression.has(epsilon)
        coefficients = tuple(expression.coeff(variable) for variable in variables)
        assert s.expand(expression-sum(coefficient*variable
                        for coefficient, variable in zip(coefficients, variables))) == 0
        signs = tuple(stretch.coefficient_sign(value) for value in coefficients)
        assert None not in signs
        normalized = model.new_trit()
        generic = stretch.shared.common.lit(quad)
        model.clauses.extend(([-normalized[0], generic], [-normalized[1], -generic]))
        model.sumzero([normalized[::-1]]+[
            pair if sign > 0 else pair[::-1]
            for pair, sign in zip(variables.values(), signs) if sign])
        count += 1
    assert count == 15
    return model


def build(directory):
    started = time.monotonic()
    directory.mkdir(parents=True, exist_ok=True)
    checks = short_edges.exact_checks()
    assert stretch.source_check('endpoint_ba') == 12
    obligations = []

    def export(name, model, clauses, claim):
        with FastSAT(model.n, clauses) as solver:
            assert solver.check() == -1, name
        write_cnf(directory/name, model.n, clauses)
        obligations.append({'file': name, 'variables': model.n,
                            'clauses': len(clauses), 'claim': claim})

    model = endpoint_model()
    violation = list(model.normal_bits[2])+list(model.normal_bits[6])
    export('c0_line_endpoint_normal_zeros.cnf', model, model.clauses+[violation],
           'the nontrivial normal stretch has N2=N6=0')
    for horizontal in (0, -1):
        model = virtual_model(horizontal)
        name = 'pure_normal' if horizontal == 0 else 'negative_horizontal'
        export(f'c0_line_endpoint_virtual12_{name}.cnf', model, model.clauses,
               f'normalized short direction ({horizontal},Y,0) is impossible')
    result = {'checks': checks, 'normal_source_family': 'endpoint_ba, right endpoint',
              'divided_determinants_per_case': 15, 'unsat_obligations': obligations,
              'excluded': 'common-line h1=0 and reflected h7=0; interior ray1 C0',
              'relative_rate_assumptions': [],
              'remaining_common_line_families': 'four middle families and two diagonal line directions',
              'whole_flat_C0_excluded': False, 'seconds': time.monotonic()-started}
    (directory/'c0_line_endpoints.json').write_text(json.dumps(result, indent=2)+'\n')
    return result


if __name__ == '__main__':
    if not __debug__:
        raise RuntimeError('run with assertions enabled')
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('output', type=Path)
    result = build(parser.parse_args().output)
    print(json.dumps({'unsat_obligations': len(result['unsat_obligations']),
                      'excluded': result['excluded'], 'seconds': result['seconds']}))
