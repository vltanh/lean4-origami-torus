#!/usr/bin/env python3
"""Exclude all six remaining middle/diagonal common-line C0 limits.

Two independently normalized short diagonals, a relative cap-area
stretch, and the marked reflection cover every relative degeneration
rate. Every Boolean obligation requires independent RUP replay.
"""

import argparse
from functools import lru_cache
from itertools import product
import json
from pathlib import Path
import time

import sympy as s

import exhaustive_c0_collinear as boundary
import exhaustive_c0_double_coincidence as upper
import exhaustive_c0_double_flat as lower
import solver_remaining_c0_flat_stretch as stretch
from solver_chambers import write_cnf
from solver_sat import FastSAT


FAMILIES = stretch.FAMILIES[4:]
REFLECTION = {
    'middle_lt_positive': 'middle_lt_negative',
    'middle_lt_negative': 'middle_lt_positive',
    'middle_gt_positive': 'middle_gt_negative',
    'middle_gt_negative': 'middle_gt_positive',
    'diagonal_positive': 'diagonal_negative',
    'diagonal_negative': 'diagonal_positive',
}


def metric_checks():
    checks = {'upper_relative_source': upper.metric_checks(),
              'lower_relative_source': lower.relative_lower_checks(),
              'marked_reflection': boundary.symmetry_checks()}
    permutation = checks['marked_reflection']['permutation']
    weights = checks['marked_reflection']['weight_indices']
    for family in FAMILIES:
        assert stretch.source_check(family) == 12
        d, x, z = stretch.coordinates(family)
        dd, xx, zz = stretch.coordinates(REFLECTION[family])
        substitution = {stretch.A: 1-stretch.A}
        for i in range(8):
            assert s.expand(d[weights[i]]-dd[i].subs(substitution)) == 0
            assert s.expand(-x[permutation[i]]-xx[i].subs(substitution)) == 0
            assert s.expand(1-z[permutation[i]]-zz[i].subs(substitution)) == 0
        # h3 is strictly positive in every open middle/diagonal family.
        assert stretch.coefficient_sign(s.Rational(1, 2)-d[3]) == 1
        assert stretch.coefficient_sign(1-z[4]) == 1
        for j in (4, 5, 7):
            assert stretch.coefficient_sign(z[j]-1) == -1

    # The already source-bound upper tilt is A/2-a2=h3/(1-2u).
    # After Y3/(L*delta)->0 and P3/L->-e, these exact cross products
    # retain the small normal factor delta, independently of t and L.
    delta, length, x2, xj, nj, y3, a2, aa = s.symbols(
        'delta L x2 xj Nj Y3 a2 A')
    p2 = s.Matrix((x2, 0))
    p3 = length*s.Matrix((-1, delta*y3))
    pj = s.Matrix((xj, delta*nj))
    cross = lambda p, q: s.det(s.Matrix.hstack(p, q))
    expression = s.cancel((a2*cross(p3, pj)-length*aa*cross(p2, pj))
                          /(length*delta))
    assert s.expand(expression.subs({x2: -s.Rational(1, 2), y3: 0})
                    -(aa/2-a2)*nj) == 0
    checks.update({'families': len(FAMILIES), 'projected_stresses_per_family': 12,
                   'reflected_family_map': REFLECTION,
                   'relative_cross_product_factor': True,
                   'strict_tilt_coefficient': 'h3/(1-2u)>0'})
    return checks


@lru_cache(maxsize=None)
def divided_forms(family, horizontal3, horizontal6):
    assert horizontal3 in (-1, 0, 1) and horizontal6 in (-1, 0, 1)
    normals = {i: s.Symbol('n'+str(i)) for i in (4, 5, 7)}
    y3, y6, epsilon, eta = s.symbols('Y3 Y6 epsilon eta')
    variables = tuple(normals.values())+(y3, y6)
    _, x, levels = stretch.coordinates(family)
    points = [s.Matrix((x[i], normals.get(i, 0), levels[i])) for i in range(8)]
    points[3] = points[1]+epsilon*s.Matrix((horizontal3, y3, 0))
    points[6] = points[0]+eta*s.Matrix((horizontal6, y6, 0))
    rows = []
    for quad in stretch.QUADS:
        contains3 = {1, 3} <= set(quad)
        contains6 = {0, 6} <= set(quad)
        if not (contains3 or contains6):
            continue
        determinant = s.expand(s.Matrix.hstack(
            *(points[i]-points[quad[0]] for i in quad[1:])).det())
        factor = (epsilon if contains3 else 1)*(eta if contains6 else 1)
        divided = s.cancel(determinant/factor)
        # Factor the actual short columns BEFORE either is set to zero.
        # This polynomial check rules out a hidden ratio epsilon/eta.
        s.Poly(divided, epsilon, eta)
        assert s.expand(determinant-factor*divided) == 0
        expression = s.expand(divided.subs({epsilon: 0, eta: 0}))
        coefficients = tuple(expression.coeff(variable) for variable in variables)
        assert s.expand(expression-sum(coefficient*variable
                        for coefficient, variable in zip(coefficients, variables))) == 0
        signs = tuple(stretch.coefficient_sign(value) for value in coefficients)
        assert None not in signs
        rows.append((quad, signs))
    assert len(rows) == 29
    return tuple(rows)


def virtual_model(family, horizontal3, horizontal6):
    model = stretch.NormalModel(family)
    # The six independent normal-zero obligations below justify these.
    for vertex in (3, 6):
        model.clauses.extend([[-bit] for bit in model.normal_bits[vertex]])
    y3, y6 = model.new_trit(), model.new_trit()
    if horizontal3 == 0:
        model.clauses.append(list(y3))
    if horizontal6 == 0:
        model.clauses.append(list(y6))
    variables = tuple(model.normal_bits[i] for i in (4, 5, 7))+(y3, y6)
    for quad, signs in divided_forms(family, horizontal3, horizontal6):
        normalized = model.new_trit()
        generic = stretch.shared.common.lit(quad)
        model.clauses.extend(([-normalized[0], generic], [-normalized[1], -generic]))
        model.sumzero([normalized[::-1]]+[
            pair if sign > 0 else pair[::-1]
            for pair, sign in zip(variables, signs) if sign])
    model.upper_virtual_normal = y3
    model.lower_virtual_normal = y6
    return model


def tilted_model(family, infinite):
    model = virtual_model(family, -1, -1)
    model.clauses.extend([[-bit] for bit in model.upper_virtual_normal])
    beta = model.new_trit()
    model.clauses.append([-beta[1]])  # B/(t*L*delta*kappa) >= 0.
    for vertex in (4, 5, 7):
        generic = stretch.shared.common.lit((1, 2, 3, vertex))
        if infinite:
            model.clauses.append([-generic])
        else:
            normalized = model.new_trit()
            model.clauses.extend(([-normalized[0], generic], [-normalized[1], -generic]))
            # The limit is (z_vertex-1/2)*beta + N_vertex.
            # Every coefficient z_vertex-1/2 is strictly negative.
            model.sumzero((normalized[::-1], beta[::-1], model.normal_bits[vertex]))
    return model


def build(directory):
    started = time.monotonic()
    directory.mkdir(parents=True, exist_ok=True)
    checks = metric_checks()
    obligations = []

    def export(name, model, clauses, claim):
        with FastSAT(model.n, clauses) as solver:
            assert solver.check() == -1, name
        write_cnf(directory/name, model.n, clauses)
        obligations.append({'file': name, 'variables': model.n,
                            'clauses': len(clauses), 'claim': claim})

    for family in FAMILIES:
        model = stretch.NormalModel(family)
        violation = list(model.normal_bits[3])+list(model.normal_bits[6])
        export(f'{family}_normal_zeros.cnf', model, model.clauses+[violation],
               'the nontrivial normal stretch has N3=N6=0')
        for horizontal3, horizontal6 in product((-1, 0, 1), repeat=2):
            if horizontal3 == horizontal6 and horizontal3 != 0:
                continue
            model = virtual_model(family, horizontal3, horizontal6)
            encode = {-1: 'negative', 0: 'normal', 1: 'positive'}
            name = f'{family}_virtual_{encode[horizontal3]}_{encode[horizontal6]}.cnf'
            export(name, model, model.clauses,
                   'the virtual directions must both be horizontal-positive or both horizontal-negative')
        model = virtual_model(family, -1, -1)
        export(f'{family}_negative_upper_normal_zero.cnf', model,
               model.clauses+[list(model.upper_virtual_normal)],
               'both negative virtual directions force Y3=0')
        for infinite in (False, True):
            model = tilted_model(family, infinite)
            stratum = 'infinite' if infinite else 'finite'
            export(f'{family}_negative_tilt_{stratum}.cnf', model, model.clauses,
                   'negative virtual directions contradict the relative upper cap tilt')
    assert len(obligations) == 66
    result = {'checks': checks, 'divided_determinants_per_case': 29,
              'unsat_obligations': obligations,
              'excluded': 'all four middle-deficit common-line families and both diagonal line directions; interior ray1 C0',
              'relative_rate_assumptions': [],
              'reflection_closes_both_positive_directions': True,
              'whole_common_line_interior_closed_with_previous_results': True,
              'whole_ray1_exclusion_claimed': False,
              'seconds': time.monotonic()-started}
    (directory/'c0_middle_lines.json').write_text(json.dumps(result, indent=2)+'\n')
    return result


if __name__ == '__main__':
    if not __debug__:
        raise RuntimeError('run with assertions enabled')
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('output', type=Path)
    result = build(parser.parse_args().output)
    print(json.dumps({'unsat_obligations': len(result['unsat_obligations']),
                      'excluded': result['excluded'], 'seconds': result['seconds']}))
