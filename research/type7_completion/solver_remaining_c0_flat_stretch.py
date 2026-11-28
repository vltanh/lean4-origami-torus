#!/usr/bin/env python3
"""Analyze normal stretches of the eight common-line ray-1 C0 families.

This compiler retains all parameter endpoints and actual zero minors.
SAT outputs are residual sign systems, not realizations or exclusions.
UNSAT outputs require independent RUP replay.
"""

import argparse
from functools import lru_cache
from itertools import combinations, product
import json
from pathlib import Path
import time

import sympy as s

import solver_remaining_c1_collinear as trits
import solver_remaining_c1_geometry as metric_geometry
import solver_remaining_chambers as shared
import solver_remaining_limit as reduction
from solver_chambers import write_cnf
from solver_sat import FastSAT

A, B, T = s.symbols('a b t')
PARAMETERS = (A, B, T)
HALF = s.Rational(1, 2)
FAMILIES = tuple('endpoint_'+a+b for a, b in product('ab', repeat=2)) + (
    'middle_lt_positive', 'middle_lt_negative',
    'middle_gt_positive', 'middle_gt_negative',
    'diagonal_positive', 'diagonal_negative')
QUADS = tuple(combinations(range(8), 4))
QUAD_INDEX = {quad: i for i, quad in enumerate(QUADS)}
TRIPLES = tuple(combinations(range(8), 3))
TRIPLE_INDEX = {triple: i for i, triple in enumerate(TRIPLES)}
CORNERS = tuple(product((0, 1), repeat=3))
RESIDUAL_PATTERNS = {
    ('endpoint_aa', 0): ((0, 1, 1, 1, 0), (0, 1, 1, 0, 0), (0, 0, 0, 1, 0)),
    ('endpoint_ba', 1): ((0, 1, 1, 1, 0), (0, 0, 1, 1, 0), (0, 1, 0, 0, 0)),
    ('middle_lt_positive', None): ((0, 1, 1, 0, 1),),
    ('middle_lt_negative', None): ((0, 0, 0, 0, -1), (0, 0, 0, 0, 1)),
    ('middle_gt_positive', None): ((0, 0, 0, 0, -1), (0, 1, 1, 0, -1),
                                  (0, 1, 1, 0, 0), (0, 0, 0, 0, 1),
                                  (0, -1, -1, 0, 1), (0, -1, -1, 0, 0)),
    ('middle_gt_negative', None): ((0, 1, 1, 0, 0), (0, 1, 1, 0, -1),
                                  (0, -1, -1, 0, 1), (0, -1, -1, 0, 0)),
    ('diagonal_positive', None): ((0, -1, -1, 0, 0), (0, -1, -1, 0, 1),
                                 (0, 0, 0, 0, 1), (0, 1, 1, 0, 1),
                                 (0, 0, 0, 0, -1), (0, 1, 1, 0, -1),
                                 (0, 1, 1, 0, 0)),
    ('diagonal_negative', None): ((0, 1, 1, 0, 0), (0, 1, 1, 0, -1),
                                 (0, 0, 0, 0, -1), (0, -1, -1, 0, 0),
                                 (0, -1, -1, 0, 1), (0, 0, 0, 0, 1)),
}


def parity(indices):
    return (-1)**sum(indices[i] > indices[j]
                    for i, j in combinations(range(len(indices)), 2))


def coordinates(family):
    """Twice the horizontal coordinates and heights of the classification.

    The positive affine map diag(2,1,2) is applied after normal stretching.
    A,B,T vary independently in (0,1); endpoint strata substitute T first.
    """
    d = [s.Integer(0)]*8
    if family.startswith('endpoint_'):
        upper, lower = family[-2:]
        d[2 if upper == 'a' else 1] = T/2
        d[7 if lower == 'a' else 6] = (1-T)/2
        u, v = A/2, B/2
        x3 = -T if upper == 'a' else T
        x6 = -(1-T) if lower == 'a' else 1-T
        x = (0, 0, -1+2*d[1], x3,
             A*x3+(1-A)*x6-A,
             B*x3+(1-B)*x6+1-B, x6, 1-2*d[7])
    else:
        if family == 'middle_lt_positive':
            u, v = A/2, (A+(1-A)*B)/2
            index, x4, x5 = 5, 1, 1-B
            deficit_formula = (v-u)/(1-2*u)
        elif family == 'middle_lt_negative':
            u, v = A*(1-B)/2, A/2
            index, x4, x5 = 3, B-1, -1
            deficit_formula = (v-u)/(2*v)
        elif family == 'middle_gt_positive':
            u, v = (A+(1-A)*B)/2, A/2
            index, x4, x5 = 3, 1-B, 1
            deficit_formula = (u-v)/(1-2*v)
        elif family == 'middle_gt_negative':
            u, v = A/2, A*(1-B)/2
            index, x4, x5 = 5, -1, B-1
            deficit_formula = (u-v)/(2*u)
        else:
            assert family in ('diagonal_positive', 'diagonal_negative')
            u = v = A/2
            x4 = x5 = 1 if family == 'diagonal_positive' else -1
            index = None
        if index is None:
            d[4] = HALF
        else:
            d[index], d[4] = B/2, (1-B)/2
            assert s.cancel(deficit_formula-d[index]) == 0
        x = (0, 0, -1, 0, x4, x5, 0, 1)
    levels = (0, 1, 1, 1, 2*u, 2*v, 0, 0)
    x = tuple(s.sympify(value) for value in x)
    levels = tuple(s.sympify(value) for value in levels)
    assert s.expand(sum(d)-HALF) == 0
    return tuple(d), x, levels


@lru_cache(maxsize=None)
def source_check(family):
    d, x, levels = coordinates(family)
    h = [HALF-value for value in d]
    X = metric_geometry.horizontal_displacements(h)
    rows = reduction.closed_c0_rows().subs(
        {reduction.A: 1-levels[4]/2, reduction.B: -levels[5]/2})
    residuals = [(x[j]-x[i])**2/4-X[i, j]**2 for i, j in reduction.EDGES]
    for value in rows*s.Matrix(residuals+[0]*5):
        assert s.expand(value) == 0
    return 12


@lru_cache(maxsize=None)
def geometry(family, anchor):
    _, x, levels = coordinates(family)
    vertices = tuple(i for i in range(8) if i not in (0, 1, anchor))
    normals = s.symbols(' '.join('n'+str(i) for i in vertices))
    normal = dict(zip(vertices, normals))
    points = [s.Matrix((x[i], normal.get(i, 0), levels[i])) for i in range(8)]
    rows = []
    for quad in QUADS:
        determinant = s.expand(s.Matrix.hstack(
            *(points[i]-points[quad[0]] for i in quad[1:])).det())
        row = tuple(determinant.coeff(n) for n in normals)
        assert s.expand(determinant-sum(c*n for c, n in zip(row, normals))) == 0
        rows.append(row)
    areas = [s.expand((x[j]-x[i])*(levels[k]-levels[i])
                      -(x[k]-x[i])*(levels[j]-levels[i]))
             for i, j, k in TRIPLES]

    def area(triple):
        return parity(triple)*areas[TRIPLE_INDEX[tuple(sorted(triple))]]

    relations = []
    for i, j in combinations(range(8), 2):
        for a, b, c in combinations([v for v in range(8) if v not in (i, j)], 3):
            quads = ((i, j, a, b), (i, j, a, c), (i, j, b, c))
            coefficients = (area((i, j, c)), -area((i, j, b)), area((i, j, a)))
            for column in range(len(normals)):
                assert s.expand(sum(coefficient*parity(quad)
                                    *rows[QUAD_INDEX[tuple(sorted(quad))]][column]
                                    for quad, coefficient in zip(quads, coefficients))) == 0
            relations.append(tuple(zip(quads, coefficients)))
    assert len(rows) == 70 and len(relations) == 560
    return vertices, tuple(rows), tuple(relations)


@lru_cache(maxsize=None)
def coefficient_sign(expression):
    polynomial = s.Poly(s.expand(expression), *PARAMETERS)
    assert all(max(exponents) <= 1 for exponents, _ in polynomial.terms()), expression
    values = tuple(polynomial.eval(dict(zip(PARAMETERS, corner))) for corner in CORNERS)
    reconstruction = 0
    for corner, value in zip(CORNERS, values):
        weight = s.prod(parameter if high else 1-parameter
                        for parameter, high in zip(PARAMETERS, corner))
        reconstruction += value*weight
    assert s.expand(reconstruction-expression) == 0
    if all(value == 0 for value in values):
        return 0
    if all(value >= 0 for value in values):
        return 1
    if all(value <= 0 for value in values):
        return -1
    return None


class NormalModel(trits.ActualBracketModel):
    def __init__(self, family, endpoint=None):
        self.n, base, *_ = shared.base_formula()
        self.clauses = [list(clause) for clause in base]
        self.trits = {}
        for high in ({1, 2, 3}, {1, 2, 3, 4, 5}):
            for support in combinations(range(8), 5):
                if set(support) <= high or not set(support) & high:
                    continue
                row = [(1 if vertex in high else -1)*(-1)**i
                       *shared.common.lit(support[:i]+support[i+1:])
                       for i, vertex in enumerate(support)]
                self.clauses.extend((row, [-literal for literal in row]))
        for index, quad in enumerate(QUADS):
            positive, negative = self.new_trit()
            self.trits[quad] = positive, negative
            self.clauses.extend(([-positive, index+1], [-negative, -index-1]))
        anchor = 7 if family.startswith('endpoint_b') and endpoint == 1 else 2
        vertices, rows, relations = geometry(family, anchor)
        normal_bits = [self.new_trit() for _ in vertices]
        self.clauses.append([bit for pair in normal_bits for bit in pair])
        for support in combinations(range(8), 5):
            self.sumzero([self.bits(support[:i]+support[i+1:], (-1)**i)
                          for i in range(5)])
        specialize = lambda value: value if endpoint is None else s.expand(value.subs(T, endpoint))
        counts = {'bracket_relations': 0, 'projection_relations': 0,
                  'omitted_bracket_relations': 0, 'omitted_projection_relations': 0}
        for quad, row in zip(QUADS, rows):
            signs = tuple(coefficient_sign(specialize(value)) for value in row)
            if None in signs:
                counts['omitted_bracket_relations'] += 1
                continue
            self.sumzero([self.bits(quad, -1)]+[
                pair if sign > 0 else pair[::-1]
                for pair, sign in zip(normal_bits, signs) if sign])
            counts['bracket_relations'] += 1
        for relation in relations:
            signs = tuple(coefficient_sign(specialize(value)) for _, value in relation)
            if None in signs:
                counts['omitted_projection_relations'] += 1
                continue
            forms = [self.bits(quad, sign) for (quad, _), sign in zip(relation, signs) if sign]
            if forms:
                self.sumzero(forms)
                counts['projection_relations'] += 1
        self.counts = counts
        self.anchor = anchor
        self.normal_bits = dict(zip(vertices, normal_bits))


def build(directory):
    started = time.monotonic()
    directory.mkdir(parents=True, exist_ok=True)
    obligations, residual, residual_sources = [], [], {}
    for family in FAMILIES:
        source_check(family)
        strata = (('interior', None), ('left_endpoint', s.Integer(0)),
                  ('right_endpoint', s.Integer(1))) if family.startswith('endpoint_') else (('interior', None),)
        for stratum, endpoint in strata:
            model = NormalModel(family, endpoint)
            with FastSAT(model.n, model.clauses) as solver:
                status = solver.check()
            record = {'family': family, 'stratum': stratum,
                      'variables': model.n, 'clauses': len(model.clauses),
                      'anchor': model.anchor, **model.counts}
            if status == -1:
                name = f'c0_flat_stretch_{family}_{stratum}.cnf'
                write_cnf(directory/name, model.n, model.clauses)
                obligations.append({'file': name, **record})
            else:
                assert status == 1
                source_key = (tuple(model.normal_bits), tuple(map(tuple, model.clauses)))
                key = (family, endpoint)
                if key in RESIDUAL_PATTERNS:
                    patterns = RESIDUAL_PATTERNS[key]
                    blocked = []
                    for pattern in patterns:
                        clause = []
                        for (positive, negative), value in zip(model.normal_bits.values(), pattern):
                            assert value in (-1, 0, 1)
                            clause.extend([-positive] if value > 0 else
                                          [-negative] if value < 0 else [positive, negative])
                        blocked.append(clause)
                    clauses = model.clauses+blocked
                    with FastSAT(model.n, clauses) as solver:
                        assert solver.check() == -1, (family, 'normal cover')
                    name = f'c0_flat_normal_cover_{family}_{stratum}.cnf'
                    write_cnf(directory/name, model.n, clauses)
                    obligations.append({'file': name, 'kind': 'residual_normal_cover',
                                        'family': family, 'stratum': stratum,
                                        'variables': model.n, 'clauses': len(clauses),
                                        'normal_vertices': tuple(model.normal_bits),
                                        'normal_sign_patterns': patterns})
                    residual_sources[source_key] = name
                else:
                    assert source_key in residual_sources, (family, stratum)
                    name = residual_sources[source_key]
                record['normal_cover'] = name
                residual.append(record)
            print(json.dumps({**record, 'status': status}), flush=True)
    assert len(obligations) == 16 and len(residual) == 10 and len(residual_sources) == 8
    packet = {'unsat_obligations': obligations, 'residual_systems': residual,
              'excluded': ['all four endpoint-deficit interiors',
                           'zero-edge endpoints h2=0 and h6=0'],
              'remaining': ['zero-edge endpoints h1=0 and h7=0',
                            'four middle-deficit line families',
                            'coincident45 circle including its two line directions'],
              'source_projected_stresses_per_family': 12,
              'geometry_checks_per_family': {'linear_determinants': 70,
                                             'projected_gp_identities': 560},
              'coefficient_sign_method': 'exact multilinear interpolation on eight corners',
              'relative_rate_assumptions': [], 'explicit_height_bound': None,
              'seconds': round(time.monotonic()-started, 3)}
    (directory/'c0_flat_stretch.json').write_text(json.dumps(packet, indent=2)+'\n')
    return packet


if __name__ == '__main__':
    if not __debug__:
        raise RuntimeError('run with assertions enabled')
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('output', type=Path)
    packet = build(parser.parse_args().output)
    print(json.dumps({'unsat_obligations': len(packet['unsat_obligations']),
                      'residual_systems': len(packet['residual_systems']),
                      'seconds': packet['seconds']}), flush=True)
