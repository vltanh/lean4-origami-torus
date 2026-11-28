#!/usr/bin/env python3
"""Exclude all six flat ray-1 C1 families by a normal stretch.

Usage: python solver_remaining_c1_flat_stretch.py OUTPUT_DIRECTORY

The fourteen CNFs cover all four ordinary closed parameter intervals
and both special families. Their coefficient signs are certified on
entire parameter boxes, not sampled. Every emitted CNF must additionally
pass independent RUP replay. No relative collapse-rate assumption is used.
"""

import argparse
from functools import lru_cache
from itertools import combinations, product
import json
from pathlib import Path
import time

import sympy as s

import solver_remaining_c1_collinear as trits
import solver_remaining_c1_flat_limits as flat
import solver_remaining_chambers as shared
from solver_chambers import write_cnf
from solver_sat import FastSAT

ALPHA, BETA, R = flat.ALPHA, flat.BETA, flat.R
PARAMETERS = (ALPHA, BETA, R)
FAMILIES = ((2, 6), (2, 7), (3, 6), (3, 7), 'left', 'right')
NORMAL_VERTICES = (2, 4, 5, 6, 7)
NORMALS = s.symbols('n2 n4 n5 n6 n7')
QUADS = tuple(combinations(range(8), 4))
QUAD_INDEX = {quad: i for i, quad in enumerate(QUADS)}
TRIPLES = tuple(combinations(range(8), 3))
TRIPLE_INDEX = {triple: i for i, triple in enumerate(TRIPLES)}
CORNERS = tuple(product((0, 1), (0, 1), (0, flat.HALF)))


def parity(indices):
    return (-1)**sum(indices[i] > indices[j]
                    for i, j in combinations(range(len(indices)), 2))


@lru_cache(maxsize=None)
def geometry(family):
    """Bind the stretch directly to the six previously checked families."""
    deficits, horizontal = flat.family_coordinates(family)
    levels = (0, ALPHA, 1, 1, 1, BETA, 0, 0)
    normal = dict(zip(NORMAL_VERTICES, NORMALS))
    # Both transformations preserve the normal coordinate. They have
    # determinant four, and act only after the nontrivial normal stretch.
    shear = 0 if family == 'left' else 1/ALPHA
    transform = s.Matrix([[2, 0, -2*shear], [0, 1, 0], [0, 0, 2]])
    assert transform.det() == 4
    points = []
    for i in range(8):
        original = s.Matrix((horizontal[i], normal.get(i, 0), s.sympify(levels[i])/2))
        point = (transform*original).applyfunc(s.cancel)
        assert point[1] == normal.get(i, 0) and point[2] == levels[i]
        assert s.denom(point[0]) == 1
        points.append(point)
    assert horizontal[0] == horizontal[1] == 0
    if family == 'left':
        assert horizontal[3] == flat.HALF
    else:
        assert s.expand(ALPHA*horizontal[3]-(1-ALPHA)/2-ALPHA*deficits[2]) == 0

    rows = []
    for quad in QUADS:
        determinant = s.expand(s.Matrix.hstack(
            *(points[i]-points[quad[0]] for i in quad[1:])).det())
        row = tuple(determinant.coeff(normal) for normal in NORMALS)
        assert s.expand(determinant-sum(a*b for a, b in zip(row, NORMALS))) == 0
        rows.append(row)
    areas = []
    for i, j, k in TRIPLES:
        areas.append(s.expand((points[j][0]-points[i][0])*(points[k][2]-points[i][2])
                              -(points[k][0]-points[i][0])*(points[j][2]-points[i][2])))

    def area(triple):
        return parity(triple)*areas[TRIPLE_INDEX[tuple(sorted(triple))]]

    relations = []
    for i, j in combinations(range(8), 2):
        for a, b, c in combinations([v for v in range(8) if v not in (i, j)], 3):
            quads = ((i, j, a, b), (i, j, a, c), (i, j, b, c))
            coefficients = (area((i, j, c)), -area((i, j, b)), area((i, j, a)))
            # Verify every projected GP identity in all five independent
            # normal coordinates before using any coefficient sign.
            for column in range(len(NORMALS)):
                assert s.expand(sum(coefficient*parity(quad)
                                    *rows[QUAD_INDEX[tuple(sorted(quad))]][column]
                                    for quad, coefficient in zip(quads, coefficients))) == 0
            relations.append(tuple(zip(quads, coefficients)))
    assert len(rows) == 70 and len(relations) == 560
    return tuple(rows), tuple(relations)


@lru_cache(maxsize=None)
def coefficient_sign(expression):
    """Strict interior sign by exact multilinear corner interpolation.

    None means the sign is not uniform and the entire relation is omitted.
    Zero means the coefficient is identically zero. Every nonzero returned
    sign is strict throughout 0<alpha,beta<1 and 0<r<1/2.
    For endpoint strata r has already been substituted, so only the two
    open height parameters remain.
    """
    polynomial = s.Poly(s.expand(expression), *PARAMETERS)
    assert all(max(exponents) <= 1 for exponents, _ in polynomial.terms())
    values = tuple(polynomial.eval(dict(zip(PARAMETERS, corner))) for corner in CORNERS)
    # Verify the interpolation identity itself, including the r scaling.
    reconstruction = 0
    for corner, value in zip(CORNERS, values):
        weight = ((ALPHA if corner[0] else 1-ALPHA)
                  *(BETA if corner[1] else 1-BETA)
                  *(2*R if corner[2] else 1-2*R))
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
    """Actual trits over the unchanged necessary generic topology source."""
    def __init__(self, family, endpoint):
        self.n, base, *_ = shared.base_formula()
        self.clauses = [list(clause) for clause in base]
        self.trits = {}
        # Strict axial cuts survive both the actual stretch and a small
        # generic perturbation. No cap area is required to be nonzero.
        for high in ({2, 3, 4}, {1, 2, 3, 4, 5}):
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
        normal_bits = [self.new_trit() for _ in NORMALS]
        self.clauses.append([bit for pair in normal_bits for bit in pair])
        for support in combinations(range(8), 5):
            self.sumzero([self.bits(support[:i]+support[i+1:], (-1)**i)
                          for i in range(5)])

        rows, relations = geometry(family)
        specialize = lambda value: value if endpoint is None else s.expand(value.subs(R, endpoint))
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


def build(directory):
    started = time.monotonic()
    directory.mkdir(parents=True, exist_ok=True)
    obligations = []
    for family in FAMILIES:
        strata = (('interior', None), ('left_endpoint', s.Integer(0)),
                  ('right_endpoint', flat.HALF)) if isinstance(family, tuple) else (('interior', None),)
        for stratum, endpoint in strata:
            model = NormalModel(family, endpoint)
            with FastSAT(model.n, model.clauses) as solver:
                assert solver.check() == -1, (family, stratum)
            label = ''.join(map(str, family)) if isinstance(family, tuple) else family
            name = f'c1_flat_stretch_{label}_{stratum}.cnf'
            write_cnf(directory/name, model.n, model.clauses)
            obligations.append({'file': name, 'family': family, 'stratum': stratum,
                                'variables': model.n, 'clauses': len(model.clauses), **model.counts})
    assert len(obligations) == 14
    packet = {'assumptions': ['ray1', '0<alpha,beta<1', 'one of the six classified flat families'],
              'families': FAMILIES, 'normal_vertices': NORMAL_VERTICES,
              'geometry_checks_per_family': {'linear_determinants': 70, 'projected_gp_identities': 560},
              'coefficient_sign_method': 'exact multilinear interpolation over all eight box corners',
              'unsat_obligations': obligations,
              'all_six_flat_families_excluded': True,
              'relative_rate_assumptions': [], 'explicit_height_bound': None,
              'seconds': round(time.monotonic()-started, 3)}
    (directory/'c1_flat_stretch.json').write_text(json.dumps(packet, indent=2)+'\n')
    return packet


if __name__ == '__main__':
    if not __debug__:
        raise RuntimeError('run with assertions enabled')
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('output', type=Path)
    packet = build(parser.parse_args().output)
    print(json.dumps({'families': len(FAMILIES), 'unsat_obligations': len(packet['unsat_obligations']),
                      'all_six_flat_families_excluded': True, 'seconds': packet['seconds']}), flush=True)
