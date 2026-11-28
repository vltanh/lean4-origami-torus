#!/usr/bin/env python3
"""Zero-safe reductions for the two-collinear-cap ray-2 C1 boundary.

All exported CNFs require independent RUP replay.  The positive-edge
stratum reduces to a common transverse line.  Two additional zero-edge
order orbits have parallel cap directions.  This is not an exclusion of
the whole two-collinear-cap boundary.
"""

import argparse
from functools import lru_cache
from itertools import combinations, product
import json
from pathlib import Path
import time

import sympy as S

import solver_remaining_c1_collinear as trits
import solver_remaining_c1_collinear_rank as rank
import solver_remaining_c1_flat_limits as old_flat
import solver_remaining_chambers as shared
from solver_chambers import write_cnf
from solver_sat import FastSAT


A, B = S.symbols('alpha beta')
HALF = S.Rational(1, 2)
UPPER = {'A': (4, (2, 3)), 'B': (2, (3, 4)), 'C': (4, (2,)),
         'D': (3, (2, 4)), 'E': (2, (3,)), 'F': (4, (3,))}
LOWER = {'A': (0, (6, 7)), 'B': (6, (0, 7)), 'C': (6, (0,)),
         'D': (7, (0, 6)), 'E': (7, (6,)), 'F': (7, (0,))}
ANCHORS = ((0, 1, 2, 3), (0, 1, 2, 7), (3, 4, 5, 6), (4, 5, 6, 7))
CROSS_QUADS = tuple(sorted({tuple(sorted(upper + lower))
                           for upper in combinations((2, 3, 4), 2)
                           for lower in combinations((0, 6, 7), 2)}))
DD_PATTERNS = ((-1, 0, 0, -1), (0, 1, -1, 0))
PARALLEL_RELATION = ((2, 1), (3, -1), (7, -1), (0, 1))
EA_RELATIONS = (((5, 1), (4, -1), (6, -1)),
                ((1, 1), (7, 1), (3, -1), (6, -1)))


def coefficient_sign(value):
    value = S.expand(value)
    if value == 0:
        return 0
    for sign in (1, -1):
        if any(S.expand(value - sign * positive) == 0
               for positive in (1, A, B, 1 - A, 1 - B)):
            return sign
    return None


@lru_cache(maxsize=1)
def height_relations():
    heights = (0, A, 1, 1, 1, B, 0, 0)

    def anchor(i, j):
        if i in (0, 1) or j in (0, 1):
            return {}
        return {tuple(sorted((0, 1, i, j))): 1 if i < j else -1}

    def area(a, b, c):
        result = {}
        for sign, i, j in ((1, b, c), (-1, a, c), (1, a, b)):
            for quad, value in anchor(i, j).items():
                result[quad] = result.get(quad, 0) + sign * value
        return result

    p = [S.zeros(2, 1), S.zeros(2, 1)]
    p.extend(S.Matrix(S.symbols(f'x{i} y{i}')) for i in range(2, 8))
    points = [point.col_join(S.Matrix([S.sympify(height) / 2]))
              for point, height in zip(p, heights)]

    def bracket(quad):
        first, *rest = quad
        return S.det(S.Matrix.hstack(*(points[i] - points[first] for i in rest)))

    all_rows, uniform = [], []
    for quad in trits.QUADS:
        row = {quad: A}
        for index, vertex in enumerate(quad):
            for minor, coefficient in area(*(quad[:index] + quad[index + 1:])).items():
                row[minor] = row.get(minor, 0) - (-1) ** (index + 3) * heights[vertex] * coefficient
        row = {minor: S.expand(coefficient) for minor, coefficient in row.items()
               if S.expand(coefficient) != 0}
        if not row:
            continue
        assert S.expand(sum(coefficient * bracket(minor) for minor, coefficient in row.items())) == 0
        all_rows.append(row)
        signs = {minor: coefficient_sign(value) for minor, value in row.items()}
        if None not in signs.values():
            uniform.append(signs)
        else:
            assert any(S.expand(value) in (A - B, B - A) for value in row.values())
    assert len(all_rows) == 55 and len(uniform) == 45
    return tuple(uniform)


class CapModel(trits.ActualBracketModel):
    def __init__(self, upper=None, lower=None):
        self.n, base, *_ = shared.base_formula()
        assert base[0] == [1]
        self.clauses = [list(row) for row in base[1:]]
        self.trits = {}
        for high in ({2, 3, 4}, {1, 2, 3, 4, 5}):
            for support in combinations(range(8), 5):
                if set(support) <= high or not set(support) & high:
                    continue
                row = [(1 if vertex in high else -1) * (-1) ** i
                       * shared.common.lit(support[:i] + support[i + 1:])
                       for i, vertex in enumerate(support)]
                self.clauses.extend((row, [-literal for literal in row]))
        for index, quad in enumerate(trits.QUADS):
            positive, negative = self.new_trit()
            self.trits[quad] = positive, negative
            self.clauses.extend(([-positive, index + 1], [-negative, -index - 1]))
        for support in combinations(range(8), 5):
            self.sumzero([self.bits(support[:i] + support[i + 1:], (-1) ** i)
                          for i in range(5)])
        for triangle in ((2, 3, 4), (0, 6, 7)):
            for vertex in range(8):
                if vertex not in triangle:
                    self.clauses.extend([[-bit] for bit in self.bits(triangle + (vertex,))])
        for choice, shapes in ((upper, UPPER), (lower, LOWER)):
            if choice is None:
                continue
            middle, parents = shapes[choice]
            for quad in trits.QUADS:
                if middle in quad:
                    self.sumzero([self.bits(tuple(parent if vertex == middle else vertex
                                                   for vertex in quad)) for parent in parents]
                                 + [self.bits(quad, -1)])
        self.add_weak_gp()
        for relation in rank.HEIGHT_SIGNS:
            self.sumzero([self.bits(quad, sign) for quad, sign in relation])
        for relation in height_relations():
            self.sumzero([self.bits(quad, sign) for quad, sign in relation.items()])

    def dependency(self, relation):
        for triple in combinations(range(8), 3):
            self.sumzero([self.bits(triple + (vertex,), sign) for vertex, sign in relation])

    def parallel(self):
        for quad in CROSS_QUADS:
            self.clauses.extend([[-bit] for bit in self.bits(quad)])

    def nonzero(self, quads):
        return [bit for quad in quads for bit in self.bits(quad)]


def saturation_checks():
    # If Y points with E, h<1/2 and |Y|=n>0, a positive deficit q
    # would force the nearest-lift sum p+q above 1/2.
    a, h, n = S.symbols('a h n')
    q = 2 * h * (a * h - n)
    p = (HALF - a * h - q * (1 / (2 * h) - a)) / (1 - a)
    excess = (1 - 2 * h) * (a * (1 - 2 * h) + 2 * n) / (2 * (1 - a))
    assert S.cancel(p + q - HALF - excess) == 0
    return {'same_direction_cauchy_saturation': True}


def dd_strict_sign_checks():
    h, k, lam, h5 = S.symbols('h k lambda h5')
    u, v = S.Matrix([1, 0]), S.Matrix([0, 1])
    p = [S.zeros(2, 1), S.zeros(2, 1), -lam * v,
         -lam * v - h * u, -lam * v - HALF * u,
         (1 - B) * h5 * u + ((1 - B) * HALF - B * lam) * v,
         HALF * v, k * v]
    z = (0, A / 2, HALF, HALF, HALF, B / 2, 0, 0)
    points = [point.col_join(S.Matrix([height])) for point, height in zip(p, z)]

    def bracket(quad):
        return S.det(S.Matrix.hstack(*(points[i] - points[quad[0]] for i in quad[1:])))

    m = B * HALF + (1 - B) * h5
    expected = {
        (1, 4, 6, 7): A * (HALF - k) / 4,
        (1, 5, 6, 7): -A * (1 - B) * h5 * (HALF - k) / 2,
        (2, 4, 5, 7): (1 - B) * (HALF - k) / 4,
        (4, 5, 6, 7): -m * (HALF - k) / 2,
    }
    for quad, value in expected.items():
        assert S.expand(bracket(quad) - value) == 0
    reflection = tuple((6 - i) % 8 for i in range(8))
    literal = shared.common.lit
    expected_images = (literal(ANCHORS[2]), -literal(ANCHORS[3]),
                       literal(ANCHORS[0]), -literal(ANCHORS[1]))
    assert tuple(literal(tuple(reflection[i] for i in quad)) for quad in ANCHORS) == expected_images
    assert literal(tuple(reflection[i] for i in (2, 3, 6, 7))) == -literal((0, 3, 4, 7))
    assert S.expand(bracket((2, 3, 6, 7)) - h * (HALF - k) / 2) == 0
    assert S.expand(bracket((0, 3, 4, 7)) + (HALF - h) * k / 2) == 0
    return {'dd_strict_minor_factors': 4, 'dd_pattern_reflection': True}


def zero_edge_checks():
    k = S.Symbol('k')
    v, e = S.Matrix(S.symbols('vx vy')), S.Matrix(S.symbols('ex ey'))
    p0 = S.zeros(2, 1)
    p1 = p0
    p3 = (HALF - (1 - A) * k) / A * v
    p4 = p3 + HALF * e
    p6, p7 = (k - HALF) * v, k * v
    p5 = B * p4 + (1 - B) * p6
    points = {i: point.col_join(S.Matrix([height])) for i, point, height in
              ((1, p1, A / 2), (3, p3, HALF), (4, p4, HALF),
               (5, p5, B / 2), (6, p6, 0), (7, p7, 0))}
    first = points[5] - B * points[4] - (1 - B) * points[6]
    second = points[1] + A * points[7] - A * points[3] - points[6]
    assert all(S.cancel(value) == 0 for value in list(first) + list(second))
    h4, c = S.symbols('h4 c')
    y = h4 - (1 - B) / 2
    sigma = h4 + (1 - B) / 2
    assert S.expand(HALF * y * c + HALF * sigma - h4 - HALF * y * (c - 1)) == 0
    return {'zero_edge_EA_EC_positive_dependencies': 2,
            'zero_edge_nonparallel_zero_Y5_factor': True}


def finite_symmetry_cover():
    reflected = {'A': 'B', 'B': 'A', 'C': 'C', 'D': 'D'}
    tip = lambda label: -1 if label == 'D' else 1

    def images(upper, lower, direction):
        yield 'identity', upper, lower, direction
        yield 'reflection', reflected[upper], reflected[lower], direction * tip(upper) * tip(lower)
        yield 'cap_swap', lower, upper, direction * tip(upper) * tip(lower)
        yield 'both', reflected[lower], reflected[upper], direction

    nonparallel = []
    parallel = []
    allowed_nonparallel = {('B', 'A'), ('B', 'B'), ('B', 'C'), ('B', 'D'),
                           ('C', 'D'), ('D', 'D'), ('C', 'C')}
    for upper, lower in product('ABCD', repeat=2):
        target = next(image for image in images(upper, lower, 1)
                      if image[1:3] in allowed_nonparallel)
        nonparallel.append({'case': upper + lower, 'symmetry': target[0],
                            'target': target[1] + target[2]})
        for direction in (-1, 1):
            found = None
            for name, uu, ll, dd in images(upper, lower, direction):
                if uu == ll == 'C':
                    reason = 'CC_budget'
                elif dd == -1 and tip(uu) == tip(ll):
                    reason = 'both_pairs_opposite'
                elif dd == 1 and (uu, ll) in {('A', 'A'), ('A', 'D'), ('B', 'D'),
                                              ('C', 'D'), ('D', 'D')}:
                    reason = 'parallel_anchor_CNF'
                elif dd == 1 and (uu, ll) in {('A', 'B'), ('A', 'C')}:
                    reason = 'half_edge_budget'
                else:
                    continue
                found = {'case': upper + lower, 'relative_direction': direction,
                         'symmetry': name, 'target': uu + ll,
                         'target_direction': dd, 'reason': reason}
                break
            assert found is not None
            parallel.append(found)
    assert len(nonparallel) == 16 and len(parallel) == 32
    return {'positive_edge_nonparallel_symmetry_cover': nonparallel,
            'positive_edge_parallel_symmetry_cover': parallel}


def build(directory):
    started = time.monotonic()
    checks = {**saturation_checks(), **dd_strict_sign_checks(), **zero_edge_checks(),
              **finite_symmetry_cover(),
              'uniform_height_relations': len(height_relations()),
              'marked_symmetries': rank.symbolic_checks()['marked_symmetries']}
    directory.mkdir(parents=True, exist_ok=True)
    obligations = []

    def emit(name, model, additions, claim):
        clauses = model.clauses + additions
        with FastSAT(model.n, clauses) as solver:
            assert solver.check() == -1, name
        filename = name + '.cnf'
        write_cnf(directory / filename, model.n, clauses)
        obligations.append({'file': filename, 'claim': claim,
                            'variables': model.n, 'clauses': len(clauses)})

    for upper, lower in (('B', 'A'), ('B', 'B'), ('B', 'C'), ('B', 'D'), ('C', 'D')):
        model = CapModel(upper, lower)
        emit('c1_flat2_nonparallel_' + upper + lower, model,
             [model.nonzero(CROSS_QUADS)], 'cap directions must be parallel')
    model = CapModel('D', 'D')
    additions = [[model.bits((2, 3, 6, 7))[0]],
                 model.nonzero(ANCHORS[:2]), model.nonzero(ANCHORS[2:])]
    for pattern in DD_PATTERNS:
        clause = []
        for quad, value in zip(ANCHORS, pattern):
            positive, negative = model.bits(quad)
            clause.extend([-positive] if value == 1 else [-negative] if value == -1
                          else [positive, negative])
        additions.append(clause)
    emit('c1_flat2_DD_anchor_cover', model, additions, 'the two stated actual anchor patterns cover DD')
    n, base, *_ = shared.base_formula()
    assert base[0] == [1]
    four = (((1, 4, 6, 7), 1), ((1, 5, 6, 7), -1),
            ((2, 4, 5, 7), 1), ((4, 5, 6, 7), -1))
    clauses = base[1:] + [[sign * shared.common.lit(quad)] for quad, sign in four]
    with FastSAT(n, clauses) as solver:
        assert solver.check() == -1
    filename = 'c1_flat2_DD_metric_signs.cnf'
    write_cnf(directory / filename, n, clauses)
    obligations.append({'file': filename, 'claim': 'four strict DD metric minors are incompatible',
                        'variables': n, 'clauses': len(clauses)})

    # Opposite directions give equal nonzero signs for the first pair.
    model = CapModel()
    model.parallel()
    emit('c1_flat2_opposite_anchor', model,
         [[model.bits(quad)[0]] for quad in ANCHORS[:2]],
         'parallel cap lines exclude actual0123>0 and actual0127>0')
    for upper, lower in (('A', 'A'), ('A', 'D'), ('B', 'D'), ('C', 'D'), ('D', 'D')):
        model = CapModel(upper, lower)
        model.parallel()
        model.dependency(PARALLEL_RELATION)
        emit('c1_flat2_parallel_anchor_' + upper + lower, model,
             [model.nonzero(ANCHORS)],
             'same E2/P7 direction forces all four actual anchors to vanish')
    for lower in ('A', 'C'):
        model = CapModel('E', lower)
        for dependency in EA_RELATIONS:
            model.dependency(dependency)
        emit('c1_flat2_zero_edge_E' + lower, model,
             [model.nonzero(CROSS_QUADS)], 'the EA/EC metric dependencies force parallel cap directions')
    assert len(obligations) == 15
    packet = {'domain': 'ray2 C1; both caps collinear; 0<alpha,beta<1',
              'positive_cap_edges_force_common_transverse_line': True,
              'additional_zero_edge_orbits_with_parallel_directions': ['EA', 'EC'],
              'whole_boundary_excluded': False, 'checks': checks,
              'unsat_obligations': obligations,
              'seconds': time.monotonic() - started}
    (directory / 'c1_flat_reduction.json').write_text(json.dumps(packet, indent=2) + '\n')
    return packet


if __name__ == '__main__':
    if not __debug__:
        raise RuntimeError('run with assertions enabled')
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('output', type=Path)
    packet = build(parser.parse_args().output)
    print(json.dumps({key: value for key, value in packet.items() if key != 'checks'}))
