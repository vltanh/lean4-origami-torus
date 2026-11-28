#!/usr/bin/env python3
"""Replay uniform quartic certificates for regular ray-1 C0.

Every accepted identity is expanded in 23 independent coordinate variables
using integer arithmetic. No optimizer, moment quotient, numerical rank,
or floating-point arithmetic is used by this verifier.
"""

import argparse
from collections import defaultdict
from functools import lru_cache
from itertools import combinations, combinations_with_replacement
import json
import hashlib
from pathlib import Path
import time

QUADS = tuple(combinations(range(8), 4))
PAIRS = tuple(combinations(range(2, 8), 2))
HEIGHTS = (20, 21, 22)
REGULAR_DEFICITS = frozenset((1, 2, 6, 7))
STRICT_NORMS = frozenset(((1, 2), (1, 3), (2, 3), (1, 6), (1, 7), (6, 7)))
STRICT_TURN = frozenset(((0, 2, 3, 7), (1, 2, 6, 7), (2, 3, 6, 7)))
DATA = Path(__file__).with_suffix('.json')


def variable(index):
    return {(index,): 1}


def linear(*terms):
    result = defaultdict(int)
    for polynomial, coefficient in terms:
        for monomial, value in polynomial.items():
            result[monomial] += coefficient * value
    return {monomial: value for monomial, value in result.items() if value}


def multiply(*polynomials):
    result = {(): 1}
    for polynomial in polynomials:
        product = defaultdict(int)
        for left, a in result.items():
            for right, b in polynomial.items():
                product[tuple(sorted(left + right))] += a * b
        result = {monomial: value for monomial, value in product.items() if value}
    return result


def vector_sum(*terms):
    return tuple(linear(*((point[i], coefficient) for point, coefficient in terms))
                 for i in range(2))


def scale(point, polynomial):
    return tuple(multiply(coordinate, polynomial) for coordinate in point)


def dot(left, right):
    return linear((multiply(left[0], right[0]), 1),
                  (multiply(left[1], right[1]), 1))


def cross(left, right):
    return linear((multiply(left[0], right[1]), 1),
                  (multiply(left[1], right[0]), -1))


@lru_cache(maxsize=1)
def polynomial_source():
    # 0..11 are the six planar points; 12..19 are deficits; 20..22
    # are a=2u, b=2(v-u), c=1-2v before common homogenization.
    P = [({}, {}), ({}, {})]
    P += [(variable(2*i), variable(2*i+1)) for i in range(6)]
    d = [variable(12+i) for i in range(8)]
    total = linear(*((value, 1) for value in d))
    T = linear((total, 2))
    h = [linear((total, 1), (value, -1)) for value in d]
    L, M = linear((d[1], 1), (d[2], 1)), linear((d[6], 1), (d[7], 1))
    D = linear((d[0], 1), (L, 1), (M, 1))
    a, b, c = map(variable, HEIGHTS)
    H = linear((a, 1), (b, 1), (c, 1))
    ab, bc = linear((a, 1), (b, 1)), linear((b, 1), (c, 1))
    E, F = vector_sum((P[3], 1), (P[2], -1)), vector_sum((P[7], 1), (P[6], -1))
    Q4 = vector_sum((scale(P[4], H), 1), (scale(P[3], a), -1), (scale(P[6], bc), -1))
    Q5 = vector_sum((scale(P[5], H), 1), (scale(P[3], ab), -1), (scale(P[6], c), -1))
    S = vector_sum((scale(Q4, c), 1), (scale(Q5, bc), -1))
    W = vector_sum((scale(Q4, ab), 1), (scale(Q5, a), -1))
    r = linear((multiply(H, h[3]), 1), (multiply(bc, D), -1))
    s = linear((multiply(H, h[5]), 1), (multiply(ab, D), -1))
    RS = linear((multiply(c, r), 1), (multiply(bc, s), 1))
    RW = linear((multiply(ab, r), 1), (multiply(a, s), 1))

    cap = [linear((dot(point, point), 1), (multiply(length, length), -1))
           for point, length in ((P[2], h[1]), (E, h[2]), (P[3], L),
                                 (P[7], h[7]), (F, h[6]), (P[6], M))]
    cap.append(linear((dot(P[2], P[7]), 1), (multiply(T, d[0]), -1),
                      (multiply(h[1], h[7]), 1)))
    middle = [
        linear((dot(Q4, Q4), 1), (multiply(r, r), -1)),
        linear((dot(Q5, Q5), 1), (multiply(s, s), -1)),
        linear((dot(Q4, Q5), 1), (multiply(r, s), 1), (multiply(H, H, T, d[4]), -1)),
        linear((dot(E, S), 1), (multiply(h[2], RS), -1),
               (multiply(c, H, T, linear((h[2], 1), (d[3], -1))), 1)),
        linear((dot(F, W), 1), (multiply(h[6], RW), -1),
               (multiply(a, H, T, linear((h[6], 1), (d[5], -1))), 1)),
    ]
    levels = ({}, H, H, H, a, ab, {}, {})
    brackets = {}
    for q in QUADS:
        origin, *others = q
        vectors = [vector_sum((P[j], 1), (P[origin], -1)) for j in others]
        heights = [linear((levels[j], 1), (levels[origin], -1)) for j in others]
        brackets[q] = linear(
            (multiply(heights[0], cross(vectors[1], vectors[2])), 1),
            (multiply(heights[1], cross(vectors[0], vectors[2])), -1),
            (multiply(heights[2], cross(vectors[0], vectors[1])), 1))

    positive = {}
    for i, j in combinations_with_replacement(range(8), 2):
        positive['d', i, j] = multiply(d[i], d[j])
    for i, j in combinations(range(1, 8), 2):
        difference = vector_sum((P[j], 1), (P[i], -1))
        positive['norm', i, j] = dot(difference, difference)
    displacement = vector_sum((P[6], 1), (P[3], -1))
    positive['mass', 0] = linear((multiply(D, D), 1), (dot(displacement, displacement), -1))
    for index, (i, j) in enumerate(((3, 4), (4, 5), (5, 6)), 1):
        difference = vector_sum((P[j], 1), (P[i], -1))
        positive['mass', index] = linear((multiply(h[i], h[i]), 1), (dot(difference, difference), -1))
    return {'P': P, 'd': d, 'T': T, 'H': H, 'h': h, 'cap': cap,
            'middle': middle, 'brackets': brackets,
            'areas': [cross(P[i], P[j]) for i, j in PAIRS], 'positive': positive}


def strict_bracket(q):
    return {1, 2, 3} <= set(q) or {0, 6, 7} <= set(q) or q in STRICT_TURN


def strict_factor(tag):
    if tag[0] == 'd':
        return tag[1] in REGULAR_DEFICITS and tag[2] in REGULAR_DEFICITS
    if tag[0] == 'norm':
        return tag[1:] in STRICT_NORMS
    return tag[0] == 'mass'


def one_cap_strict(q, factor, upper):
    """A strict residual requiring just the specified regular endpoint cap."""
    cap = {1, 2, 3} if upper else {0, 6, 7}
    deficits = {1, 2} if upper else {6, 7}
    norms = {(1, 2), (1, 3), (2, 3)} if upper else {(1, 6), (1, 7), (6, 7)}
    return cap <= set(q) and (
        factor[0] == 'd' and factor[1] in deficits and factor[2] in deficits
        or factor[0] == 'norm' and factor[1:] in norms)


def verify_identity(certificate):
    source = polynomial_source()
    word = tuple(certificate['word'])
    assert len(word) == 70 and set(word) <= {-1, 1}
    signs = dict(zip(QUADS, word))
    result = defaultdict(int)
    strict_terms, required, seen = 0, {}, set()
    cap_witnesses = {'upper': [], 'lower': []}
    counts = {'equation_terms': 0, 'positive_terms': 0}
    for record in certificate['terms']:
        kind, *fields = record
        weight = int(fields.pop())
        assert weight != 0
        key = json.dumps(record[:-1], separators=(',', ':'))
        assert key not in seen
        seen.add(key)
        if kind == 'cap':
            equation, area, heights = fields
            assert 0 <= equation < 7 and 0 <= area < 15
            assert tuple(heights) in tuple(combinations_with_replacement(HEIGHTS, 2))
            polynomial = multiply(source['cap'][equation], source['areas'][area],
                                  {tuple(heights): 1})
            counts['equation_terms'] += 1
        elif kind == 'middle':
            equation, area = fields
            assert 0 <= equation < 5 and 0 <= area < 15
            polynomial = multiply(source['middle'][equation], source['areas'][area])
            counts['equation_terms'] += 1
        elif kind == 'positive':
            q, sign, factor, height = fields
            q, factor = tuple(q), tuple(factor)
            assert q in QUADS and sign == signs[q] and height in HEIGHTS
            assert weight > 0
            if factor[0] == 'plusnorm':
                assert len(factor) == 3 and 2 <= factor[1] < factor[2] < 8
                vector = vector_sum((source['P'][factor[1]], 1), (source['P'][factor[2]], 1))
                nonnegative = dot(vector, vector)
            else:
                assert factor in source['positive']
                nonnegative = source['positive'][factor]
            polynomial = multiply(source['brackets'][q], nonnegative, variable(height))
            polynomial = linear((polynomial, sign))
            required[q] = sign
            strict_terms += int(strict_bracket(q) and strict_factor(factor))
            for name, upper in (('upper', True), ('lower', False)):
                if one_cap_strict(q, factor, upper):
                    cap_witnesses[name].append([list(q), sign, list(factor), height])
            counts['positive_terms'] += 1
        else:
            raise AssertionError(('unknown term type', kind))
        for monomial, value in polynomial.items():
            # Each term has planar/deficit degree four, height degree two.
            assert sum(index < 20 for index in monomial) == 4
            assert sum(index >= 20 for index in monomial) == 2
            result[monomial] += weight * value
    assert strict_terms > 0
    assert not any(result.values()), 'nonzero universal coordinate polynomial'
    return {**counts, 'strict_positive_terms': strict_terms,
            'one_cap_strict_witnesses': cap_witnesses,
            'required_signs': [[list(q), sign] for q, sign in sorted(required.items())],
            'expanded_coordinate_monomials': len(result),
            'max_weight_bits': max(abs(int(record[-1])).bit_length() for record in certificate['terms'])}


def source_checks():
    """Bind all twelve equations and all brackets independently of discovery."""
    import sympy as s
    import remaining_c0_height_order as metric
    import solver_remaining_c0_sections as sections
    import solver_remaining_c1_geometry as geometry
    import solver_remaining_limit as reduction

    source = polynomial_source()
    variables = s.symbols('v0:23')

    def expression(polynomial):
        return sum(value*s.prod(variables[i] for i in monomial)
                   for monomial, value in polynomial.items())

    u, v = s.symbols('u v')
    d = list(variables[12:20])
    normalized = {variables[19]: s.Rational(1, 2)-sum(d[:7]),
                  variables[20]: 2*u, variables[21]: 2*(v-u), variables[22]: 1-2*v}
    P = [s.Matrix([expression(value) for value in point]) for point in source['P']]
    h = [s.Rational(1, 2)-value for value in d]
    h = [value.subs(normalized) for value in h]
    X = geometry.horizontal_displacements(h)
    T = {edge: s.expand((P[edge[1]]-P[edge[0]]).dot(P[edge[1]]-P[edge[0]])-value**2)
         for edge, value in X.items()}
    original = reduction.original_system((s.Rational(1, 2),)*3+(1-u, -v, 0))
    edges = ((1, 2), (2, 3), (1, 3), (0, 7), (6, 7), (0, 6))
    for index, edge in enumerate(edges):
        assert not any(original[reduction.EDGES.index(edge), :])
        assert s.expand(expression(source['cap'][index]).subs(normalized)-T[edge]) == 0
    core_row = [int(edge == (0, 1))-int(edge == (0, 2))
                -int(edge == (1, 7))+int(edge == (2, 7)) for edge in reduction.EDGES]+[0]*5
    assert not any(s.Matrix([core_row])*original)
    core = T[0, 1]-T[0, 2]-T[1, 7]+T[2, 7]
    assert s.expand(2*expression(source['cap'][6]).subs(normalized)+core) == 0

    lu, lv = 1-2*u, 1-2*v
    D = sum((s.Rational(1, 2)-h[i]) for i in (0, 1, 2, 6, 7))
    Q4, Q5 = P[4]-2*u*P[3]-lu*P[6], P[5]-2*v*P[3]-lv*P[6]
    r, q = h[3]-lu*D, h[5]-2*v*D
    E, F = P[3]-P[2], P[7]-P[6]
    expected = (Q4.dot(Q4)-r*r, Q5.dot(Q5)-q*q,
                Q4.dot(Q5)+r*q-(s.Rational(1, 2)-h[4]),
                E.dot(lv*Q4-lu*Q5)-h[2]*(lv*r+lu*q)+lv*(h[2]-(s.Rational(1, 2)-h[3])),
                2*(F.dot(v*Q4-u*Q5)-h[6]*(v*r+u*q)+u*(h[6]-(s.Rational(1, 2)-h[5]))))
    for polynomial, target in zip(source['middle'], expected):
        assert s.expand(expression(polynomial).subs(normalized)-target) == 0

    levels = (0, s.Rational(1, 2), s.Rational(1, 2), s.Rational(1, 2), u, v, 0, 0)
    points = [point.col_join(s.Matrix([level])) for point, level in zip(P, levels)]
    for q in QUADS:
        actual = s.det(s.Matrix.hstack(*(points[j]-points[q[0]] for j in q[1:])))
        assert s.expand(expression(source['brackets'][q]).subs(normalized)-2*actual) == 0
    return {'full_source': metric.metric_bindings(), 'cap_core_source_rows': 7,
            'homogenized_middle_bindings': 5, 'common_positive_bracket_scale_checks': 70,
            'strict_masses': sections.scalar_checks()['timelike_middle_edges']+1}


def verify(data_path=DATA):
    raw = Path(data_path).read_bytes()
    data = json.loads(raw)
    assert data['format'] == 1
    checks = source_checks()
    certificates = [verify_identity(certificate) for certificate in data['certificates']]
    return {'source_checks': checks, 'certificate_count': len(certificates),
            'data_sha256': hashlib.sha256(raw).hexdigest(),
            'certificates': certificates, 'height_domain': '0<u<v<1/2',
            'actual_zeros_retained': True, 'numerical_solver_used_for_replay': False}


def build(directory, data_path=DATA):
    """Regenerate complete coverage; the exported CNF needs separate RUP."""
    import exhaustive_c0_height_order as source
    import exhaustive_c0_positive_cones as reflection
    import solver_remaining_chambers as shared
    from solver_chambers import transformed_model, write_cnf
    from solver_sat import FastSAT

    directory.mkdir(parents=True, exist_ok=True)
    result = verify(data_path)
    reflection_checks = reflection.symbolic_checks()
    permutation = tuple((1-i) % 8 for i in range(8))
    n, clauses = source.source_formula()
    literal = shared.common.lit
    base = clauses+[[literal((0, 1, 3, 6))], [-literal((2, 3, 4, 5))],
                    [-literal((4, 5, 6, 7))],
                    [literal((2, 3, 5, 6)), literal((3, 4, 6, 7))]]
    words = []
    with FastSAT(n, base) as solver:
        while solver.check() == 1:
            word = tuple(solver.model(70))
            words.append(word)
            solver.add([-(i+1)*value for i, value in enumerate(word)])
    words.sort()
    assert len(words) == len(set(words)) == 26
    covered, remaining = [], []
    for word in words:
        matches = []
        for reflected in (False, True):
            transformed = tuple(transformed_model(word, permutation)) if reflected else word
            signs = dict(zip(QUADS, transformed))
            for index, certificate in enumerate(result['certificates']):
                if all(signs[tuple(q)] == sign for q, sign in certificate['required_signs']):
                    matches.append({'certificate': index, 'reflected': reflected})
        if matches:
            covered.append({'word': word, 'certificates': matches})
        else:
            remaining.append(word)
    blocks = [[-(i+1)*value for i, value in enumerate(word)] for word in words]
    cnf = 'c0_quartic_26_source_coverage.cnf'
    with FastSAT(n, base+blocks) as solver:
        assert solver.check() == -1
    write_cnf(directory/cnf, n, base+blocks)
    result.update({'reflection_checks': reflection_checks,
                   'covered_word_count': len(covered), 'covered_words': covered,
                   'remaining_word_count': len(remaining), 'remaining_words': remaining,
                   'coverage_obligation': cnf,
                   'whole_regular_C0_interior_excluded_after_independent_replay': not remaining})
    (directory/'c0_quartic.json').write_text(json.dumps(result, indent=2)+'\n')
    return result


if __name__ == '__main__':
    if not __debug__:
        raise RuntimeError('run with assertions enabled')
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('output', type=Path, nargs='?')
    parser.add_argument('--data', type=Path, default=DATA)
    arguments = parser.parse_args()
    started = time.monotonic()
    result = build(arguments.output, arguments.data) if arguments.output else verify(arguments.data)
    print(json.dumps({'verified': True, 'certificate_count': result['certificate_count'],
                      'seconds': round(time.monotonic()-started, 3)}, sort_keys=True), flush=True)
