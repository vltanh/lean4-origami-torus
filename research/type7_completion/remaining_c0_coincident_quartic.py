#!/usr/bin/env python3
"""Exact zero implications close the upper-coincident interior C0 stratum.

Five full-coordinate integer identities and fourteen inherited identities
force a segment inconsistent with the exact metric radius.  The actual-
trit conjunction requires independent RUP acceptance.
"""

import argparse
from collections import defaultdict
from functools import lru_cache
from itertools import combinations_with_replacement
import hashlib
import json
from pathlib import Path
import time

import exhaustive_c0_collinear as boundary
import solver_remaining_c0_quartic as general
from solver_chambers import write_cnf
from solver_sat import FastSAT


DATA = Path(__file__).with_suffix('.json')


@lru_cache(maxsize=1)
def gauge_source():
    original = general.polynomial_source()
    substitutions = {0: general.linear((original['h'][1], -1)),
                     1: {}, 2: {}, 3: {}, 13: {}, 14: {}}

    def substitute(polynomial):
        result = {}
        for monomial, value in polynomial.items():
            term = {(): value}
            for variable in monomial:
                term = general.multiply(term, substitutions.get(variable, general.variable(variable)))
            result = general.linear((result, 1), (term, 1))
        return {monomial: value for monomial, value in result.items()
                if 13 not in monomial and 14 not in monomial}

    source = dict(original)
    for name in ('cap', 'middle', 'areas'):
        source[name] = [substitute(polynomial) for polynomial in original[name]]
    for name in ('brackets', 'positive'):
        source[name] = {key: substitute(polynomial) for key, polynomial in original[name].items()}
    source['P'] = [tuple(substitute(coordinate) for coordinate in point) for point in original['P']]
    assert all(not polynomial for polynomial in source['cap'][:3])
    assert source['P'][3] == ({}, {})
    return source


def strict_factor(tag):
    if tag[0] == 'd':
        return tag[1] in (6, 7) and tag[2] in (6, 7)
    return tag[0] == 'norm' and tag[1:] in ((1, 2), (2, 3), (1, 6), (1, 7), (6, 7))


def verify_identity(certificate):
    source = gauge_source()
    word = tuple(certificate['word'])
    assert len(word) == 70 and set(word) <= {-1, 1}
    signs = dict(zip(general.QUADS, word))
    residual = defaultdict(int)
    required, conclusions, seen = {}, set(), set()
    witnesses = []
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
            assert tuple(heights) in tuple(combinations_with_replacement(general.HEIGHTS, 2))
            polynomial = general.multiply(source['cap'][equation], source['areas'][area],
                                          {tuple(heights): 1})
            counts['equation_terms'] += 1
        elif kind == 'middle':
            equation, area = fields
            assert 0 <= equation < 5 and 0 <= area < 15
            polynomial = general.multiply(source['middle'][equation], source['areas'][area])
            counts['equation_terms'] += 1
        elif kind == 'positive':
            quad, sign, tag, height = fields
            quad, tag = tuple(quad), tuple(tag)
            assert quad in general.QUADS and sign == signs[quad]
            assert height in general.HEIGHTS and weight > 0
            if tag[0] == 'plusnorm':
                assert len(tag) == 3 and 2 <= tag[1] < tag[2] < 8
                vector = general.vector_sum((source['P'][tag[1]], 1), (source['P'][tag[2]], 1))
                factor = general.dot(vector, vector)
            else:
                assert tag in source['positive']
                factor = source['positive'][tag]
            polynomial = general.multiply(source['brackets'][quad], factor, general.variable(height))
            polynomial = general.linear((polynomial, sign))
            required[quad] = sign
            if strict_factor(tag):
                conclusions.add((quad, sign))
                witnesses.append([list(quad), sign, list(tag), height])
            counts['positive_terms'] += 1
        else:
            raise AssertionError(('unknown term type', kind))
        for monomial, value in polynomial.items():
            assert sum(index < 20 for index in monomial) == 4
            assert sum(index >= 20 for index in monomial) == 2
            assert 13 not in monomial and 14 not in monomial
            residual[monomial] += weight*value
    assert conclusions, 'no separately proved positive factor for a zero implication'
    assert not any(residual.values()), 'nonzero full-coordinate residual'
    return {**counts, 'strict_factor_witnesses': witnesses,
            'required_signs': [[list(quad), sign] for quad, sign in sorted(required.items())],
            'zero_conclusions': [[list(quad), sign] for quad, sign in sorted(conclusions)],
            'expanded_coordinate_monomials': len(residual),
            'max_weight_bits': max(abs(int(record[-1])).bit_length() for record in certificate['terms'])}


def inherited_zero_rules(certificate, upper):
    deficits = (1, 2) if upper else (6, 7)
    norms = ((1, 2), (1, 3), (2, 3)) if upper else ((1, 6), (1, 7), (6, 7))
    required, conclusions = {}, set()
    for record in certificate['terms']:
        if record[0] != 'positive':
            continue
        _, quad, sign, tag, height, weight = record
        quad, tag = tuple(quad), tuple(tag)
        assert int(weight) > 0
        required[quad] = sign
        if (tag[0] == 'd' and tag[1] in deficits and tag[2] in deficits
                or tag[0] == 'norm' and tag[1:] in norms):
            conclusions.add((quad, sign))
    return {'required_signs': [[list(quad), sign] for quad, sign in sorted(required.items())],
            'zero_conclusions': [[list(quad), sign] for quad, sign in sorted(conclusions)]}


def add_zero_rules(model, identity, reflected=False):
    permutation = tuple((1-i) % 8 for i in range(8))

    def transform(quad):
        return tuple(permutation[i] for i in quad) if reflected else tuple(quad)

    failures = [model.bits(transform(quad), -sign)[0]
                for quad, sign in identity['required_signs']]
    for quad, sign in identity['zero_conclusions']:
        # All required weak signs plus a strictly positive quadratic
        # factor force this bracket to vanish.  A zero actual trit
        # satisfies the conclusion; its generic completion stays free.
        model.clauses.append(failures+[-model.bits(transform(quad), sign)[0]])
    return len(identity['zero_conclusions'])


def segment_checks():
    import sympy as s
    x, y, a, b, t, v = s.symbols('x y a b t v')
    P6, P7 = s.Matrix((x, y)), s.Matrix((a, b))
    P5 = t*P6
    C67 = s.det(s.Matrix.hstack(P6, P7))
    C57 = s.det(s.Matrix.hstack(P5, P7))
    points = (s.Matrix((0, 0, s.Rational(1, 2))), P5.col_join(s.Matrix((v,))),
              P6.col_join(s.zeros(1, 1)), P7.col_join(s.zeros(1, 1)))
    bracket = s.det(s.Matrix.hstack(*(point-points[0] for point in points[1:])))
    assert s.expand(C57-t*C67) == 0
    assert s.expand(2*bracket-(t-(1-2*v))*C67) == 0
    assert all(s.expand(value) == 0 for value in P5-(1-2*v)*P6-(t-(1-2*v))*P6)
    return {'segment_determinant_identities': 2, 'segment_radius_identity': 1}


def actual_source():
    model = boundary.ActualModel('1_equals_3', 1, boundary.height_relations())
    model.clauses.extend([[model.bits((2, 3, 6, 7))[0]],
                          [model.bits((1, 2, 6, 7))[1]],
                          [-model.bits((0, 2, 3, 7))[1]],
                          [-model.bits((2, 3, 4, 5))[0]],
                          [-model.bits((4, 5, 6, 7))[0]]])
    return model


def build(directory=None, data_path=DATA):
    raw = Path(data_path).read_bytes()
    data = json.loads(raw)
    assert data['format'] == 1 and data['collinear_case'] == '1_equals_3'
    assert data['zero_deficits'] == [1, 2]
    inherited_raw = general.DATA.read_bytes()
    inherited_data = json.loads(inherited_raw)
    inherited = general.verify()
    assert hashlib.sha256(inherited_raw).hexdigest() == inherited['data_sha256']
    identities = [verify_identity(certificate) for certificate in data['certificates']]
    reflection = boundary.symmetry_checks()
    segment = segment_checks()
    model = actual_source()
    inherited_count = 0
    for reflected in (False, True):
        for certificate in inherited_data['certificates']:
            inherited_count += add_zero_rules(model, inherited_zero_rules(certificate, reflected), reflected)
    new_count = sum(add_zero_rules(model, identity) for identity in identities)
    violation = list(model.bits((0, 1, 5, 6)))
    violation += [model.bits((0, 1, 5, 7))[1], model.bits((1, 5, 6, 7))[0],
                  -model.bits((0, 1, 2, 7))[1]]
    clauses = model.clauses+[violation]
    with FastSAT(model.n, clauses) as solver:
        status = solver.check()
    assert status in (-1, 1)
    result = {'inherited_source_checks': inherited['source_checks'],
              'inherited_identity_count': len(inherited['certificates']),
              'inherited_zero_implications': inherited_count,
              'certificate_count': len(identities), 'certificates': identities,
              'new_zero_implications': new_count, 'reflection': reflection, 'segment_checks': segment,
              'data_sha256': hashlib.sha256(raw).hexdigest(),
              'conclusion': 'actual C56=0, C57>=0, [1567]<=0, C27<0',
              'segment_conjunction_verified': status == -1,
              'actual_zeros_retained': True,
              'numerical_solver_used_for_replay': False,
              'complete_upper_coincident_interior_after_independent_replay_and_segment_proof': status == -1}
    if directory is not None:
        directory.mkdir(parents=True, exist_ok=True)
        if status == -1:
            filename = 'c0_coincident_quartic_segment.cnf'
            write_cnf(directory/filename, model.n, clauses)
            result['coverage_obligation'] = filename
        (directory/'c0_coincident_quartic.json').write_text(json.dumps(result, indent=2)+'\n')
    return result


if __name__ == '__main__':
    if not __debug__:
        raise RuntimeError('run with assertions enabled')
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('output', type=Path, nargs='?')
    parser.add_argument('--data', type=Path, default=DATA)
    arguments = parser.parse_args()
    started = time.monotonic()
    result = build(arguments.output, arguments.data)
    print(json.dumps({'exact_identities': result['certificate_count'],
                      'segment_conjunction': result['segment_conjunction_verified'],
                      'seconds': time.monotonic()-started}))
