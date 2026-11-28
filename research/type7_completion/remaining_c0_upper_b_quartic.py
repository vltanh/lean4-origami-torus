#!/usr/bin/env python3
"""Exact uniform quartic replay and zero-safe cover for upper-b C0.

The upper cap has d2=0<d1; the lower cap is regular; 0<u<v<1/2.
All polynomial identities are expanded over the full coordinate ring.
The finite cover additionally requires independent RUP acceptance.
"""

import argparse
from collections import defaultdict
from functools import lru_cache
from itertools import combinations_with_replacement
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
    length = general.linear((original['d'][1], 1), (original['d'][2], 1))
    substitutions = {0: general.linear((original['h'][1], -1)), 1: {},
                     2: length, 3: {}, 14: {}}

    def substitute(polynomial):
        result = {}
        for monomial, value in polynomial.items():
            term = {(): value}
            for variable in monomial:
                term = general.multiply(term, substitutions.get(variable, general.variable(variable)))
            result = general.linear((result, 1), (term, 1))
        # The d2 substitution also applies to the replacement coordinates.
        return {monomial: value for monomial, value in result.items() if 14 not in monomial}

    source = dict(original)
    for name in ('cap', 'middle', 'areas'):
        source[name] = [substitute(polynomial) for polynomial in original[name]]
    for name in ('brackets', 'positive'):
        source[name] = {key: substitute(polynomial) for key, polynomial in original[name].items()}
    source['P'] = [tuple(substitute(coordinate) for coordinate in point) for point in original['P']]
    # P3-P2 = (sum d,0), and all three upper cap equations vanish
    # identically after the exact order-b gauge substitution.
    assert all(not polynomial for polynomial in source['cap'][:3])
    return source


def strict_bracket(quad):
    return {0, 6, 7} <= set(quad) or quad in ((1, 2, 6, 7), (2, 3, 6, 7))


def strict_factor(tag):
    if tag[0] == 'd':
        return tag[1] in (6, 7) and tag[2] in (6, 7)
    if tag[0] == 'norm':
        return tag[1:] in ((1, 2), (1, 3), (2, 3), (1, 6), (1, 7), (6, 7))
    return tag[0] == 'mass'


def verify_identity(certificate):
    source = gauge_source()
    word = tuple(certificate['word'])
    assert len(word) == 70 and set(word) <= {-1, 1}
    signs = dict(zip(general.QUADS, word))
    residual = defaultdict(int)
    required, seen, witnesses = {}, set(), []
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
            if strict_bracket(quad) and strict_factor(tag):
                witnesses.append([list(quad), sign, list(tag), height])
            counts['positive_terms'] += 1
        else:
            raise AssertionError(('unknown term type', kind))
        for monomial, value in polynomial.items():
            assert sum(index < 20 for index in monomial) == 4
            assert sum(index >= 20 for index in monomial) == 2
            assert 14 not in monomial
            residual[monomial] += weight*value
    assert witnesses, 'no separately proved strict residual'
    assert not any(residual.values()), 'nonzero full-coordinate residual'
    return {**counts, 'strict_witnesses': witnesses,
            'required_signs': [[list(quad), sign] for quad, sign in sorted(required.items())],
            'expanded_coordinate_monomials': len(residual),
            'max_weight_bits': max(abs(int(record[-1])).bit_length() for record in certificate['terms'])}


def actual_source():
    model = boundary.ActualModel('1_between_2_3', 1, boundary.height_relations())
    model.clauses.extend([[model.bits((2, 3, 6, 7))[0]],
                          [model.bits((1, 2, 6, 7))[1]],
                          [-model.bits((0, 2, 3, 7))[1]],
                          [-model.bits((2, 3, 4, 5))[0]],
                          [-model.bits((4, 5, 6, 7))[0]]])
    return model


def build(directory=None, data_path=DATA):
    data = json.loads(Path(data_path).read_text())
    assert data['format'] == 1 and data['collinear_case'] == '1_between_2_3'
    assert data['zero_deficits'] == [2]
    inherited = general.verify()
    identities = [verify_identity(certificate) for certificate in data['certificates']]
    model = actual_source()
    permutation = tuple((1-i) % 8 for i in range(8))
    old_count = 0
    for reflected in (False, True):
        for certificate in inherited['certificates']:
            cap = 'upper' if reflected else 'lower'
            if not certificate['one_cap_strict_witnesses'][cap]:
                continue
            model.clauses.append([model.bits(tuple(permutation[i] for i in quad)
                                             if reflected else tuple(quad), -sign)[0]
                                  for quad, sign in certificate['required_signs']])
            old_count += 1
    assert old_count == 23
    for identity in identities:
        model.clauses.append([model.bits(tuple(quad), -sign)[0]
                              for quad, sign in identity['required_signs']])
    with FastSAT(model.n, model.clauses) as solver:
        status = solver.check()
    result = {'inherited_source_checks': inherited['source_checks'],
              'certificate_count': len(identities), 'certificates': identities,
              'inherited_one_cap_implications': old_count,
              'uncovered_source_satisfiable': status == 1,
              'actual_zeros_retained': True,
              'numerical_solver_used_for_replay': False,
              'complete_upper_b_interior_exclusion_after_independent_replay': status == -1}
    assert status in (-1, 1)
    if directory is not None:
        directory.mkdir(parents=True, exist_ok=True)
        if status == -1:
            filename = 'c0_upper_b_quartic_complete_cover.cnf'
            write_cnf(directory/filename, model.n, model.clauses)
            result['coverage_obligation'] = filename
        (directory/'c0_upper_b_quartic.json').write_text(json.dumps(result, indent=2)+'\n')
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
                      'complete_source_cover': not result['uncovered_source_satisfiable'],
                      'seconds': time.monotonic()-started}))
