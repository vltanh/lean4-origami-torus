#!/usr/bin/env python3
"""Exact forced profiles in two surviving endpoint virtual-edge cones.

Usage: python solver_remaining_virtual12_consequences.py [--produce OUTPUT]

Replays the frozen virtual12 packet before checking 17 nonnegative row
combinations. The optional LP is only a producer, never a replay dependency.
"""

import argparse
from fractions import Fraction
import hashlib
import json
from pathlib import Path
import time

import sympy as sym

import solver_remaining_virtual12 as source

TARGETS = {
    'negative_x_boundary': (source.C-source.E, source.E-source.C,
                            source.D, -source.D, source.Y, -source.Y, source.C),
    'positive_z_boundary': (source.Y, -source.Y),
}
DEFAULT_DATA = Path(__file__).with_suffix('.json')


def source_data():
    raw = source.DEFAULT_DATA.read_bytes()
    packet = json.loads(raw)
    words = tuple(sorted(map(source.word, source.endpoint.endpoint_primary_models())))
    source.verify(packet, words)
    return packet, words, hashlib.sha256(raw).hexdigest()


def surviving_groups(packet, words):
    for scenario, targets in TARGETS.items():
        groups = source.groups(words, scenario)
        for index, ((rows, signs), record) in enumerate(zip(groups, packet['scenarios'][scenario])):
            assert list(signs) == record['signs']
            if record['satisfiable_relaxation']:
                yield scenario, index, rows, signs, targets


def produce(packet, words, digest):
    import numpy as np
    from scipy.optimize import linprog
    records = []
    for scenario, index, rows, signs, targets in surviving_groups(packet, words):
        matrix = sym.Matrix(rows).T
        certificates = []
        for target in targets:
            target_row = source.primitive_row(target)
            result = linprog(np.ones(matrix.cols), A_eq=np.array(matrix).astype(float),
                             b_eq=np.array(target_row, dtype=float), bounds=(0, None), method='highs')
            assert result.success
            support = [i for i, weight in enumerate(result.x) if weight > 1e-9]
            weights, parameters = matrix[:, support].gauss_jordan_solve(sym.Matrix(target_row))
            assert parameters.rows == 0 and all(weight >= 0 for weight in weights)
            assert matrix[:, support]*weights == sym.Matrix(target_row)
            certificates.append({'target': str(target),
                                 'weights': [[i, str(weight)] for i, weight in zip(support, weights)]})
        records.append({'scenario': scenario, 'group': index, 'signs': list(signs),
                        'certificates': certificates})
    return {'source_sha256': digest, 'records': records}


def verify(data, packet, words, digest):
    assert data['source_sha256'] == digest
    expected = list(surviving_groups(packet, words))
    assert len(data['records']) == len(expected) == 6
    count = 0
    for record, (scenario, index, rows, signs, targets) in zip(data['records'], expected):
        assert record['scenario'] == scenario and record['group'] == index
        assert record['signs'] == list(signs)
        assert len(record['certificates']) == len(targets)
        for certificate, target in zip(record['certificates'], targets):
            assert certificate['target'] == str(target)
            support = [entry[0] for entry in certificate['weights']]
            assert len(support) == len(set(support)) and all(0 <= i < len(rows) for i in support)
            weights = [sym.Rational(str(Fraction(entry[1]))) for entry in certificate['weights']]
            assert all(weight >= 0 for weight in weights)
            target_row = source.primitive_row(target)
            for column in range(5):
                assert sum(weight*rows[i][column] for i, weight in zip(support, weights)) == target_row[column]
            count += 1
    assert count == 17
    return {'exact_nonnegative_row_combinations': count, 'surviving_groups': len(expected),
            'negative_x_boundary': 'c=e>=0, d=aY=0; normalized profile is (1,0,1,0)',
            'positive_z_boundary': 'aY=0', 'endpoint_exclusion': False}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--produce', type=Path)
    args = parser.parse_args()
    start = time.monotonic()
    packet, words, digest = source_data()
    if args.produce:
        data = produce(packet, words, digest)
        args.produce.write_text(json.dumps(data, separators=(',', ':'))+'\n')
    else:
        data = json.loads(DEFAULT_DATA.read_text())
    result = verify(data, packet, words, digest)
    result['seconds'] = round(time.monotonic()-start, 3)
    print(json.dumps(result), flush=True)


if __name__ == '__main__':
    if not __debug__:
        raise RuntimeError('run with assertions enabled')
    main()
