#!/usr/bin/env python3
"""The forced first-width profile in the positive-axial ray-1 endpoint.

Usage: python remaining_ray1_positive_z_profile.py [--produce OUTPUT]

Checks the vertex6 polarizations in the actual face027 gauge, then
replays rational Farkas implications d=0 => c=e<=0 for all surviving
positive-axial cones. The companion note supplies the uniform bounds.
"""

import argparse
from fractions import Fraction
import json
from pathlib import Path
import time

import sympy as s

import exhaustive_remaining_axis as axis
import solver_remaining_virtual12_consequences as source

virtual = source.source
DEFAULT_DATA = Path(__file__).with_suffix('.json')
TARGETS = (virtual.C-virtual.E, virtual.E-virtual.C, -virtual.C)


def source_data():
    packet, words, digest = source.source_data()
    source.verify(json.loads(source.DEFAULT_DATA.read_text()), packet, words, digest)
    return packet, words, digest


def groups(packet, words):
    scenario = 'positive_z_boundary'
    for index, ((rows, signs), record) in enumerate(zip(
            virtual.groups(words, scenario), packet['scenarios'][scenario])):
        assert list(signs) == record['signs']
        if record['satisfiable_relaxation']:
            # The metric lemma supplies d=0. Both signs of this equality
            # are genuine nonnegative rows, not strict inequalities.
            rows = tuple(sorted(set(rows+(virtual.primitive_row(virtual.D),
                                          virtual.primitive_row(-virtual.D))),
                                key=virtual.row_key))
            yield index, rows, signs


def produce(packet, words, digest):
    import numpy as np
    from scipy.optimize import linprog
    records = []
    for index, rows, signs in groups(packet, words):
        matrix = s.Matrix(rows).T
        certificates = []
        for target in TARGETS:
            target_row = virtual.primitive_row(target)
            result = linprog(np.ones(matrix.cols), A_eq=np.array(matrix).astype(float),
                             b_eq=np.array(target_row, dtype=float), bounds=(0, None),
                             method='highs')
            assert result.success
            support = [i for i, value in enumerate(result.x) if value > 1e-9]
            weights, parameters = matrix[:, support].gauss_jordan_solve(s.Matrix(target_row))
            assert parameters.rows == 0 and all(weight >= 0 for weight in weights)
            assert matrix[:, support]*weights == s.Matrix(target_row)
            certificates.append({'target': str(target),
                                 'weights': [[i, str(weight)] for i, weight in zip(support, weights)]})
        records.append({'group': index, 'signs': list(signs), 'certificates': certificates})
    return {'source_sha256': digest, 'records': records}


def verify(data, packet, words, digest):
    assert data['source_sha256'] == digest
    expected = list(groups(packet, words))
    assert len(data['records']) == len(expected) == 5
    count = 0
    for record, (index, rows, signs) in zip(data['records'], expected):
        assert record['group'] == index and record['signs'] == list(signs)
        assert len(record['certificates']) == len(TARGETS)
        for certificate, target in zip(record['certificates'], TARGETS):
            assert certificate['target'] == str(target)
            support = [entry[0] for entry in certificate['weights']]
            assert len(support) == len(set(support)) and all(0 <= i < len(rows) for i in support)
            weights = [s.Rational(str(Fraction(entry[1]))) for entry in certificate['weights']]
            assert all(weight >= 0 for weight in weights)
            target_row = virtual.primitive_row(target)
            for column in range(5):
                assert sum(weight*rows[i][column] for i, weight in zip(support, weights)) == target_row[column]
            count += 1
    assert count == 15
    assert sum(len(signs) for _, _, signs in expected) == 172

    # With max(|c|,|d|,|e|)=1, d=0,c=e<=0 force(-1,0,-1).
    substitution = {virtual.C: -1, virtual.D: 0, virtual.E: -1, virtual.Y: 0}
    macro = {i: virtual.bracket(quad).subs(substitution) for i, quad in enumerate(virtual.QUADS)}
    leading = {i: value.subs(substitution) for i, value in
               virtual.virtual_brackets(s.Integer(0), s.Integer(2)).items()}
    candidates = sorted(word for _, _, signs in expected for word in signs)
    fixed = [word for word in candidates if all(value == 0 or bool(value > 0) == (word[i] == '+')
              for i, value in list(macro.items())+list(leading.items()))]
    assert len(fixed) == len(set(fixed)) == 100
    return {'exact_farkas_implications': count, 'positive_axial_words': len(candidates),
            'fixed_profile_words': len(fixed), 'profile': '(-1,0,-1)',
            'implication': 'd=0 implies c=e<=0'}


def metric_checks():
    shifts, faces, edges = axis.case_data(1)
    assert all(edge in edges for edge in ((0, 1), (0, 6), (0, 7), (1, 6), (6, 7)))
    assert shifts[0, 6] == shifts[1, 6] == (0, 0)
    assert shifts[6, 7] == (-1, 0)
    assert any(set(face) == {0, 2, 7} for face in faces)
    half = s.Rational(1, 2)
    t, d0, d6, d7, v1, v7, u = s.symbols('t d0 d6 d7 v1 v7 u')
    h0, h6, h7, r = half-d0, half-d6, half-d7, d6+d7
    assert s.expand(h7+r-1+h6) == 0
    assert s.expand((h0*h0+r*r-(h0-r)**2)/2-h0*r) == 0
    c67 = (r*r+h7*h7-h6*h6)/2

    sigma, q, u6, lam, w1, w6 = s.symbols('sigma q U6 lambda6 W1 W6')
    dot016 = t*((h0+sigma)*u6+w1*w6)+(v1+t*q)*(u+t*lam)
    target016 = t*h0*r+v1*u
    row016 = (h0+sigma)*u6+(v1+t*q)*lam+q*u+w1*w6-h0*r
    assert s.expand(dot016-target016-t*row016) == 0
    dot067 = t*h7*u6+v7*(u+t*lam)
    target067 = t*c67+v7*u
    row067 = h7*u6+v7*lam-c67
    assert s.expand(dot067-target067-t*row067) == 0
    determinant = (h0+sigma)*v7-h7*(v1+t*q)
    assert determinant.subs({d0: 0, d7: 0, sigma: 0, v1: half, v7: 0, t: 0}) == -s.Rational(1, 4)
    norm06 = t*(u6*u6+w6*w6)+(u+t*lam)**2-(t*r*r+u*u)
    assert s.expand(norm06-t*(u6*u6+w6*w6+2*u*lam+t*lam*lam-r*r)) == 0

    # Unit normal to face027 in the original axis frame. Its numerator
    # is Z-a*P-b*zeta; the unit factor is sqrt(1+a^2+t*b^2).
    p2, p7, n2, n7, z2, z7 = s.symbols('P2 P7 Z2 Z7 zeta2 zeta7')
    denominator = p7*z2-p2*z7
    a = (n7*z2-n2*z7)/denominator
    b = (p7*n2-p2*n7)/denominator
    assert s.cancel(a*p2+b*z2-n2) == 0
    assert s.cancel(a*p7+b*z7-n7) == 0
    assert denominator.subs({p2: 0, p7: half, z2: half, z7: 0}) == s.Rational(1, 4)
    return {'vertex6_rows': [str(row016), str(row067)],
            'determinant_limit': '-1/4',
            'normal06': 'W6^2=r^2-U6^2-2*u*lambda6-t*lambda6^2',
            'plane_normal_numerator': 'Z-a*P-b*zeta',
            'plane_coefficients': {'a': str(a), 'b': str(b)},
            'uniform_conclusion': 'W6=o(delta), hence d=0'}


def exact_checks(data_path=DEFAULT_DATA):
    packet, words, digest = source_data()
    result = verify(json.loads(Path(data_path).read_text()), packet, words, digest)
    result['metric_identities'] = metric_checks()
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--produce', type=Path)
    args = parser.parse_args()
    start = time.monotonic()
    if args.produce:
        packet, words, digest = source_data()
        data = produce(packet, words, digest)
        args.produce.write_text(json.dumps(data, separators=(',', ':'))+'\n')
        result = verify(data, packet, words, digest)
        result['metric_identities'] = metric_checks()
    else:
        result = exact_checks()
    result['seconds'] = round(time.monotonic()-start, 3)
    print(json.dumps(result), flush=True)


if __name__ == '__main__':
    if not __debug__:
        raise RuntimeError('run with assertions enabled')
    main()
