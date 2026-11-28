#!/usr/bin/env python3
"""Optional bounded LP producer for uniform regular-C0 quartic identities.

Example:
  python solver_remaining_c0_quartic_discover.py SOURCE.json 0 RESULT.json

SOURCE.json must contain a `remaining_words` list of complete 70-sign words.
Discovery needs numpy, scipy, highspy, sympy and python-flint. These optional
dependencies are not used by the independent certificate replay.
"""

import argparse
from itertools import combinations, combinations_with_replacement
import json
from pathlib import Path
import time

import solver_remaining_c0_quartic as replay


def coordinate_projection():
    """Exact 210-coordinate projection of planar dot-times-area quartics."""
    from sympy import ZZ
    from sympy.polys.matrices import DomainMatrix

    P = replay.polynomial_source()['P'][2:]
    polynomials = [replay.multiply(replay.dot(P[i], P[j]), replay.cross(P[k], P[l]))
                   for i, j in combinations_with_replacement(range(6), 2)
                   for k, l in combinations(range(6), 2)]
    monomials = sorted({m for polynomial in polynomials for m in polynomial})
    index = {m: i for i, m in enumerate(monomials)}
    matrix = DomainMatrix({i: {index[m]: value for m, value in polynomial.items()}
                           for i, polynomial in enumerate(polynomials)},
                          (len(polynomials), len(monomials)), ZZ)
    _, pivots = matrix.to_field().rref()
    planar = [monomials[i] for i in pivots]
    assert len(planar) == 210
    mixed = [tuple(sorted((2*i, 2*j+1, 12+k, 12+l)))
             for i, j in combinations(range(6), 2)
             for k, l in combinations_with_replacement(range(8), 2)]
    assert len(mixed) == len(set(mixed)) == 540
    heights = tuple(combinations_with_replacement(replay.HEIGHTS, 2))
    return sorted(tuple(sorted(monomial+height))
                  for monomial in planar+mixed for height in heights)


def build_system(word, extra_squares=False):
    import numpy as np
    from scipy.sparse import coo_matrix

    assert len(word) == 70 and set(word) <= {-1, 1}
    source = replay.polynomial_source()
    monomials = coordinate_projection()
    index = {m: i for i, m in enumerate(monomials)}
    polynomials, tags, strict = [], [], []
    heights = tuple(combinations_with_replacement(replay.HEIGHTS, 2))
    for i, equation in enumerate(source['cap']):
        for j, area in enumerate(source['areas']):
            for height in heights:
                polynomials.append(replay.multiply(equation, area, {height: 1}))
                tags.append(['cap', i, j, height])
                strict.append(False)
    for i, equation in enumerate(source['middle']):
        for j, area in enumerate(source['areas']):
            polynomials.append(replay.multiply(equation, area))
            tags.append(['middle', i, j])
            strict.append(False)
    free_count = len(tags)
    factor_groups = [dict(source['positive'])]
    if extra_squares:
        extra = {}
        for i, j in combinations(range(2, 8), 2):
            vector = replay.vector_sum((source['P'][i], 1), (source['P'][j], 1))
            extra['plusnorm', i, j] = replay.dot(vector, vector)
        factor_groups.append(extra)
    for factors in factor_groups:
        for q, sign in zip(replay.QUADS, word):
            for tag, factor in factors.items():
                for height in replay.HEIGHTS:
                    polynomial = replay.multiply(source['brackets'][q], factor, replay.variable(height))
                    polynomials.append(replay.linear((polynomial, sign)))
                    tags.append(['positive', q, sign, tag, height])
                    strict.append(replay.strict_bracket(q) and replay.strict_factor(tag))
    rows, cols, values = [], [], []
    for column, polynomial in enumerate(polynomials):
        for monomial, value in polynomial.items():
            if monomial in index:
                rows.append(index[monomial]); cols.append(column); values.append(value)
        if strict[column]:
            rows.append(len(monomials)); cols.append(column); values.append(1)
    matrix = coo_matrix((np.asarray(values, dtype=float), (rows, cols)),
                        shape=(len(monomials)+1, len(tags))).tocsc()
    rhs = np.zeros(matrix.shape[0]); rhs[-1] = 1
    return {'matrix': matrix, 'rhs': rhs, 'tags': tags, 'free_count': free_count,
            'polynomials': polynomials, 'word': list(word)}


def discover(system, seconds):
    import highspy
    import numpy as np

    matrix, rhs, n = system['matrix'], system['rhs'], system['free_count']
    columns = matrix.shape[1]
    solver = highspy.Highs()
    for key, value in (('output_flag', False), ('threads', 1),
                       ('solver', 'ipm'), ('time_limit', seconds)):
        solver.setOptionValue(key, value)
    model = highspy.HighsLp()
    model.num_col_, model.num_row_ = columns, matrix.shape[0]
    # Feasibility is the objective. Minimizing the certificate size before
    # finding a feasible support was substantially slower on this system.
    model.col_cost_ = np.zeros(columns)
    model.col_lower_ = np.r_[np.full(n, -highspy.kHighsInf), np.zeros(columns-n)]
    model.col_upper_ = np.full(columns, highspy.kHighsInf)
    model.row_lower_, model.row_upper_ = rhs, rhs
    model.a_matrix_.format_ = highspy.MatrixFormat.kColwise
    model.a_matrix_.start_, model.a_matrix_.index_, model.a_matrix_.value_ = (
        matrix.indptr, matrix.indices, matrix.data)
    solver.passModel(model)
    started = time.monotonic(); solver.run()
    status = solver.getModelStatus()
    report = {'backend': solver.version(), 'status': str(status),
              'seconds': time.monotonic()-started,
              'ipm_iterations': solver.getInfo().ipm_iteration_count,
              'rows': matrix.shape[0], 'columns': matrix.shape[1]}
    if status != highspy.HighsModelStatus.kOptimal:
        return None, report
    values = np.asarray(solver.getSolution().col_value)
    report['numerical_residual'] = float(max(abs(matrix@values-rhs)))
    return values, report


def reconstruct(system, approximate):
    from fractions import Fraction
    from math import gcd, lcm
    from flint import fmpq_mat
    import numpy as np
    from scipy.linalg import qr

    started = time.monotonic()
    support = np.flatnonzero(abs(approximate) > 1e-8)
    matrix = system['matrix'][:, support].toarray()
    _, triangular, pivots = qr(matrix.T, mode='economic', pivoting=True)
    rank = sum(abs(np.diag(triangular)) > 1e-9)
    if rank != len(support):
        raise ValueError('numerical candidate has no full-rank active basis')
    rows = pivots[:rank]
    selected = matrix[rows]
    assert np.max(abs(selected-np.rint(selected))) == 0
    selected = selected.astype(np.int64)
    rhs = system['rhs'][rows].astype(np.int64)
    exact = fmpq_mat(rank, rank, [int(value) for value in selected.ravel()])
    solution = exact.solve(fmpq_mat(rank, 1, list(map(int, rhs))), algorithm='dixon')
    weights = [Fraction(int(value.p), int(value.q)) for value in solution.entries()]
    assert all(weight >= 0 for index, weight in zip(support, weights)
               if index >= system['free_count'])
    denominator = lcm(*(weight.denominator for weight in weights))
    integers = [int(weight*denominator) for weight in weights]
    divisor = gcd(*integers)
    integers = [weight//divisor for weight in integers]
    certificate = {'word': system['word'],
                   'terms': [[*system['tags'][int(index)], str(weight)]
                             for index, weight in zip(support, integers) if weight]}
    # This expands every coordinate monomial, including every row omitted
    # by discovery's projection. Approximate support/basis choices are
    # therefore not trusted by acceptance.
    verified = replay.verify_identity(certificate)
    return certificate, {'seconds': time.monotonic()-started, **verified}


if __name__ == '__main__':
    if not __debug__:
        raise RuntimeError('run with assertions enabled')
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('source', type=Path)
    parser.add_argument('word_index', type=int)
    parser.add_argument('output', type=Path)
    parser.add_argument('--seconds', type=float, default=30.0)
    parser.add_argument('--extra-squares', action='store_true')
    args = parser.parse_args()
    assert 0 < args.seconds <= 300
    words = json.loads(args.source.read_text())['remaining_words']
    system = build_system(words[args.word_index], args.extra_squares)
    approximate, report = discover(system, args.seconds)
    print(json.dumps({'discovery': report}), flush=True)
    if approximate is None:
        raise SystemExit('No exact certificate produced.')
    certificate, exact_report = reconstruct(system, approximate)
    packet = {'format': 1, 'certificates': [certificate],
              'discovery': report, 'exact_reconstruction': exact_report}
    args.output.write_text(json.dumps(packet, separators=(',', ':'))+'\n')
    print(json.dumps({'exact_identity_verified': True,
                      'terms': len(certificate['terms']),
                      'seconds': exact_report['seconds']}), flush=True)
