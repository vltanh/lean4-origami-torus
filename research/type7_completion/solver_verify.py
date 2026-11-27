#!/usr/bin/env python3
"""Independent exact replay of a solver_chambers.py manifest.

Usage: python solver_verify.py OUTPUT_DIRECTORY

The separate solver_check_rup.cpp must also accept coverage.cnf and
coverage.drat to certify enumeration completeness independently of Z3.
This script checks every listed primary model directly, every symmetry,
each strictness witness, every omitted circuit, and the metric reductions.
It does not run an undecided nonlinear query or assert a marking exclusion.
"""

from collections import Counter
from fractions import Fraction as F
from itertools import combinations
import json
from pathlib import Path
import sys

import sympy as sym

import solver_chambers as producer
import solver_final_polynomials
import solver_metric_certificates
from verify_linking import lk, short_pairs


def main(directory):
    source = json.loads((directory / 'chambers.json').read_text())
    models = {tuple(1 if value == '+' else -1 for value in text)
              for text in source['all_models']}
    assert len(models) == len(source['all_models']) == 1888
    assert all(len(m) == 70 and m[0] == 1 for m in models)
    n, clauses, faces, edges, neighbors = producer.base_formula()
    # Bind the independently checked UNSAT trace to this exact manifest.
    # An unrelated UNSAT CNF would not certify this model enumeration.
    cnf_lines = (directory / 'coverage.cnf').read_text().splitlines()
    header = cnf_lines.pop(0).split()
    expected = clauses + [[-(i + 1) * value for i, value in enumerate(model)]
                          for model in models]
    assert header == ['p', 'cnf', str(n), str(len(expected))]
    parsed = []
    for line in cnf_lines:
        row = list(map(int, line.split()))
        assert row and row[-1] == 0 and all(0 < abs(v) <= n for v in row[:-1])
        parsed.append(tuple(sorted(row[:-1])))
    assert Counter(parsed) == Counter(tuple(sorted(row)) for row in expected)
    simplices = {(i,) for i in range(8)} | edges | set(faces)
    initial_strict = {q for q in producer.Q if set(combinations(q, 2)) <= edges}
    _, shifts, undirected, xb, yb, kx, ky = producer.direct.load_data()

    def sign(model, q):
        parity = (-1) ** sum(a > b for i, a in enumerate(q) for b in q[i + 1:])
        return parity * model[producer.QI[tuple(sorted(q))]]

    def linking(model, a, b):
        return sum(lk((a[0], a[i], a[i + 1]), b, model) for i in range(1, len(a) - 1))

    # Evaluate the primary constraints and the meaning of the auxiliary
    # existential tests, independently of auxiliary SAT assignments.
    for model in models:
        assert all(any(model[abs(v) - 1] == (1 if v > 0 else -1) for v in clause)
                   for clause in clauses if all(abs(v) <= 70 for v in clause))
        for vertex in range(8):
            assert any(len({sign(model, tri + (w,)) for w in neighbors[vertex] - set(tri)}) == 2
                       for tri in faces if vertex in tri)
        assert all(linking(model, a, b) == 0 for a, b in short_pairs(shifts))
        assert abs(linking(model, (0, 2, 4, 6), (1, 3, 5, 7))) == 2

    # A^T Q A = Q for Q = Q0 + y^2 Q1 is exact at every y.
    forms = (((F(1), F(1, 2)), (F(1, 2), F(1, 4))),
             ((F(0), F(0)), (F(0), F(1))))
    face_set = {tuple(sorted(f)) for f in faces}
    phase = []
    for entry in source['symmetries']:
        p, matrix, gauge = entry['permutation'], entry['matrix'], entry['gauge']
        assert sorted(p) == list(range(8))
        assert {tuple(sorted(p[v] for v in f)) for f in face_set} == face_set
        for form in forms:
            assert [[sum(matrix[k][i] * form[k][l] * matrix[l][j]
                         for k in range(2) for l in range(2))
                     for j in range(2)] for i in range(2)] == [list(row) for row in form]
        for i, j in undirected:
            assert shifts[p[i], p[j]] == tuple(
                sum(matrix[k][l] * shifts[i, j][l] for l in range(2))
                + gauge[j][k] - gauge[i][k] for k in range(2))
        preserves_phase = frozenset(frozenset(p[v] for v in cap)
                                   for cap in producer.CAPS) == producer.CAPS
        assert preserves_phase == entry['phase_preserving']
        if preserves_phase:
            phase.append(p)
    assert len(source['symmetries']) == 32 and len(phase) == 16
    assert len({tuple(p) for p in phase}) == 16
    assert all(tuple(p[q[i]] for i in range(8)) in {tuple(s) for s in phase}
               for p in phase for q in phase)

    covered = set()
    total_witnesses = total_omitted = 0
    final_polynomial_excluded = []
    metric_excluded = []
    solver_metric_certificates.symbolic_checks()
    partitions = producer.circuit_partitions(faces, edges)
    for row in source['chambers']:
        model = tuple(1 if value == '+' else -1 for value in row['signs'])
        assert model in models
        for p in phase:
            mapped = tuple(sign(model, tuple(p[v] for v in q)) for q in producer.Q)
            mapped = tuple(v * mapped[0] for v in mapped)
            assert mapped in models
            covered.add(mapped)
        strict = set(initial_strict)
        for witness in row['trace']:
            kind, q, *rest = witness
            q = tuple(q)
            assert q not in strict
            if kind == 'cofactor':
                w, known = rest
                support = tuple(sorted(q + (w,)))
                assert w not in q and tuple(known) in strict
                assert set(known) < set(support) and tuple(known) != q
                cofactors = {v: (-1)**i * sign(model, support[:i] + support[i + 1:])
                             for i, v in enumerate(support)}
                positive = tuple(v for v in q if cofactors[v] > 0)
                negative = tuple(v for v in q if cofactors[v] < 0)
                forbidden = (not positive or not negative
                             or (positive in simplices and negative in simplices)
                             or (len(positive) == 1 and set(negative) <= neighbors[positive[0]])
                             or (len(negative) == 1 and set(positive) <= neighbors[negative[0]]))
                assert forbidden
            elif kind == 'gp':
                common, others, positive, right = rest
                common = tuple(common)
                a, b, c, d = others
                pairs = ((common + (a, b), common + (c, d)),
                         (common + (a, c), common + (b, d)),
                         (common + (a, d), common + (b, c)))
                signs = [(-1)**i * sign(model, u) * sign(model, v)
                         for i, (u, v) in enumerate(pairs)]
                assert signs[right] == -sum(signs) and positive != right
                assert all(tuple(sorted(v)) in strict for v in pairs[positive])
                assert q in {tuple(sorted(v)) for v in pairs[right]}
            else:
                raise AssertionError(kind)
            strict.add(q)
            total_witnesses += 1
        assert strict == {tuple(map(int, q)) for q in row['strict']}
        if 'final_polynomial' in row:
            certificate = solver_final_polynomials.verify(model, strict)
            assert certificate is not None
            assert json.loads(json.dumps(certificate)) == row['final_polynomial']
            final_polynomial_excluded.append(row['id'])
        if 'metric_certificate' in row:
            certificate = solver_metric_certificates.verify(model, source['symmetries'])
            assert certificate is not None
            assert json.loads(json.dumps(certificate)) == row['metric_certificate']
            permutation = certificate['permutation']
            clique = tuple(sorted(permutation[v] for v in certificate['strict_clique']))
            assert clique in initial_strict
            metric_excluded.append(row['id'])
        retained = {(tuple(a), tuple(b)) for a, b in row['remaining_circuits']}
        expected_retained = set()
        for support, positive in partitions:
            if len(support) == 5:
                signs = [(-1)**i * sign(model, support[:i] + support[i + 1:])
                         * (1 if v in positive else -1) for i, v in enumerate(support)]
                assert len(set(signs)) == 2
            elif not any(set(support) <= set(q) for q in strict):
                expected_retained.add((support, positive))
        assert expected_retained == retained
        assert all(len(s) == 4 for s, _ in retained)
        total_omitted += len(partitions) - len(retained)
    assert len(source['chambers']) == 132 and covered == models
    if final_polynomial_excluded:
        assert final_polynomial_excluded == [23, 131]
    if metric_excluded:
        assert metric_excluded == [129, 130, 131]
    excluded = sorted(set(final_polynomial_excluded) | set(metric_excluded))
    if final_polynomial_excluded and metric_excluded:
        assert excluded == [23, 129, 130, 131]

    x = [0] + list(sym.symbols('x1:8'))
    gamma = [0] + list(sym.symbols('gamma1:8'))
    t = sym.Symbol('t')
    X = lambda i, j: x[j] - x[i] + kx[i, j]
    Y = lambda i, j: ky[i, j] + t * (gamma[j] - gamma[i])
    oriented_faces = producer.direct.load_data()[0]
    assert sym.expand(sum(X(a, b) * Y(a, c) - X(a, c) * Y(a, b)
                          for a, b, c in oriented_faces)) == -2
    selected = {}
    for cap in (producer.direct.p.CAP_A, producer.direct.p.CAP_B):
        assert sum(kx[i, j] for i, j in producer.direct.p.ring_edges(cap)) == -1
        assert all(ky[i, j] == 0 for i, j in producer.direct.p.ring_edges(cap))
        for k in (0, 1):
            i, middle, j = cap[k:k + 3]
            b = yb[i] - yb[j]
            a = kx[i, middle] + kx[middle, j] - xb[j] + xb[i] - b / 2
            assert a.denominator == b.denominator == 1
            assert sym.expand(X(i, middle) + X(middle, j)
                              - (x[j] - x[i] + xb[j] - xb[i] + a + b/2)) == 0
            selected[f'{i}{j}'] = ((int(a), int(b)), (int(a + 1), int(b)))
    assert selected == {'04': ((0, 0), (1, 0)), '15': ((-1, 0), (0, 0)),
                        '26': ((0, -1), (1, -1)), '37': ((-1, 0), (0, 0))}
    # Uniform lower bound for the discarded nonzero-vertical images:
    # y^2 - 2|g| - 1/4 > 64 - (1/2+1/64) - 1/4 > 0.
    assert F(64) - (F(1, 2) + F(1, 64)) - F(1, 4) > 0
    print(f'PASS 1888 primary models, 32 marked symmetries, 132 phase chambers; '
          f'{total_witnesses} strictness witnesses and {total_omitted} omitted circuit tests replayed')
    print('PASS exact total-area identity and eight retained nearest-image inequalities')
    if final_polynomial_excluded:
        print('PASS exact final-polynomial exclusions of weak chambers 23 and 131')
    if metric_excluded:
        print('PASS exact raw-bracket metric exclusions of weak chambers 129, 130, 131 for y>=8')
    if excluded:
        print(f'PASS {len(excluded)} complete weak chambers excluded; {132 - len(excluded)} remain')
    print('Completeness additionally requires the independent RUP replay; no full marking exclusion is claimed.')


if __name__ == '__main__':
    if not __debug__:
        raise RuntimeError('run with assertions enabled')
    if len(sys.argv) != 2:
        raise SystemExit(__doc__)
    main(Path(sys.argv[1]))
