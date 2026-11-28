#!/usr/bin/env python3
"""Discover exact quadratic metric certificates in 490 quotient coordinates.

Usage: python solver_metric_cone.py MANIFEST_DIRECTORY OUTPUT_DIRECTORY
       [--case 55] [--coefficient 1/8] [--seconds 5]
       python solver_metric_cone.py MANIFEST_DIRECTORY --replay-candidate FILE

By default, try the manifest's unexcluded chambers.  Explicit --case
options also allow reproduction of already certified chambers.  LP is
only a bounded discovery step.  Every exported certificate is recovered
over exact rationals and independently checked by coordinate expansion.
The verifier modules do not import this optional NumPy/SciPy producer.
"""

import argparse
from collections import Counter, defaultdict
from fractions import Fraction as F
from itertools import combinations, combinations_with_replacement
import json
from math import gcd, lcm
from pathlib import Path
import time

import solver_chambers as compiler
import solver_metric_certificates as metric
import solver_metric_differences as differences
import solver_metric_quotient as replay

QUADS = metric.QUADS
QUAD_INDEX = metric.INDEX
PRODUCTS = tuple(combinations_with_replacement(range(70), 2))
PRODUCT_INDEX = {pair: i for i, pair in enumerate(PRODUCTS)}


def build_quotient():
    """Exact multigraded elimination; this is never trusted by replay."""
    import sympy as sym

    triples = tuple(combinations(range(1, 8), 3))
    triple_index = {q: i for i, q in enumerate(triples)}
    monomials = tuple(combinations_with_replacement(range(35), 2))
    monomial_index = {q: i for i, q in enumerate(monomials)}

    def degree(q):
        return tuple(sum(v in triples[i] for i in q) for v in range(1, 8))

    def bracket(q):
        if len(set(q)) != 3:
            return None, 0
        parity = (-1)**sum(a > b for i, a in enumerate(q) for b in q[i + 1:])
        return triple_index[tuple(sorted(q))], parity

    blocks = defaultdict(list)
    for i, q in enumerate(monomials):
        blocks[degree(q)].append(i)
    relations = defaultdict(set)
    for first in combinations(range(1, 8), 2):
        for second in combinations(range(1, 8), 4):
            row = Counter()
            for i, vertex in enumerate(second):
                left, parity = bracket(first + (vertex,))
                if parity:
                    right = triple_index[second[:i] + second[i + 1:]]
                    row[monomial_index[tuple(sorted((left, right)))]] += (-1)**i * parity
            row = replay.clean(row)
            if not row:
                continue
            leading = min(row)
            orientation = 1 if row[leading] > 0 else -1
            key = degree(monomials[leading])
            assert all(degree(monomials[i]) == key for i in row)
            relations[key].add(tuple(sorted((i, orientation*v) for i, v in row.items())))

    representation, free = {}, []
    for key, columns in blocks.items():
        rows = sorted(relations[key])
        local = {v: i for i, v in enumerate(columns)}
        matrix = sym.MutableSparseMatrix(len(rows), len(columns), {
            (i, local[j]): v for i, row in enumerate(rows) for j, v in row})
        reduced, pivots = matrix.rref()
        remaining = [i for i in range(len(columns)) if i not in pivots]
        free.extend(columns[i] for i in remaining)
        for i in remaining:
            representation[columns[i]] = {columns[i]: sym.Integer(1)}
        for row, pivot in enumerate(pivots):
            representation[columns[pivot]] = {
                columns[j]: -reduced[row, j] for j in remaining if reduced[row, j]}
    free = tuple(sorted(free))
    assert len(free) == 490 and max(map(len, blocks.values())) == 10
    free_index = {v: i for i, v in enumerate(free)}
    reduced_monomials = []
    for i in range(len(monomials)):
        row = representation[i]
        assert all(sym.denom(v) == 1 for v in row.values())
        reduced_monomials.append({free_index[j]: int(v) for j, v in row.items()})

    anchored = [{triple_index[q]: v for q, v in replay.anchored_form(quad).items()}
                for quad in QUADS]
    raw_products = []
    for a, b in PRODUCTS:
        row = Counter()
        for i, left in anchored[a].items():
            for j, right in anchored[b].items():
                for k, value in reduced_monomials[monomial_index[tuple(sorted((i, j)))]].items():
                    row[k] += left * right * value
        raw_products.append(replay.clean(row))
    assert sum(map(len, raw_products)) == 19411
    assert max(abs(v) for row in raw_products for v in row.values()) == 2
    return raw_products


def metric_products(model, symmetries, coefficient):
    """All nontrivial signed differences, times every raw magnitude."""
    rows, tags, seen = [], [], set()
    for permutation in metric.phase_permutations(symmetries):
        for pair in combinations((1, 4, 5), 2):
            for direction in (-1, 1):
                source = differences.metric_row(model, permutation, pair, direction, coefficient)
                linear = {QUAD_INDEX[q]: value for q, value in source.items() if value}
                key = tuple(sorted(linear.items()))
                if key in seen or all(value <= 0 for value in linear.values()):
                    continue
                seen.add(key)
                for multiplier in range(70):
                    rows.append({PRODUCT_INDEX[tuple(sorted((i, multiplier)))]: value
                                 for i, value in linear.items()})
                    tags.append((permutation, pair, direction, multiplier))
    return rows, tags


def sparse_matrix(rows, columns):
    from scipy.sparse import coo_matrix

    return coo_matrix(([float(v) for row in rows for v in row.values()],
                       ([i for i, row in enumerate(rows) for _ in row],
                        [j for row in rows for j in row])),
                      shape=(len(rows), columns)).tocsr()


def exact_remainder(weights, rows, model, basis):
    """Return the exact quotient remainder of metric sum minus positive sum."""
    count = len(rows)
    polynomial = Counter()
    for weight, row in zip(weights[:count], rows):
        if weight:
            for i, value in row.items():
                polynomial[i] += weight * value
    for i, value in enumerate(weights[count:]):
        polynomial[i] -= value
    remainder = Counter()
    for i, value in polynomial.items():
        if value:
            a, b = PRODUCTS[i]
            for j, coefficient in basis[i].items():
                remainder[j] += value * model[a] * model[b] * coefficient
    return replay.clean(remainder)


def reconstruct(values, rows, model, basis, strict_products, coefficient):
    """Use floating values only to suggest a support; solve that support exactly."""
    import sympy as sym

    count = len(rows)
    weights = [F(float(v)).limit_denominator(10**8) for v in values]
    if (min(weights) >= 0 and sum(weights[count+i] for i in strict_products) > 0
            and not exact_remainder(weights, rows, model, basis)):
        return weights, False
    # This threshold selects a proposed active support only.  The result
    # is accepted solely after exact equations and exact signs are checked.
    support = [i for i, value in enumerate(values) if value > 10**-10]
    if not support or len(support) > 491:
        raise ValueError('no small active support for exact reconstruction')
    matrix = {}
    denominator = coefficient.denominator
    for column, variable in enumerate(support):
        polynomial = rows[variable] if variable < count else {variable-count: F(-1)}
        reduced = Counter()
        for i, value in polynomial.items():
            a, b = PRODUCTS[i]
            for j, multiplier in basis[i].items():
                reduced[j] += value * model[a] * model[b] * multiplier
        for row, value in reduced.items():
            if value:
                assert (value * denominator).denominator == 1
                matrix[row, column] = int(value * denominator)
        if variable >= count and variable-count in strict_products:
            matrix[490, column] = 1
    system = sym.MutableSparseMatrix(491, len(support), matrix)
    solution, parameters = system.gauss_jordan_solve(sym.Matrix([0]*490 + [1]))
    if parameters.rows:
        solution = solution.subs({symbol: 0 for symbol in parameters})
    weights = [F(0)] * len(values)
    for i, value in zip(support, solution):
        weights[i] = F(int(sym.numer(value)), int(sym.denom(value)))
    if (min(weights) < 0 or sum(weights[count+i] for i in strict_products) <= 0
            or exact_remainder(weights, rows, model, basis)):
        raise ValueError('the proposed active support has no checked positive certificate')
    return weights, True


def make_certificate(chamber, model, rows, tags, weights, coefficient):
    denominator = lcm(*(weight.denominator for weight in weights))
    integers = [int(weight * denominator) for weight in weights]
    divisor = gcd(*integers)
    assert divisor > 0
    integers = [weight // divisor for weight in integers]
    count = len(rows)
    raw = Counter()
    for weight, row in zip(integers[:count], rows):
        if weight:
            for i, value in row.items():
                raw[i] += weight * value
    for i, value in enumerate(integers[count:]):
        raw[i] -= value
    scale = coefficient.denominator
    identity = {}
    for i, value in sorted(raw.items()):
        if value:
            a, b = PRODUCTS[i]
            value *= scale * model[a] * model[b]
            assert value.denominator == 1
            key = '*'.join(''.join(map(str, QUADS[q])) for q in (a, b))
            identity[key] = int(value)
    products = []
    for i, weight in enumerate(integers[:count]):
        if weight:
            permutation, pair, direction, multiplier = tags[i]
            products.append({'weight': scale*weight, 'source': (permutation, pair, direction),
                             'multiplier': QUADS[multiplier]})
    return {'reference_case': chamber, 'reference_signs': ''.join('+' if v > 0 else '-' for v in model),
            'coefficient': str(coefficient), 'metric_rows': products, 'raw_identity': identity}


def coordinate_check(certificate):
    """Independent from the discovery quotient and all LP arithmetic."""
    replay.validate_raw_expansions()
    anchored = Counter()
    for key, coefficient in certificate['raw_identity'].items():
        assert isinstance(coefficient, int) and not isinstance(coefficient, bool) and coefficient != 0
        a, b = replay.parse_product(key)
        for u, left in replay.anchored_form(a).items():
            for v, right in replay.anchored_form(b).items():
                anchored[tuple(sorted((u, v)))] += coefficient * left * right
    expanded = Counter()
    for (u, v), coefficient in anchored.items():
        for monomial, value in replay.anchor_product(u, v).items():
            expanded[monomial] += coefficient * value
    if any(expanded.values()):
        raise ValueError('independent coordinate identity replay failed')


def residual(certificate, model, phase):
    result = Counter()
    coefficient = F(certificate['coefficient'])
    for row in certificate['metric_rows']:
        permutation, pair, direction = row['source']
        assert tuple(permutation) in phase
        assert isinstance(row['weight'], int) and not isinstance(row['weight'], bool) and row['weight'] > 0
        multiplier = tuple(row['multiplier'])
        assert multiplier in QUAD_INDEX
        for q, value in differences.metric_row(model, tuple(permutation), tuple(pair),
                                               direction, coefficient).items():
            result[tuple(sorted((q, multiplier)))] += row['weight'] * value
    for key, value in certificate['raw_identity'].items():
        a, b = replay.parse_product(key)
        result[a, b] -= value * model[QUAD_INDEX[a]] * model[QUAD_INDEX[b]]
    return replay.clean(result)


def checked_coverage(certificate, chambers, symmetries, edges):
    """Every exported reuse gets a fresh exact nonnegative residual check."""
    coordinate_check(certificate)
    phase = metric.phase_permutations(symmetries)
    cliques = {q for q in QUADS if set(combinations(q, 2)) <= set(edges)}
    covered = []
    for row in chambers:
        model = tuple(1 if value == '+' else -1 for value in row['signs'])
        for permutation in phase:
            mapped = compiler.transformed_model(model, permutation)
            polynomial = residual(certificate, mapped, phase)
            if (polynomial and all(value >= 0 for value in polynomial.values())
                    and any(value > 0 and a in cliques and b in cliques
                            for (a, b), value in polynomial.items())):
                covered.append({'chamber': row['id'], 'signs': row['signs'],
                                'reference': certificate['reference_case'],
                                'permutation': permutation})
                break
    return covered


def replay_packet(path, chambers, symmetries, edges):
    """Proof-only replay of an exported packet, without importing an LP library."""
    packet = json.loads(path.read_text())
    certificates = {row['reference_case']: row for row in packet['certificates']}
    assert len(certificates) == len(packet['certificates'])
    assert set(certificates) == {row['reference'] for row in packet['coverage']}
    models = {row['id']: row['signs'] for row in chambers}
    phase = metric.phase_permutations(symmetries)
    cliques = {q for q in QUADS if set(combinations(q, 2)) <= set(edges)}
    for certificate in certificates.values():
        coordinate_check(certificate)
        replay.minimum_height(F(certificate['coefficient']))
    checked = set()
    for entry in packet['coverage']:
        assert entry['chamber'] not in checked and models[entry['chamber']] == entry['signs']
        assert len(entry['signs']) == 70 and set(entry['signs']) <= {'+', '-'}
        model = tuple(1 if value == '+' else -1 for value in entry['signs'])
        permutation = tuple(entry['permutation'])
        assert permutation in phase
        polynomial = residual(certificates[entry['reference']],
                              compiler.transformed_model(model, permutation), phase)
        assert polynomial and all(value >= 0 for value in polynomial.values())
        assert any(value > 0 and a in cliques and b in cliques
                   for (a, b), value in polynomial.items())
        checked.add(entry['chamber'])
    assert checked
    print(json.dumps({'status': 'independent exact replay passed', 'cases': sorted(checked),
                      'identities': len(certificates)}), flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('manifest', type=Path)
    parser.add_argument('output', type=Path, nargs='?')
    parser.add_argument('--replay-candidate', type=Path,
                        help='check an exported packet without importing NumPy or SciPy')
    parser.add_argument('--case', type=int, action='append', dest='cases')
    parser.add_argument('--coefficient', type=F, default=F(1, 8))
    parser.add_argument('--seconds', type=float, default=5,
                        help='wall-clock limit for each floating LP call, at most 60 seconds')
    parser.add_argument('--method', choices=('highs', 'highs-ds', 'highs-ipm'), default='highs')
    parser.add_argument('--feasibility', action='store_true', help='seek any certificate, without minimizing its weights')
    args = parser.parse_args()
    if args.coefficient <= 0 or not 0 < args.seconds <= 60:
        parser.error('coefficient must be positive, and seconds must lie in (0,60]')
    source = json.loads((args.manifest / 'chambers.json').read_text())
    if args.replay_candidate:
        metric.symbolic_checks()
        replay_packet(args.replay_candidate, source['chambers'], compiler.marked_symmetries(),
                      compiler.direct.load_data()[2])
        return
    if args.output is None:
        parser.error('an output directory is required for discovery')
    try:
        import numpy as np
        from scipy.optimize import linprog
        from scipy.sparse import csr_matrix, hstack
    except ImportError as error:
        raise SystemExit('Discovery needs NumPy and SciPy; exact verifier modules do not.') from error
    selected = set(args.cases or ())
    if selected - {row['id'] for row in source['chambers']}:
        parser.error('requested case is absent from the manifest')
    args.output.mkdir(parents=True, exist_ok=True)
    metric.symbolic_checks()
    symmetries = compiler.marked_symmetries()
    edges = compiler.direct.load_data()[2]
    build_start = time.monotonic()
    basis = build_quotient()
    substitution = sparse_matrix(basis, 490)
    print(json.dumps({'quotient_seconds': time.monotonic()-build_start,
                      'raw_products': 2485, 'free_coordinates': 490,
                      'substitution_nonzeros': substitution.nnz,
                      'minimum_y': replay.minimum_height(args.coefficient)}), flush=True)
    summaries = []
    (args.output / 'discovery_summary.json').write_text('[]\n')
    for row in source['chambers']:
        if selected and row['id'] not in selected:
            continue
        if not selected and any(key.endswith('_certificate') or key == 'final_polynomial' for key in row):
            continue
        path = args.output / f'phase0_chamber_{row["id"]:03d}_metric_certificate.json'
        path.unlink(missing_ok=True)
        assert len(row['signs']) == 70 and set(row['signs']) <= {'+', '-'}
        model = tuple(1 if value == '+' else -1 for value in row['signs'])
        assert len(model) == 70 and all(value in (-1, 1) for value in model)
        rows, tags = metric_products(model, symmetries, args.coefficient)
        signs = np.array([model[a]*model[b] for a, b in PRODUCTS])
        signed = substitution.multiply(signs[:, None]).tocsr()
        reduced = sparse_matrix(rows, 2485) @ signed
        equalities = hstack([reduced.T, -signed.T]).tocsr()
        count = len(rows)
        strict = {QUAD_INDEX[tuple(map(int, q))] for q in row['strict']}
        strict_products = {i for i, (a, b) in enumerate(PRODUCTS) if a in strict and b in strict}
        normalization = csr_matrix(([-1.]*len(strict_products),
                                    ([0]*len(strict_products), [count+i for i in sorted(strict_products)])),
                                   shape=(1, count+2485))
        objective = np.zeros(count+2485) if args.feasibility else np.r_[np.ones(count), np.full(2485, .001)]
        start = time.monotonic()
        solved = linprog(objective, A_eq=equalities, b_eq=np.zeros(490),
                         A_ub=normalization, b_ub=[-1.], bounds=(0, None),
                         method=args.method, options={'time_limit': args.seconds})
        summary = {'case': row['id'], 'solver_status': solved.status,
                   'solver_seconds': time.monotonic()-start, 'status': 'no certificate'}
        if solved.status == 0:
            try:
                if not np.isfinite(solved.x).all():
                    raise ValueError('nonfinite discovery weights')
                start = time.monotonic()
                weights, reconstructed = reconstruct(solved.x, rows, model, basis,
                                                      strict_products, args.coefficient)
                summary['exact_reconstruction_seconds'] = time.monotonic()-start
                summary['active_basis_reconstructed'] = reconstructed
                certificate = make_certificate(row['id'], model, rows, tags, weights, args.coefficient)
                start = time.monotonic()
                coverage = checked_coverage(certificate, source['chambers'], symmetries, edges)
                if row['id'] not in {entry['chamber'] for entry in coverage}:
                    raise ValueError('candidate has no checked positive K4 residual for its source chamber')
                summary['independent_replay_seconds'] = time.monotonic()-start
                summary['covered_cases'] = [entry['chamber'] for entry in coverage]
                payload = {'certificates': [certificate], 'coverage': coverage}
                path.write_text(json.dumps(payload, indent=2)+'\n')
                summary['status'] = 'exact certificate'
                summary['file'] = path.name
            except (ValueError, AssertionError) as error:
                summary['status'] = 'candidate rejected by exact replay'
                summary['reason'] = str(error)
        summaries.append(summary)
        print(json.dumps(summary), flush=True)
        (args.output / 'discovery_summary.json').write_text(json.dumps(summaries, indent=2)+'\n')
    print('Only exported exact certificates prove exclusions; other LP outcomes make no geometric claim.')


if __name__ == '__main__':
    if not __debug__:
        raise RuntimeError('run with assertions enabled')
    main()
