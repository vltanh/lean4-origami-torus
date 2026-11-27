#!/usr/bin/env python3
"""Compile full ray-3 topology into finite weak-sign metric chambers.

Usage: python solver_chambers.py OUTPUT_DIRECTORY [--proof] [--queries] [--chart face]

The default enumerates and verifies 1,888 generic sign completions, then
uses the 16 canonical-phase-preserving marked metric symmetries to obtain
132 representatives.  Nonclique signs remain weak unless nonvanishing
has been proved by the cofactor/Grassmann--Pluecker propagation below.
Generated manifests, CNF, traces, and SMT queries belong in scratch.

These are necessary systems, not a marking exclusion.  The geometric
premises are those audited in geometric_audit.md.  Every exported query
retains every actual minimal circuit test not already excluded by its
weak signs and proved nonvanishing brackets.  No lower bound for an
unknown cap edge, determinant, or denominator is assumed.
"""

import argparse
from collections import Counter
from itertools import combinations, permutations
import json
from pathlib import Path
import re
import time

import direct_metric as direct
import solver_final_polynomials
import solver_metric_certificates
import solver_metric_differences
import solver_metric_products
import solver_metric_quadratics
import verify_nonparallel_corner as corner
from verify_linking import CNF, SAT, data, formula, lit, short_pairs

V = tuple(range(8))
Q = tuple(combinations(V, 4))
QI = {q: i for i, q in enumerate(Q)}
CAPS = frozenset((frozenset(direct.p.CAP_A), frozenset(direct.p.CAP_B)))
LATTICE_ISOMETRIES = (
    ((1, 0), (0, 1)), ((-1, 0), (0, -1)),
    ((-1, -1), (0, 1)), ((1, 1), (0, -1)),
)


def base_formula():
    n, clauses, faces, edges, neighbors = formula(7)
    extra = CNF(n)
    cases = json.loads((direct.ROOT / 'linking_checkpoint/cases.json').read_text())
    case = next(c for c in cases if c['file'] == 't7_ray_3.smt2')
    shifts, _, _ = data(case)
    for a, b in short_pairs(shifts):
        extra.unlink(a, b)
    corner.require_link_values(extra, (0, 2, 4, 6), (1, 3, 5, 7), {-2, 2})
    return extra.n, clauses + extra.C, faces, edges, neighbors


def enumerate_models(n, clauses, symmetries=None):
    """Block a whole verified phase-symmetry orbit per SAT check.

    The independently checked coverage formula still blocks every one of
    the 1,888 individual models.  This only avoids asking the producer to
    rediscover their symmetric copies in separate solver calls.
    """
    solver = SAT(n, clauses)
    permutations = [entry['permutation'] for entry in symmetries
                    if entry['phase_preserving']] if symmetries is not None else [V]
    models = set()
    checks = 0
    while True:
        status = solver.check()
        checks += 1
        if status == -1:
            break
        if status != 1:
            raise RuntimeError(f'incomplete Boolean enumeration: status {status}')
        model = tuple(solver.model())
        orbit = {transformed_model(model, permutation) for permutation in permutations}
        assert not (orbit & models)
        models.update(orbit)
        for member in sorted(orbit):
            solver.add([-(i + 1) * value for i, value in enumerate(member)])
    assert len(models) == 1888
    if len(permutations) == 16:
        assert checks == 133
    return tuple(sorted(models))


def apply_matrix(matrix, vector):
    return tuple(sum(matrix[i][j] * vector[j] for j in range(2)) for i in range(2))


def marked_symmetries():
    """Exact face/cocycle verification, including all gauge corrections.

    K[p(i),p(j)] = A*K[i,j] + g[j]-g[i].  Thus the intrinsic change
    u'[i]=A^{-1}(u[p(i)]+g[i]) preserves all lengths after translating
    the origin.  A is a lattice isometry at every x=1/2, y>0.
    """
    faces, shifts, edges, *_ = direct.load_data()
    faces = {tuple(sorted(f)) for f in faces}
    result = []
    for permutation in permutations(V):
        if {tuple(sorted(permutation[i] for i in f)) for f in faces} != faces:
            continue
        for matrix in LATTICE_ISOMETRIES:
            gauge = {0: (0, 0)}
            while len(gauge) != 8:
                previous = len(gauge)
                for a, b in edges:
                    if (a in gauge) == (b in gauge):
                        continue
                    if b in gauge:
                        a, b = b, a
                    old = shifts[permutation[a], permutation[b]]
                    new = apply_matrix(matrix, shifts[a, b])
                    gauge[b] = tuple(gauge[a][k] + old[k] - new[k] for k in range(2))
                assert len(gauge) > previous
            if not all(tuple(shifts[permutation[a], permutation[b]][k]
                             - apply_matrix(matrix, shifts[a, b])[k] for k in range(2))
                       == tuple(gauge[b][k] - gauge[a][k] for k in range(2))
                       for a, b in edges):
                continue
            phase_preserving = frozenset(frozenset(permutation[i] for i in cap)
                                         for cap in CAPS) == CAPS
            result.append({'permutation': permutation, 'matrix': matrix,
                           'gauge': [gauge[i] for i in V],
                           'phase_preserving': phase_preserving})
    assert len(result) == 32
    phase = [s for s in result if s['phase_preserving']]
    assert len(phase) == 16
    # Any cap edge can be sent to edge 01; hence a separate, unreduced
    # longest-edge cover may safely impose h01>=1/4 and px1>3/16.
    cap_edges = {frozenset(e) for cap in (direct.p.CAP_A, direct.p.CAP_B)
                 for e in direct.p.ring_edges(cap)}
    assert {frozenset((s['permutation'][0], s['permutation'][1])) for s in phase} == cap_edges
    return result


def transformed_model(model, permutation):
    answer = []
    for q in Q:
        mapped = tuple(permutation[i] for i in q)
        parity = (-1) ** sum(mapped[i] > mapped[j] for i, j in combinations(range(4), 2))
        answer.append(parity * model[QI[tuple(sorted(mapped))]])
    return tuple(value * answer[0] for value in answer)


def representatives(models, symmetries):
    allowed = set(models)
    seen = set()
    result = []
    for model in models:
        if model in seen:
            continue
        orbit = {transformed_model(model, s['permutation']) for s in symmetries
                 if s['phase_preserving']}
        assert orbit <= allowed
        seen.update(orbit)
        result.append(model)
    assert seen == allowed and len(result) == 132
    return tuple(result)


def model_sign(model, points):
    value = lit(points)
    return model[abs(value) - 1] * (1 if value > 0 else -1)


def strict_closure(model, faces, edges, neighbors):
    """Return exact nonvanishing propagation and its replayable witnesses.

    A cofactor step assumes the candidate four-bracket zero.  A known
    strict cofactor gives affine rank four on five points; the residual
    sign partition contradicts acyclicity, embedding, or strict neighbor
    support.  A GP step uses a positive summand in A+B=C to make both
    factors of C nonzero.  This is valid for weak other bracket signs.
    """
    simplices = {(i,) for i in V} | set(edges) | set(faces)
    strict = {q for q in Q if set(combinations(q, 2)) <= edges}
    assert len(strict) == 16
    trace = []
    while True:
        old = set(strict)
        for q in Q:
            if q in strict:
                continue
            for w in V:
                if w in q:
                    continue
                support = tuple(sorted(q + (w,)))
                cofactors = {v: (-1)**i * model_sign(model, support[:i] + support[i + 1:])
                             for i, v in enumerate(support)}
                known = next((tuple(v for v in support if v != z) for z in q
                              if tuple(v for v in support if v != z) in strict), None)
                if known is None:
                    continue
                positive = tuple(v for v in q if cofactors[v] > 0)
                negative = tuple(v for v in q if cofactors[v] < 0)
                if (not positive or not negative
                    or (positive in simplices and negative in simplices)
                    or (len(positive) == 1 and set(negative) <= neighbors[positive[0]])
                    or (len(negative) == 1 and set(positive) <= neighbors[negative[0]])):
                    strict.add(q)
                    trace.append(['cofactor', q, w, known])
                    break
        for common in combinations(V, 2):
            for a, b, c, d in combinations([v for v in V if v not in common], 4):
                relation = [(common + (a, b), common + (c, d)),
                            (common + (a, c), common + (b, d)),
                            (common + (a, d), common + (b, c))]
                signs = [(-1)**i * model_sign(model, u) * model_sign(model, v)
                         for i, (u, v) in enumerate(relation)]
                assert abs(sum(signs)) == 1
                right = signs.index(-sum(signs))
                positive = next((i for i, pair in enumerate(relation)
                                 if i != right and all(tuple(sorted(q)) in strict for q in pair)), None)
                if positive is None:
                    continue
                for q in relation[right]:
                    q = tuple(sorted(q))
                    if q not in strict:
                        strict.add(q)
                        trace.append(['gp', q, common, (a, b, c, d), positive, right])
        if old == strict:
            return strict, trace


def circuit_partitions(faces, edges):
    simplices = {(i,) for i in V} | set(edges) | set(faces)
    result = []
    for size in range(3, 6):
        for support in combinations(V, size):
            for k in range(1, min(3, size - 1) + 1):
                for positive in combinations(support, k):
                    negative = tuple(v for v in support if v not in positive)
                    if support[0] in positive and positive in simplices and negative in simplices:
                        result.append((support, positive))
    assert Counter(len(s) for s, _ in result) == {3: 144, 4: 236, 5: 144}
    return result


def remaining_circuits(model, strict, partitions):
    remaining = []
    for support, positive in partitions:
        if len(support) == 5:
            # A minimal five-point circuit has every cofactor nonzero.
            # Its prescribed signs already forbid this simplex partition.
            signed = [(1 if v in positive else -1) * (-1)**i
                      * model_sign(model, support[:i] + support[i + 1:])
                      for i, v in enumerate(support)]
            assert len(set(signed)) == 2
        elif not any(set(support) <= set(q) for q in strict):
            remaining.append((support, positive))
    assert all(len(support) == 4 for support, _ in remaining)
    return remaining


def query_parts(y, chart='direct'):
    if chart == 'direct':
        text, metadata = direct.generate(y)
    elif chart == 'face':
        import remaining_null_metric
        text, metadata = remaining_null_metric.generate(y)
    else:
        raise ValueError(f'unknown metric chart {chart!r}')
    prefix, suffix = text.split('(declare-fun b1 () Bool)', 1)
    if chart == 'direct':
        prefix = reduce_metric_prefix(prefix, y)
    else:
        # The face chart already has the exact eight nearest-image cuts
        # and the negative-area convention.  Its strict chamber signs
        # absorb these identical K4 tests, as for the direct chart.
        prefix = '\n'.join(line for line in prefix.splitlines()
                           if not re.match(r'\(define-fun m[0-7]{4} ', line)
                           and not re.match(r'\(assert \(distinct m[0-7]{4} 0\)\)', line)) + '\n'
    definitions = {}
    for line in suffix.splitlines():
        match = re.fullmatch(r'\(define-fun (a([0-7]+)c([012]+)) \(\) Real .*\)', line)
        if match:
            definitions[match.group(1)] = line
    projected = suffix[suffix.index('(define-fun projected_area_'):].removesuffix('(check-sat)\n')
    return prefix, definitions, projected, metadata


def reduce_metric_prefix(prefix, y):
    """Discard exactly redundant nearest lifts and the impossible area sign.

    Each cap diagonal has a directed two-edge horizontal step H in (-1,0)
    and gamma step g with |g|<(1/2+1/y^2)/2.  Its nearest lattice images
    therefore use horizontal steps H,H+1 and zero leading vertical step.
    All other horizontal images are farther.  For a nonzero vertical
    integer k, y^2*k^2+2*k*g >= y^2-2*|g| > 1/4 for y>=8, so even
    the closer of H,H+1 is strictly nearer.  Two inequalities per diagonal
    imply the original 63, retaining all equality boundaries.

    The sum of the sixteen oriented double face areas is identically -2
    for this cocycle, independently of all vertex coordinates.
    """
    m = direct.m
    _, _, _, xb, yb, kx, _ = direct.load_data()
    keep = set()
    for cap in (direct.p.CAP_A, direct.p.CAP_B):
        for k in (0, 1):
            i, middle, j = cap[k:k + 3]
            b = yb[i] - yb[j]
            a0 = kx[i, middle] + kx[middle, j] - (xb[j] - xb[i]) - b / 2
            assert a0.denominator == b.denominator == 1
            xi, xj = '0' if i == 0 else f'x{i}', f'x{j}'
            gi, gj = '0' if i == 0 else f'gamma{i}', f'gamma{j}'
            for a in (a0, a0 + 1):
                u = m.add(m.sub(xj, xi), m.rat(xb[j] - xb[i] + a + b / 2))
                v = m.add(m.rat(yb[j] - yb[i] + b),
                          m.mul(m.rat(m.F(1, y*y)), m.sub(gj, gi)))
                keep.add(m.op('assert', m.op('<=', f'nonedge{i}{j}',
                    m.mul('den', m.add(m.mul(u, u), m.mul(str(y*y), v, v))))))
    assert len(keep) == 8
    lines = []
    original_lifts = kept_lifts = area_branches = clique_tests = 0
    for line in prefix.splitlines():
        if line.startswith('(assert (<= nonedge'):
            original_lifts += 1
            if line not in keep:
                continue
            kept_lifts += 1
        if line.startswith('(assert (or (and (> area0 '):
            area_branches += 1
            lines.extend(m.op('assert', m.op('<', f'area{i}', '0')) for i in range(16))
            continue
        # Their identical affine minors get a strict chamber sign below.
        if re.match(r'\(define-fun m[0-7]{4} ', line):
            continue
        if re.match(r'\(assert \(distinct m[0-7]{4} 0\)\)', line):
            clique_tests += 1
            continue
        lines.append(line)
    assert (original_lifts, kept_lifts, area_branches, clique_tests) == (252, 8, 1, 16)
    return '\n'.join(lines) + '\n'


def generate_query(parts, model, strict, circuits):
    prefix, definitions, projected, _ = parts
    lines = [prefix.rstrip()]
    needed = set()

    def minor(support, axes):
        key = 'a' + ''.join(map(str, support)) + 'c' + ''.join(map(str, axes))
        assert key in definitions
        needed.add(key)
        return key

    assertions = []
    m = direct.m
    for q, sign in zip(Q, model):
        comparison = ('>' if sign > 0 else '<') if q in strict else ('>=' if sign > 0 else '<=')
        assertions.append(m.op('assert', m.op(comparison, minor(q, (0, 1, 2)), '0')))
    for support, positive in circuits:
        size = len(support)
        rank = m.all_([m.op('=', minor(support, axes), '0')
                       for axes in combinations(range(3), size - 1)])
        tests = []
        for axes in combinations(range(3), size - 2):
            signed = []
            for i, vertex in enumerate(support):
                value = minor(support[:i] + support[i + 1:], axes)
                signed.append(value if ((i % 2 == 0) == (vertex in positive)) else m.neg(value))
            tests.append(m.any_([m.all_([m.op('>', v, '0') for v in signed]),
                                 m.all_([m.op('<', v, '0') for v in signed])]))
        assertions.append(m.op('assert', m.op('not', m.all_([rank, m.any_(tests)]))))
    lines.extend(definitions[key] for key in sorted(needed))
    lines.extend(assertions)
    lines.append(projected.rstrip())
    lines.append('(check-sat)')
    result = '\n'.join(lines) + '\n'
    assert ' Bool)' not in result and 'long_link' not in result
    return result


def write_cnf(path, n, clauses):
    path.write_text(f'p cnf {n} {len(clauses)}\n' + ''.join(
        ' '.join(map(str, row)) + ' 0\n' for row in clauses))


def write_proof(n, clauses, directory):
    # The independent RUP checker validates the shifted input and every
    # logged input clause; Z3 is only a trace producer.
    m = direct.m
    proof = directory / 'coverage.drat'
    lines = [f'(set-option :sat.drat.file "{proof}")',
             '(set-option :sat.drat.binary false)']
    lines += [f'(declare-const x{i} Bool)' for i in range(1, n + 1)]
    lines += ['(declare-const guard Bool)']
    lines += [f'(assert (or guard x{i}))' for i in range(1, n + 1)]
    lines += ['(assert (or ' + ' '.join(f'x{i}' if i > 0 else f'(not x{-i})' for i in row) + '))'
              for row in clauses]
    lines += ['(assert guard)', '(check-sat-using sat)']
    answer = m.solve('\n'.join(lines), 60000)
    if not answer.startswith('unsat'):
        raise RuntimeError(f'coverage proof not produced: {answer}')
    return proof


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('output', type=Path)
    parser.add_argument('--proof', action='store_true')
    parser.add_argument('--queries', action='store_true')
    parser.add_argument('--chart', choices=('direct', 'face'), default='direct')
    args = parser.parse_args()
    args.output.mkdir(parents=True, exist_ok=True)
    start = time.monotonic()
    n, clauses, faces, edges, neighbors = base_formula()
    symmetries = marked_symmetries()
    enumeration_start = time.monotonic()
    models = enumerate_models(n, clauses, symmetries)
    enumeration_time = time.monotonic() - enumeration_start
    reps = representatives(models, symmetries)
    partitions = circuit_partitions(faces, edges)
    blocked = clauses + [[-(i + 1) * value for i, value in enumerate(model)] for model in models]
    write_cnf(args.output / 'coverage.cnf', n, blocked)
    rows = []
    parts = query_parts(10**6, args.chart) if args.queries else None
    for i, model in enumerate(reps):
        strict, trace = strict_closure(model, faces, edges, neighbors)
        remaining = remaining_circuits(model, strict, partitions)
        row = {'id': i, 'signs': ''.join('+' if v > 0 else '-' for v in model),
               'strict': [''.join(map(str, q)) for q in sorted(strict)],
               'trace': trace, 'remaining_circuits': remaining}
        final_polynomial = solver_final_polynomials.verify(model, strict)
        metric_certificate = solver_metric_certificates.verify(model, symmetries)
        metric_difference = solver_metric_differences.verify(model, symmetries, edges)
        metric_product = solver_metric_products.verify(model, strict, symmetries)
        metric_quadratic = solver_metric_quadratics.verify(model, symmetries, edges)
        if final_polynomial:
            row['final_polynomial'] = final_polynomial
        if metric_certificate:
            row['metric_certificate'] = metric_certificate
        if metric_difference:
            row['metric_difference_certificate'] = metric_difference
        if metric_product:
            row['metric_product_certificate'] = metric_product
        if metric_quadratic:
            row['metric_quadratic_certificate'] = metric_quadratic
        exclusion = final_polynomial or metric_certificate or metric_difference or metric_product or metric_quadratic
        if exclusion:
            # Do not leave a stale undecided query after regenerating an
            # output directory produced by the earlier compiler.
            if args.queries:
                (args.output / f'phase0_chamber_{i:03d}.smt2').unlink(missing_ok=True)
        if parts and not exclusion:
            query = generate_query(parts, model, strict, remaining)
            path = args.output / f'phase0_chamber_{i:03d}.smt2'
            path.write_text(query)
            row |= {'query_bytes': len(query), 'query_assertions': query.count('(assert ')}
        rows.append(row)
    manifest = {'chart': args.chart,
                'all_models': [''.join('+' if v > 0 else '-' for v in model) for model in models],
                'symmetries': symmetries, 'chambers': rows}
    (args.output / 'chambers.json').write_text(json.dumps(manifest, separators=(',', ':')) + '\n')
    if args.proof:
        write_proof(n, blocked, args.output.resolve())
    excluded_count = sum(any(key in row for key in (
        'final_polynomial', 'metric_certificate', 'metric_difference_certificate',
        'metric_product_certificate', 'metric_quadratic_certificate')) for row in rows)
    print(json.dumps({'models': len(models), 'phase_symmetries': 16,
                      'chambers': len(reps), 'enumeration_seconds': enumeration_time,
                      'final_polynomial_exclusions': sum('final_polynomial' in row for row in rows),
                      'metric_certificate_exclusions': sum('metric_certificate' in row for row in rows),
                      'metric_difference_exclusions': sum('metric_difference_certificate' in row for row in rows),
                      'metric_product_exclusions': sum('metric_product_certificate' in row for row in rows),
                      'metric_quadratic_exclusions': sum('metric_quadratic_certificate' in row for row in rows),
                      'algebraically_excluded_chambers': excluded_count,
                      'remaining_metric_chambers': len(reps) - excluded_count,
                      'strict_counts': dict(Counter(len(row['strict']) for row in rows)),
                      'remaining_circuit_counts': dict(Counter(len(row['remaining_circuits']) for row in rows)),
                      'seconds': time.monotonic() - start}), flush=True)
    print(f'{excluded_count} weak chambers excluded by exact final-polynomial or metric certificates; '
          'no full marking excluded. '
          'Replay coverage.cnf and coverage.drat independently when --proof was used.')


if __name__ == '__main__':
    if not __debug__:
        raise RuntimeError('run with assertions enabled')
    main()
