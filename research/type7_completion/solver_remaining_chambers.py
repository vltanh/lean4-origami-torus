#!/usr/bin/env python3
"""Compile ray-1/2 topology into compact finite K4-sign branches.

Usage: python solver_remaining_chambers.py OUTPUT [--proof]
       [--queries --mark 1 --mask 03 --anchor 013]

The shared 18,080 generic models are enumerated with a pure SAT backend.
Each finite-y mask retains the proved separation of its two small-edge
gap clusters. Strictness is propagated once per topological orbit and
intersected within each K4-sign branch. A compact decision diagram keeps
all remaining weak sign choices, including zeros. Only actual circuits
not already excluded by those choices and strict minors remain.
"""

import argparse
from collections import Counter, defaultdict
from itertools import combinations, permutations
import json
from pathlib import Path
import time

import solver_chambers as common
from solver_sat import FastSAT
import solver_remaining_face as face
from verify_linking import CNF, data, formula, short_pairs
from verify_nonparallel_corner import require_link_values

V, Q, QI = common.V, common.Q, common.QI
MASKS = face.m.MASKS
LONG_RINGS = ((0, 2, 4, 6), (1, 3, 5, 7))


def base_formula():
    cases = json.loads((face.ROOT/'linking_checkpoint/cases.json').read_text())
    pairs = []
    for mark in (1, 2):
        shifts, _, _ = data(next(row for row in cases if row['file'] == f't7_ray_{mark}.smt2'))
        pairs.append(short_pairs(shifts))
    assert pairs[0] == pairs[1] and len(pairs[0]) == 12
    n, clauses, faces, edges, neighbors = formula(7)
    extra = CNF(n)
    for a, b in pairs[0]:
        extra.unlink(a, b)
    require_link_values(extra, *LONG_RINGS, {-2, -1, 1, 2})
    return extra.n, clauses+extra.C, faces, edges, neighbors, pairs[0]


def cycle_forms(cycle):
    cycle = tuple(cycle)
    return {cycle[i:]+cycle[:i] for i in range(len(cycle))} | {
        cycle[::-1][i:]+cycle[::-1][:i] for i in range(len(cycle))}


def topological_symmetries(faces, pairs):
    """For common Boolean enumeration only; these do not quotient metrics."""
    face_set = {frozenset(face) for face in faces}
    pair_set = {frozenset((frozenset(a), frozenset(b))) for a, b in pairs}
    long_cycles = set().union(*(cycle_forms(cycle) for cycle in LONG_RINGS))
    result = []
    for permutation in permutations(V):
        if {frozenset(permutation[i] for i in face) for face in faces} != face_set:
            continue
        if {frozenset((frozenset(permutation[i] for i in a),
                       frozenset(permutation[i] for i in b))) for a, b in pairs} != pair_set:
            continue
        if not all(tuple(permutation[i] for i in cycle) in long_cycles for cycle in LONG_RINGS):
            continue
        result.append(permutation)
    assert len(result) == 16
    return result


def gap_clusters(mask):
    large = sorted(map(int, mask))
    gaps = []
    for left, right in zip(large, large[1:]+large[:1]):
        distance = (right-left) % 8
        if distance >= 3:
            gaps.append(tuple((left+j) % 8 for j in range(1, distance+1)))
    assert len(gaps) == 2 and not set(gaps[0]) & set(gaps[1])
    assert all(len(gap) >= 3 for gap in gaps)
    return gaps


def separation_clauses(mask):
    """The finite y>=10^6 gap-hull theorem, including all five-point tests."""
    left, right = map(set, gap_clusters(mask))
    result = []
    for support in combinations(sorted(left | right), 5):
        if set(support) <= left or set(support) <= right:
            continue
        row = [(1 if vertex in left else -1)*(-1)**i
               *common.lit(support[:i]+support[i+1:]) for i, vertex in enumerate(support)]
        result.extend([row, [-value for value in row]])
    return result


def satisfies(model, clauses):
    return all(any(model[abs(literal)-1] == (1 if literal > 0 else -1) for literal in clause)
               for clause in clauses)


def enumerate_models(n, clauses, symmetries):
    models, calls = set(), 0
    start = time.monotonic()
    with FastSAT(n, clauses) as solver:
        while True:
            status = solver.check()
            calls += 1
            if status == -1:
                break
            if status != 1:
                raise RuntimeError(f'incomplete Boolean enumeration: {status}')
            model = tuple(solver.model())
            orbit = {common.transformed_model(model, permutation) for permutation in symmetries}
            assert not orbit & models
            models.update(orbit)
            for member in sorted(orbit):
                solver.add([-(i+1)*value for i, value in enumerate(member)])
    assert len(models) == 18080 and calls == 1151
    return tuple(sorted(models)), {'sat_calls': calls, 'seconds': time.monotonic()-start}


def strict_orbits(models, symmetries, faces, edges, neighbors):
    mapped, records = {}, []
    for model in models:
        if model in mapped:
            continue
        strict, trace = common.strict_closure(model, faces, edges, neighbors)
        records.append({'signs': ''.join('+' if value > 0 else '-' for value in model),
                        'strict': [''.join(map(str, quad)) for quad in sorted(strict)], 'trace': trace})
        for permutation in symmetries:
            transformed = common.transformed_model(model, permutation)
            inverse = {old: new for new, old in enumerate(permutation)}
            image = frozenset(tuple(sorted(inverse[i] for i in quad)) for quad in strict)
            if transformed in mapped:
                # Different stabilizer actions can give different valid
                # propagated sets. Their union is still proved strict.
                mapped[transformed] |= image
            else:
                mapped[transformed] = image
    assert len(records) == 1150 and set(mapped) == set(models)
    return mapped, records


def decision_diagram(models, cliques):
    """Ordered Boolean diagram; weak-zero semantics is supplied by the query."""
    # Split the most variable columns early; a fixed deterministic order
    # makes independent reconstruction of all generic assignments simple.
    order = sorted(set(range(70))-set(cliques),
                   key=lambda index: (abs(sum(model[index] for model in models)), index))
    words = tuple(sorted({tuple(model[index] for index in order) for model in models}))
    nodes, ids, cache = [], {}, {}

    def build(level, suffixes):
        if not suffixes:
            return 0
        if level == len(order):
            return 1
        key = level, suffixes
        if key in cache:
            return cache[key]
        negative = tuple(sorted({word[1:] for word in suffixes if word[0] < 0}))
        positive = tuple(sorted({word[1:] for word in suffixes if word[0] > 0}))
        high, low = build(level+1, positive), build(level+1, negative)
        if high == low:
            result = high
        else:
            node = order[level], high, low
            if node not in ids:
                ids[node] = len(nodes)+2
                nodes.append(node)
            result = ids[node]
        cache[key] = result
        return result

    root = build(0, words)
    return {'order': order, 'nodes': nodes, 'root': root}


def compile_manifest(models, symmetries, faces, edges, neighbors):
    strict, orbit_records = strict_orbits(models, symmetries, faces, edges, neighbors)
    cliques = [QI[quad] for quad in Q if set(combinations(quad, 2)) <= edges]
    assert len(cliques) == 16
    partitions = common.circuit_partitions(faces, edges)
    masks = {}
    for mask in MASKS:
        separation = separation_clauses(mask)
        survivors = [model for model in models if satisfies(model, separation)]
        grouped = defaultdict(list)
        for model in survivors:
            pattern = ''.join('+' if model[index] > 0 else '-' for index in cliques)
            grouped[pattern].append(model)
        branches = []
        for pattern, members in sorted(grouped.items()):
            proved = set.intersection(*(set(strict[model]) for model in members))
            # A three-point support can have a different strict containing
            # four-set in different sign models.  Intersect rank facts,
            # rather than requiring a shared containing four-set.
            ranks = set.intersection(*(
                {support for quad in strict[model]
                 for size in (3, 4) for support in combinations(quad, size)}
                for model in members))
            remaining = [(support, positive) for support, positive in partitions
                         if len(support) < 5 and support not in ranks]
            branches.append({'pattern': pattern, 'models': len(members),
                             'strict': [''.join(map(str, quad)) for quad in sorted(proved)],
                             'remaining_circuits': remaining,
                             'diagram': decision_diagram(members, cliques)})
        masks[mask] = {'gap_clusters': gap_clusters(mask), 'separation_clauses': separation,
                       'models': len(survivors), 'branches': branches}
    return {'all_models': [''.join('+' if value > 0 else '-' for value in model) for model in models],
            'topological_symmetries': symmetries, 'strict_orbits': orbit_records,
            'cliques': [''.join(map(str, Q[index])) for index in cliques], 'masks': masks}


def generate_query(parts, cliques, branch):
    prefix, definitions, _ = parts
    strict = {tuple(map(int, quad)) for quad in branch['strict']}
    needed, assertions = set(), []
    m = face.m

    def minor(vertices, axes=(0, 1, 2)):
        name = 'a'+''.join(map(str, vertices))+'c'+''.join(map(str, axes))
        assert name in definitions
        needed.add(name)
        return name

    for quad, sign in zip(cliques, branch['pattern']):
        assertions.append(m.op('assert', m.op('>' if sign == '+' else '<', minor(tuple(map(int, quad))), '0')))
    for quad in sorted(strict-set(tuple(map(int, quad)) for quad in cliques)):
        assertions.append(m.op('assert', m.op('distinct', minor(quad), '0')))
    diagram_lines = []
    def child(index):
        return 'false' if index == 0 else 'true' if index == 1 else f'choice{index}'
    for identifier, (index, high, low) in enumerate(branch['diagram']['nodes'], 2):
        value = minor(Q[index])
        if Q[index] in strict:
            expression = m.op('ite', m.op('>', value, '0'), child(high), child(low))
        else:
            expression = m.any_([m.all_([m.op('>=', value, '0'), child(high)]),
                                 m.all_([m.op('<=', value, '0'), child(low)])])
        diagram_lines.append(f'(define-fun choice{identifier} () Bool {expression})')
    assertions.append(m.op('assert', child(branch['diagram']['root'])))
    for support, positive in branch['remaining_circuits']:
        support, positive = tuple(support), tuple(positive)
        size = len(support)
        rank = m.all_([m.op('=', minor(support, axes), '0')
                       for axes in combinations(range(3), size-1)])
        tests = []
        for axes in combinations(range(3), size-2):
            signed = []
            for i, vertex in enumerate(support):
                value = minor(support[:i]+support[i+1:], axes)
                signed.append(value if ((i % 2 == 0) == (vertex in positive)) else m.neg(value))
            tests.append(m.any_([m.all_([m.op('>', value, '0') for value in signed]),
                                 m.all_([m.op('<', value, '0') for value in signed])]))
        assertions.append(m.op('assert', m.op('not', m.all_([rank, m.any_(tests)]))))
    text = prefix+'\n'.join(definitions[name] for name in sorted(needed))+'\n'
    text += '\n'.join(diagram_lines+assertions+['(check-sat)'])+'\n'
    assert '(declare-fun b' not in text and 'long_link' not in text
    return text


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('output', type=Path)
    parser.add_argument('--proof', action='store_true')
    parser.add_argument('--queries', action='store_true')
    parser.add_argument('--mark', type=int, choices=(1, 2))
    parser.add_argument('--mask', choices=MASKS)
    parser.add_argument('--anchor', choices=('013', '023'), default='013')
    args = parser.parse_args()
    if args.queries and (args.mark is None or args.mask is None):
        parser.error('--queries requires a selected --mark and --mask')
    args.output.mkdir(parents=True, exist_ok=True)
    start = time.monotonic()
    n, clauses, faces, edges, neighbors, pairs = base_formula()
    symmetries = topological_symmetries(faces, pairs)
    models, timing = enumerate_models(n, clauses, symmetries)
    manifest = compile_manifest(models, symmetries, faces, edges, neighbors)
    if args.queries:
        manifest['query_request'] = {'mark': args.mark, 'mask': args.mask,
                                     'anchor': args.anchor, 'y': 10**6}
    (args.output/'remaining_chambers.json').write_text(json.dumps(manifest, separators=(',', ':'))+'\n')
    coverage = clauses+[[-(i+1)*value for i, value in enumerate(model)] for model in models]
    common.write_cnf(args.output/'coverage.cnf', n, coverage)
    if args.proof:
        common.write_proof(n, coverage, args.output)
    if args.queries:
        parts = face.query_parts(args.mark, args.mask, anchor=args.anchor)
        for index, branch in enumerate(manifest['masks'][args.mask]['branches']):
            text = generate_query(parts, manifest['cliques'], branch)
            (args.output/f'ray{args.mark}_{args.mask}_k4_{index:03d}.smt2').write_text(text)
    summary = {'models': len(models), 'common_topological_orbits': len(manifest['strict_orbits']),
               'boolean_enumeration': timing, 'total_seconds': time.monotonic()-start,
               'masks': {mask: {'models': row['models'], 'K4_branches': len(row['branches']),
                                'strict_range': [min(len(branch['strict']) for branch in row['branches']),
                                                 max(len(branch['strict']) for branch in row['branches'])],
                                'remaining_circuits': [min(len(branch['remaining_circuits']) for branch in row['branches']),
                                                       max(len(branch['remaining_circuits']) for branch in row['branches'])],
                                'diagram_nodes': [min(len(branch['diagram']['nodes']) for branch in row['branches']),
                                                  max(len(branch['diagram']['nodes']) for branch in row['branches'])]}
                         for mask, row in manifest['masks'].items()}}
    (args.output/'summary.json').write_text(json.dumps(summary, indent=2)+'\n')
    print(json.dumps(summary), flush=True)
    print('Independent manifest and RUP replay are required; no ray or mask is excluded.')


if __name__ == '__main__':
    if not __debug__:
        raise RuntimeError('run with assertions enabled')
    main()
