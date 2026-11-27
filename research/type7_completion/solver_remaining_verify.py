#!/usr/bin/env python3
"""Independent replay of the ray-1/2 finite sign/circuit compiler.

Usage: python solver_remaining_verify.py OUTPUT_DIRECTORY

The separate RUP checker must also accept coverage.cnf/coverage.drat.
This verifier uses exact integer bitsets to check all primary models and
linking counts simultaneously, then replays every strictness witness and
decodes every decision diagram back to its exact generic model set.
"""

from collections import Counter, defaultdict
from itertools import combinations, product
import json
from pathlib import Path
import re
import sys

import solver_remaining_chambers as producer
from remaining_verify import parse_count
from verify_projected_metric import parse


def model_bits(models):
    return [sum(1 << row for row, model in enumerate(models) if model[column] > 0)
            for column in range(70)]


def verify_primary_models(models, clauses, faces, neighbors, short_pairs):
    """Bit parallel truth evaluation, independent of auxiliary SAT values."""
    universe = (1 << len(models))-1
    columns = model_bits(models)

    def literal(value):
        bits = columns[abs(value)-1]
        return bits if value > 0 else universe ^ bits

    for clause in clauses:
        if any(abs(value) > 70 for value in clause):
            continue
        bits = 0
        for value in clause:
            bits |= literal(value)
        assert bits == universe
    for vertex in range(8):
        mixed = 0
        for tri in faces:
            if vertex not in tri:
                continue
            positive = negative = 0
            for neighbor in neighbors[vertex]-set(tri):
                bits = literal(producer.common.lit(tri+(neighbor,)))
                positive |= bits
                negative |= universe ^ bits
            mixed |= positive & negative
        assert mixed == universe

    def linking(a, b):
        states = {0: universe}
        for i in range(1, len(a)-1):
            tri = (a[0], a[i], a[i+1])
            for u, v in zip(b, b[1:]+b[:1]):
                support = tuple(sorted(tri+(u, v)))
                signs = [(1 if vertex in tri else -1)*(-1)**j
                         *producer.common.lit(support[:j]+support[j+1:])
                         for j, vertex in enumerate(support)]
                terminal = producer.common.lit(tri+(v,))
                assert (terminal in signs) != (-terminal in signs)
                if terminal not in signs:
                    signs = [-value for value in signs]
                positive = negative = universe
                for value in signs:
                    bits = literal(value)
                    positive &= bits
                    negative &= universe ^ bits
                assert not positive & negative
                neither = universe ^ (positive | negative)
                next_states = defaultdict(int)
                for count, bits in states.items():
                    next_states[count+1] |= bits & positive
                    next_states[count-1] |= bits & negative
                    next_states[count] |= bits & neither
                states = next_states
        return states

    for a, b in short_pairs:
        assert linking(a, b).get(0, 0) == universe
    states = linking(*producer.LONG_RINGS)
    allowed = 0
    for value in (-2, -1, 1, 2):
        allowed |= states.get(value, 0)
    assert allowed == universe


def replay_strict(model, record, faces, edges, neighbors):
    strict = {quad for quad in producer.Q if set(combinations(quad, 2)) <= edges}
    simplices = {(i,) for i in range(8)} | edges | set(faces)

    def sign(points):
        literal = producer.common.lit(points)
        return model[abs(literal)-1]*(1 if literal > 0 else -1)

    for kind, raw_quad, *rest in record['trace']:
        quad = tuple(raw_quad)
        assert quad not in strict
        if kind == 'cofactor':
            vertex, known = rest
            support = tuple(sorted(quad+(vertex,)))
            assert vertex not in quad and tuple(known) in strict
            assert set(known) < set(support) and tuple(known) != quad
            cofactors = {v: (-1)**i*sign(support[:i]+support[i+1:])
                         for i, v in enumerate(support)}
            positive = tuple(v for v in quad if cofactors[v] > 0)
            negative = tuple(v for v in quad if cofactors[v] < 0)
            assert (not positive or not negative
                    or (positive in simplices and negative in simplices)
                    or (len(positive) == 1 and set(negative) <= neighbors[positive[0]])
                    or (len(negative) == 1 and set(positive) <= neighbors[negative[0]]))
        elif kind == 'gp':
            common, others, positive, right = rest
            common = tuple(common)
            a, b, c, d = others
            pairs = ((common+(a, b), common+(c, d)),
                     (common+(a, c), common+(b, d)),
                     (common+(a, d), common+(b, c)))
            signs = [(-1)**i*sign(left)*sign(right_quad)
                     for i, (left, right_quad) in enumerate(pairs)]
            assert signs[right] == -sum(signs) and positive != right
            assert all(tuple(sorted(value)) in strict for value in pairs[positive])
            assert quad in {tuple(sorted(value)) for value in pairs[right]}
        else:
            raise AssertionError(kind)
        strict.add(quad)
    assert strict == {tuple(map(int, quad)) for quad in record['strict']}
    return strict


def decode_diagram(diagram, expected_count):
    order, nodes, root = diagram['order'], diagram['nodes'], diagram['root']
    positions = {index: level for level, index in enumerate(order)}
    assert len(order) == len(positions) == 54
    assert 0 <= root < len(nodes)+2
    for identifier, (index, high, low) in enumerate(nodes, 2):
        assert index in positions and 0 <= high < identifier and 0 <= low < identifier
        assert high != low
        for child in (high, low):
            if child > 1:
                assert positions[nodes[child-2][0]] > positions[index]
    cache = {}

    def expand(identifier, level):
        key = identifier, level
        if key in cache:
            return cache[key]
        if identifier == 0:
            result = set()
        elif identifier == 1:
            assert 2**(len(order)-level) <= expected_count
            result = set(product((-1, 1), repeat=len(order)-level))
        else:
            index, high, low = nodes[identifier-2]
            position = positions[index]
            assert position >= level
            assert 2**(position-level) <= expected_count
            tails = {(1,)+tail for tail in expand(high, position+1)} | {
                (-1,)+tail for tail in expand(low, position+1)}
            result = {prefix+tail for prefix in product((-1, 1), repeat=position-level)
                      for tail in tails}
        assert len(result) <= expected_count
        cache[key] = result
        return result

    return order, expand(root, 0)


def verify_queries(directory, source, partitions):
    """Bind emitted formulas to the replayed cover and original circuits."""
    if 'query_request' not in source:
        return 0
    request = source['query_request']
    mark, mask, y, anchor = (request[key] for key in ('mark', 'mask', 'y', 'anchor'))
    full, _ = producer.face.generate(mark, mask, y, anchor)
    prefix, definitions, _ = producer.face.query_parts(mark, mask, y, anchor)
    full_circuits = [parse(line)[0] for line in full.splitlines()
                     if line.startswith('(assert (not (and ')]
    assert len(full_circuits) == len(partitions) == 524
    circuit_map = dict(zip(partitions, full_circuits))
    prefix_forms = parse(prefix)
    allowed_definitions = {name: parse(line)[0] for name, line in definitions.items()}
    cliques = [tuple(map(int, quad)) for quad in source['cliques']]

    def minor(support):
        return 'a'+''.join(map(str, support))+'c012'

    def child(identifier):
        return 'false' if identifier == 0 else 'true' if identifier == 1 else f'choice{identifier}'

    branches = source['masks'][mask]['branches']
    for index, branch in enumerate(branches):
        path = directory/f'ray{mark}_{mask}_k4_{index:03d}.smt2'
        text = path.read_text()
        forms = parse(text)
        assert forms[:len(prefix_forms)] == prefix_forms
        remaining = forms[len(prefix_forms):]
        strict = {tuple(map(int, quad)) for quad in branch['strict']}
        while remaining and remaining[0][0] == 'define-fun' and remaining[0][3] == 'Real':
            form = remaining.pop(0)
            assert form == allowed_definitions[form[1]]
        for identifier, (column, high, low) in enumerate(branch['diagram']['nodes'], 2):
            value = minor(producer.Q[column])
            if producer.Q[column] in strict:
                body = ['ite', ['>', value, '0'], child(high), child(low)]
            else:
                body = ['or', ['and', ['>=', value, '0'], child(high)],
                        ['and', ['<=', value, '0'], child(low)]]
            assert remaining.pop(0) == ['define-fun', f'choice{identifier}', [], 'Bool', body]
        expected = [['assert', ['>' if sign == '+' else '<', minor(quad), '0']]
                    for quad, sign in zip(cliques, branch['pattern'])]
        expected += [['assert', ['distinct', minor(quad), '0']]
                     for quad in sorted(strict-set(cliques))]
        expected.append(['assert', child(branch['diagram']['root'])])
        expected += [circuit_map[(tuple(support), tuple(positive))]
                     for support, positive in branch['remaining_circuits']]
        expected.append(['check-sat'])
        assert remaining == expected
        assert '(declare-fun b' not in text and not re.search(r'\bG[1-7][1-7]\b', text)
        parse_count(text)
    return len(branches)


def main(directory):
    source = json.loads((directory/'remaining_chambers.json').read_text())
    models = [tuple(1 if value == '+' else -1 for value in text) for text in source['all_models']]
    assert len(models) == len(set(models)) == 18080
    assert all(len(model) == 70 and model[0] == 1 for model in models)
    n, clauses, faces, edges, neighbors, short_pairs = producer.base_formula()
    lines = (directory/'coverage.cnf').read_text().splitlines()
    expected = clauses+[[-(i+1)*value for i, value in enumerate(model)] for model in models]
    assert lines[0].split() == ['p', 'cnf', str(n), str(len(expected))]
    parsed = []
    for line in lines[1:]:
        row = list(map(int, line.split()))
        assert row and row[-1] == 0 and all(0 < abs(value) <= n for value in row[:-1])
        parsed.append(tuple(sorted(row[:-1])))
    assert Counter(parsed) == Counter(tuple(sorted(row)) for row in expected)
    verify_primary_models(models, clauses, faces, neighbors, short_pairs)

    symmetries = [tuple(row) for row in source['topological_symmetries']]
    assert len(symmetries) == len(set(symmetries)) == 16
    face_set = {frozenset(face) for face in faces}
    pair_set = {frozenset((frozenset(a), frozenset(b))) for a, b in short_pairs}
    long_cycles = set().union(*(producer.cycle_forms(cycle) for cycle in producer.LONG_RINGS))
    for permutation in symmetries:
        assert sorted(permutation) == list(range(8))
        assert {frozenset(permutation[i] for i in face) for face in faces} == face_set
        assert {frozenset((frozenset(permutation[i] for i in a), frozenset(permutation[i] for i in b)))
                for a, b in short_pairs} == pair_set
        assert all(tuple(permutation[i] for i in cycle) in long_cycles for cycle in producer.LONG_RINGS)
    assert all(tuple(p[q[i]] for i in range(8)) in symmetries for p in symmetries for q in symmetries)

    strict_models, witnesses = {}, 0
    for record in source['strict_orbits']:
        model = tuple(1 if value == '+' else -1 for value in record['signs'])
        assert model in models and model not in strict_models
        strict = replay_strict(model, record, faces, edges, neighbors)
        witnesses += len(record['trace'])
        for permutation in symmetries:
            transformed = producer.common.transformed_model(model, permutation)
            inverse = {old: new for new, old in enumerate(permutation)}
            image = {tuple(sorted(inverse[i] for i in quad)) for quad in strict}
            strict_models.setdefault(transformed, set()).update(image)
    assert len(source['strict_orbits']) == 1150 and set(strict_models) == set(models)
    model_indices = {model: index for index, model in enumerate(models)}
    rank_masks = defaultdict(int)
    for model, strict in strict_models.items():
        bit = 1 << model_indices[model]
        supports = set(strict)
        for quad in strict:
            supports.update(combinations(quad, 3))
        for support in supports:
            rank_masks[support] |= bit
    cliques = [tuple(map(int, quad)) for quad in source['cliques']]
    assert cliques == [quad for quad in producer.Q if set(combinations(quad, 2)) <= edges]
    clique_indices = [producer.QI[quad] for quad in cliques]
    partitions = producer.common.circuit_partitions(faces, edges)
    total_branches = omitted = 0
    for mask in producer.MASKS:
        row = source['masks'][mask]
        separation = producer.separation_clauses(mask)
        assert row['gap_clusters'] == list(map(list, producer.gap_clusters(mask)))
        assert row['separation_clauses'] == separation
        grouped = defaultdict(list)
        for model in models:
            if producer.satisfies(model, separation):
                pattern = ''.join('+' if model[index] > 0 else '-' for index in clique_indices)
                grouped[pattern].append(model)
        assert row['models'] == sum(map(len, grouped.values()))
        assert {branch['pattern'] for branch in row['branches']} == set(grouped)
        for branch in row['branches']:
            members = grouped[branch['pattern']]
            assert len(members) == branch['models']
            strict = set.intersection(*(strict_models[model] for model in members))
            assert strict == {tuple(map(int, quad)) for quad in branch['strict']}
            member_mask = sum(1 << model_indices[model] for model in members)
            expected_retained = {(support, positive) for support, positive in partitions
                                 if len(support) < 5
                                 and rank_masks[support] & member_mask != member_mask}
            assert expected_retained == {(tuple(support), tuple(positive))
                                          for support, positive in branch['remaining_circuits']}
            # Five-point forbidden partitions were directly checked in the
            # common primary sign constraints; a minimal five-circuit has
            # no zero cofactor, so compatible weak signs suffice to omit it.
            order, decoded = decode_diagram(branch['diagram'], len(members))
            assert set(order) == set(range(70))-set(clique_indices)
            assert decoded == {tuple(model[index] for index in order) for model in members}
            total_branches += 1
            omitted += len(partitions)-len(expected_retained)
    assert total_branches == sum(len(row['branches']) for row in source['masks'].values())
    queries = verify_queries(directory, source, partitions)
    print(f'PASS 18080 exact primary models and linking values; 16 checked topology symmetries', flush=True)
    print(f'PASS {witnesses} strictness witnesses, {total_branches} K4 branches and {omitted} omitted circuits', flush=True)
    print('PASS every decision diagram decodes to exactly its listed generic model subset', flush=True)
    if queries:
        print(f'PASS {queries} emitted quadratic queries: exact prefix, zero-safe diagram, original retained circuits, parse', flush=True)
    print('Completeness also requires the independent RUP replay; no marking exclusion is claimed.')


if __name__ == '__main__':
    if not __debug__:
        raise RuntimeError('run with assertions enabled')
    if len(sys.argv) != 2:
        raise SystemExit(__doc__)
    main(Path(sys.argv[1]))
