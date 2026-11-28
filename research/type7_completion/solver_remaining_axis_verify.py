#!/usr/bin/env python3
"""Independently replay the 268-branch bounded-axis wrapper.

Usage: python solver_remaining_axis_verify.py SOURCE_DIRECTORY OUTPUT_DIRECTORY

The common manifest is replayed first and must separately have an accepted
coverage.cnf/coverage.drat RUP proof. The wrapper checks its exact hash,
reconstructs every unfiltered group, decodes every weak sign diagram, and
binds emitted formulas to the bounded chart and original actual circuits.
For symbolic-height packets it also checks t>0, the exact upper bound,
all degree/scope metadata, and the stable branch IDs and query hashes.
"""

from collections import defaultdict
import hashlib
from itertools import combinations
import json
from pathlib import Path
import re
import sys

import exhaustive_remaining_axis as axis
import solver_remaining_chambers as common
import solver_remaining_verify as replay
from remaining_verify import parse_count
from verify_projected_metric import parse


def verify_queries(directory, record, partitions):
    if 'query_request' not in record:
        return 0
    mark, y = (record['query_request'][name] for name in ('mark', 'y'))
    all_heights = record['query_request'].get('all_heights', False)
    assert isinstance(all_heights, bool)
    full, metadata = axis.generate(mark, y, all_heights=all_heights)
    if all_heights:
        assert record['query_metadata'] == json.loads(json.dumps(metadata))
    prefix_text, suffix = full.split('(declare-fun b1 () Bool)', 1)
    prefix = []
    for form in parse(prefix_text):
        if form[0] == 'define-fun' and re.fullmatch(r'm[0-7]{4}', form[1]):
            continue
        if (form[0] == 'assert' and form[1][0] == 'distinct'
                and re.fullmatch(r'm[0-7]{4}', form[1][1])):
            continue
        prefix.append(form)
    if all_heights:
        assert ['declare-fun', 't', [], 'Real'] in prefix
        assert ['assert', ['>', 't', '0']] in prefix
        assert ['assert', ['<=', 't', ['/', '1', str(y*y)]]] in prefix
    suffix_forms = parse(suffix)
    definitions = {form[1]: form for form in suffix_forms if form[0] == 'define-fun'
                   and re.fullmatch(r'a[0-7]+c[012]+', form[1])}
    actual_circuits = [parse(line)[0] for line in suffix.splitlines()
                       if line.startswith('(assert (not (and ')]
    assert len(definitions) == 322 and len(actual_circuits) == len(partitions) == 524
    circuit_map = dict(zip(partitions, actual_circuits))
    cliques = [tuple(map(int, quad)) for quad in record['cliques']]

    def minor(quad):
        return 'a'+''.join(map(str, quad))+'c012'

    def child(identifier):
        return 'false' if identifier == 0 else 'true' if identifier == 1 else f'choice{identifier}'

    for index, branch in enumerate(record['branches']):
        suffix = '_all_heights' if all_heights else ''
        text = (directory/f'ray{mark}_axis_k4_{index:03d}{suffix}.smt2').read_text()
        forms = parse(text)
        assert forms[:len(prefix)] == prefix
        remaining = forms[len(prefix):]
        strict = {tuple(map(int, quad)) for quad in branch['strict']}
        while remaining and remaining[0][0] == 'define-fun' and remaining[0][3] == 'Real':
            definition = remaining.pop(0)
            assert definition == definitions[definition[1]]
        for identifier, (column, high, low) in enumerate(branch['diagram']['nodes'], 2):
            value = minor(common.Q[column])
            if common.Q[column] in strict:
                expression = ['ite', ['>', value, '0'], child(high), child(low)]
            else:
                expression = ['or', ['and', ['>=', value, '0'], child(high)],
                              ['and', ['<=', value, '0'], child(low)]]
            assert remaining.pop(0) == ['define-fun', f'choice{identifier}', [], 'Bool', expression]
        expected = [['assert', ['>' if sign == '+' else '<', minor(quad), '0']]
                    for quad, sign in zip(cliques, branch['pattern'])]
        expected += [['assert', ['distinct', minor(quad), '0']]
                     for quad in sorted(strict-set(cliques))]
        expected.append(['assert', child(branch['diagram']['root'])])
        expected += [circuit_map[(tuple(support), tuple(positive))]
                     for support, positive in branch['remaining_circuits']]
        expected.append(['check-sat'])
        assert remaining == expected
        assert len(re.findall(r'^\(declare-fun \S+ \(\) Real\)', text, re.M)) == (39 if all_heights else 38)
        assert '(declare-fun b' not in text and 'long_link' not in text
        parse_count(text)
    return len(record['branches'])


def verify_branch_index(directory, record, manifest_bytes):
    """Bind the frozen tail-query index; it is not an exclusion ledger."""
    request = record.get('query_request', {})
    if not request.get('all_heights', False):
        return
    mark, y = request['mark'], request['y']
    index = json.loads((directory/'branch_index.json').read_text())
    assert index['format'] == 1 and index['mark'] == mark
    assert index['minimum_y'] == y and index['height_scope'] == 'entire tail'
    assert index['t_interval'] == f'0 < t <= 1/{y*y}'
    assert index['common_manifest_sha256'] == record['common_manifest_sha256']
    assert index['axis_manifest_sha256'] == hashlib.sha256(manifest_bytes).hexdigest()
    assert index['nonlinear_decisions'] == 0
    expected = []
    for number, branch in enumerate(record['branches']):
        filename = f'ray{mark}_axis_k4_{number:03d}_all_heights.smt2'
        expected.append({'id': f'ray{mark}_k4_{number:03d}',
                         'pattern': branch['pattern'], 'generic_models': branch['models'],
                         'query_file': filename,
                         'query_sha256': hashlib.sha256((directory/filename).read_bytes()).hexdigest()})
    assert index['branches'] == expected
    assert len({entry['id'] for entry in expected}) == 268


def main(source_directory, output_directory):
    source_bytes = (source_directory/'remaining_chambers.json').read_bytes()
    source = json.loads(source_bytes)
    manifest_bytes = (output_directory/'axis_chambers.json').read_bytes()
    record = json.loads(manifest_bytes)
    assert record['common_manifest_sha256'] == hashlib.sha256(source_bytes).hexdigest()
    replay.main(source_directory)
    assert record['axis_identity_checks'] == json.loads(json.dumps(axis.verify()))
    n, clauses, faces, edges, neighbors, pairs = common.base_formula()
    models = [tuple(1 if value == '+' else -1 for value in word) for word in source['all_models']]
    strict_models = {}
    for witness in source['strict_orbits']:
        model = tuple(1 if value == '+' else -1 for value in witness['signs'])
        strict = replay.replay_strict(model, witness, faces, edges, neighbors)
        for permutation in source['topological_symmetries']:
            transformed = common.common.transformed_model(model, permutation)
            inverse = {old: new for new, old in enumerate(permutation)}
            strict_models.setdefault(transformed, set()).update(
                tuple(sorted(inverse[i] for i in quad)) for quad in strict)
    assert len(strict_models) == 18080 and set(strict_models) == set(models)
    assert record['models'] == 18080 and record['cliques'] == source['cliques']
    clique_indices = [common.QI[tuple(map(int, quad))] for quad in record['cliques']]
    grouped = defaultdict(list)
    indices = {model: index for index, model in enumerate(models)}
    rank_masks = defaultdict(int)
    for model in models:
        grouped[''.join('+' if model[index] > 0 else '-' for index in clique_indices)].append(model)
        supports = set(strict_models[model])
        for quad in strict_models[model]:
            supports.update(combinations(quad, 3))
        for support in supports:
            rank_masks[support] |= 1 << indices[model]
    assert len(grouped) == len(record['branches']) == 268
    assert {branch['pattern'] for branch in record['branches']} == set(grouped)
    partitions = common.common.circuit_partitions(faces, edges)
    for branch in record['branches']:
        members = grouped[branch['pattern']]
        assert branch['models'] == len(members)
        strict = set.intersection(*(strict_models[model] for model in members))
        assert strict == {tuple(map(int, quad)) for quad in branch['strict']}
        member_mask = sum(1 << indices[model] for model in members)
        retained = {(support, positive) for support, positive in partitions
                    if len(support) < 5 and rank_masks[support] & member_mask != member_mask}
        assert retained == {(tuple(support), tuple(positive))
                            for support, positive in branch['remaining_circuits']}
        order, decoded = replay.decode_diagram(branch['diagram'], len(members))
        assert set(order) == set(range(70))-set(clique_indices)
        assert decoded == {tuple(model[index] for index in order) for model in members}
    count = verify_queries(output_directory, record, partitions)
    verify_branch_index(output_directory, record, manifest_bytes)
    print('PASS unfiltered 18080-model cover: 268 exact K4 groups, rank facts, circuits and weak diagrams', flush=True)
    if count:
        print(f'PASS {count} bounded-axis formulas: complete metric prefix, original retained circuits, zero boundaries and parse', flush=True)
    if record.get('query_request', {}).get('all_heights', False):
        print('PASS entire-height-tail interval, 39-real metadata and 268 frozen query IDs/hashes', flush=True)
    print('The common RUP replay and bounded-axis necessity proof remain premises; no marking is excluded.')


if __name__ == '__main__':
    if not __debug__:
        raise RuntimeError('run with assertions enabled')
    if len(sys.argv) != 3:
        raise SystemExit(__doc__)
    main(Path(sys.argv[1]), Path(sys.argv[2]))
