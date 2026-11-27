#!/usr/bin/env python3
"""Compile the bounded shared axis chart into 268 unfiltered K4 branches.

Usage: python solver_remaining_axis.py SOURCE_DIRECTORY OUTPUT_DIRECTORY
       [--queries --mark 2 --y 1000000]

SOURCE_DIRECTORY contains the replayable common 18,080-model cover from
solver_remaining_chambers.py. This wrapper does not impose any finite
mask. The separate axis gauge covers every realization for y>=32.
"""

import argparse
from collections import defaultdict
import hashlib
from itertools import combinations
import json
from pathlib import Path
import re
import time

import exhaustive_remaining_axis as axis
import solver_remaining_chambers as common


def transported_strict(source):
    result = {}
    for record in source['strict_orbits']:
        model = tuple(1 if sign == '+' else -1 for sign in record['signs'])
        strict = {tuple(map(int, quad)) for quad in record['strict']}
        for permutation in source['topological_symmetries']:
            transformed = common.common.transformed_model(model, permutation)
            inverse = {old: new for new, old in enumerate(permutation)}
            result.setdefault(transformed, set()).update(
                tuple(sorted(inverse[i] for i in quad)) for quad in strict)
    return result


def compile_cover(source):
    models = [tuple(1 if sign == '+' else -1 for sign in word)
              for word in source['all_models']]
    strict = transported_strict(source)
    assert len(models) == len(strict) == 18080 and set(models) == set(strict)
    _, _, faces, edges, _, _ = common.base_formula()
    partitions = common.common.circuit_partitions(faces, edges)
    cliques = [common.QI[tuple(map(int, quad))] for quad in source['cliques']]
    groups = defaultdict(list)
    for model in models:
        pattern = ''.join('+' if model[index] > 0 else '-' for index in cliques)
        groups[pattern].append(model)
    branches = []
    for pattern, members in sorted(groups.items()):
        proved = set.intersection(*(strict[model] for model in members))
        ranks = set.intersection(*(
            {support for quad in strict[model]
             for size in (3, 4) for support in combinations(quad, size)}
            for model in members))
        remaining = [(support, positive) for support, positive in partitions
                     if len(support) < 5 and support not in ranks]
        branches.append({'pattern': pattern, 'models': len(members),
                         'strict': [''.join(map(str, quad)) for quad in sorted(proved)],
                         'remaining_circuits': remaining,
                         'diagram': common.decision_diagram(members, cliques)})
    assert len(branches) == 268
    return {'models': len(models), 'cliques': source['cliques'], 'branches': branches}


def query_parts(mark, y=10**6):
    full, metadata = axis.generate(mark, y)
    prefix, suffix = full.split('(declare-fun b1 () Bool)', 1)
    prefix = '\n'.join(line for line in prefix.splitlines()
                       if not re.match(r'\(define-fun m[0-7]{4} ', line)
                       and not re.match(r'\(assert \(distinct m[0-7]{4} 0\)\)', line))+'\n'
    definitions = {}
    for line in suffix.splitlines():
        match = re.fullmatch(r'\(define-fun (a[0-7]+c[012]+) \(\) Real .*\)', line)
        if match:
            definitions[match.group(1)] = line
    assert len(definitions) == 322
    # Unlike the face wrapper, the axis prefix already contains all eight
    # cyclic horizontal inequalities before the Boolean/circuit suffix.
    return prefix, definitions, metadata


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('source', type=Path)
    parser.add_argument('output', type=Path)
    parser.add_argument('--queries', action='store_true')
    parser.add_argument('--mark', type=int, choices=(1, 2))
    parser.add_argument('--y', type=int, default=10**6)
    args = parser.parse_args()
    if args.queries and args.mark is None:
        parser.error('--queries requires --mark')
    if args.y < 32:
        parser.error('the bounded axis chart requires y>=32')
    start = time.monotonic()
    source_path = args.source/'remaining_chambers.json'
    source_bytes = source_path.read_bytes()
    source = json.loads(source_bytes)
    result = compile_cover(source)
    result['common_manifest_sha256'] = hashlib.sha256(source_bytes).hexdigest()
    result['axis_identity_checks'] = axis.verify()
    if args.queries:
        result['query_request'] = {'mark': args.mark, 'y': args.y}
    args.output.mkdir(parents=True, exist_ok=True)
    (args.output/'axis_chambers.json').write_text(json.dumps(result, separators=(',', ':'))+'\n')
    sizes = []
    if args.queries:
        parts = query_parts(args.mark, args.y)
        for index, branch in enumerate(result['branches']):
            text = common.generate_query(parts, result['cliques'], branch)
            (args.output/f'ray{args.mark}_axis_k4_{index:03d}.smt2').write_text(text)
            sizes.append(len(text))
    summary = {'models': result['models'], 'K4_branches': len(result['branches']),
               'minimum_y': 32, 'seconds': time.monotonic()-start,
               'strict_range': [min(len(row['strict']) for row in result['branches']),
                                max(len(row['strict']) for row in result['branches'])],
               'remaining_circuits': [min(len(row['remaining_circuits']) for row in result['branches']),
                                      max(len(row['remaining_circuits']) for row in result['branches'])],
               'diagram_nodes': [min(len(row['diagram']['nodes']) for row in result['branches']),
                                 max(len(row['diagram']['nodes']) for row in result['branches'])]}
    if sizes:
        summary['query_byte_range'] = [min(sizes), max(sizes)]
    (args.output/'summary.json').write_text(json.dumps(summary, indent=2)+'\n')
    print(json.dumps(summary), flush=True)
    print('Independent common-cover, RUP and axis-wrapper replays are required; no marking is excluded.')


if __name__ == '__main__':
    if not __debug__:
        raise RuntimeError('run with assertions enabled')
    main()
