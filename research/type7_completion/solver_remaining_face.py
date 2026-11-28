#!/usr/bin/env python3
"""Quadratic face-coordinate systems for every ray-1/2 finite mask.

Usage: python solver_remaining_face.py OUTPUT --mark 1 --mask 03

The anchor is an actual intrinsic face, 013 by default (023 is also
supported). It is placed isometrically in a spatial coordinate plane.
All original shortest-lift, area, mask, nonedge, weak-sign, linking and
actual circuit conditions are retained. The 21 non-anchor edge equations
are quadratic in 29 real variables; no Gram inverse or determinant
completion equation remains. This is a necessary system, not an exclusion.
"""

import argparse
from itertools import combinations
import json
from pathlib import Path
import re
import time

import remaining_full_metric as original

linked, m = original.linked, original.linked.m
ROOT = linked.ROOT


def case_data(mark):
    assert mark in (1, 2)
    case = next(row for row in json.loads((ROOT/'linking_checkpoint/cases.json').read_text())
                if row['file'] == f't7_ray_{mark}.smt2')
    shifts, _, _ = linked.data(case)
    faces = [tuple(map(int, face)) for face in json.loads(
        (ROOT/'linking_checkpoint/lutz_faces.json').read_text())['7'].split()]
    edges = sorted({tuple(sorted(edge)) for face in faces for edge in combinations(face, 2)})
    return shifts, faces, edges


def generate(mark, mask, y=10**6, anchor='013'):
    assert mark in (1, 2) and mask in m.MASKS
    assert isinstance(y, int) and not isinstance(y, bool) and y >= 10**6
    assert anchor in ('013', '023')
    anchors = tuple(map(int, anchor))
    shifts, faces, edges = case_data(mark)
    assert any(set(face) == set(anchors) for face in faces)
    _, second, third = anchors
    assert tuple(shifts[0, second][k]+shifts[second, third][k] for k in (0, 1)) == shifts[0, third]
    source, metadata = original.generate(mark, mask, y)
    prefix = source.split('(define-fun G11 () Real', 1)[0]
    suffix = source[source.index('(declare-fun b1 () Bool)'):]
    free = tuple(i for i in range(8) if i not in anchors)
    points = {0: ('0', '0', '0')}
    for i in (second, third):
        points[i] = (m.mul(m.rat(m.F(1, y)), f'X0{i}'), f'V0{i}', '0')
    declarations = []
    for i in free:
        points[i] = tuple(f'p{i}_{axis}' for axis in range(3))
        declarations += [f'(declare-fun {name} () Real)' for name in points[i]]
    marker = '(declare-fun v7 () Real)\n'
    assert prefix.count(marker) == 1
    prefix = prefix.replace(marker, marker+'\n'.join(declarations)+'\n')

    def distance(i, j):
        differences = [m.sub(points[j][axis], points[i][axis]) for axis in range(3)]
        return m.add(*(m.mul(value, value) for value in differences))

    replaced = []
    for i, j in combinations(range(8), 2):
        if (i, j) in edges:
            continue
        old = f'(declare-fun z{i}{j} () Real)'
        assert prefix.count(old) == 1
        prefix = prefix.replace(old, f'(define-fun z{i}{j} () Real {distance(i, j)})')
        replaced.append((i, j))
    assert replaced == [(0, 4), (1, 5), (2, 6), (3, 7)]
    metric_edges = [edge for edge in edges if not set(edge) <= set(anchors)]
    assert len(metric_edges) == 21
    prefix += '\n'.join(m.op('assert', m.op('=', distance(i, j), f'D{i}{j}'))
                        for i, j in metric_edges)+'\n'

    def minor(vertices, axes):
        first, *rest = vertices
        return m.det([[m.sub(points[i][axis], points[first][axis]) for axis in axes]
                      for i in rest])

    cliques = [quad for quad in combinations(range(8), 4)
               if set(combinations(quad, 2)) <= set(edges)]
    assert len(cliques) == 16
    for quad in cliques:
        name = 'm'+''.join(map(str, quad))
        prefix += f'(define-fun {name} () Real {minor(quad, (0, 1, 2))})\n'
        prefix += m.op('assert', m.op('distinct', name, '0'))+'\n'
    rewritten, counts = [], {1: 0, 2: 0, 3: 0}
    for line in suffix.splitlines():
        match = re.fullmatch(r'\(define-fun (a([0-7]+)c([012]+)) \(\) Real .*\)', line)
        if match:
            name, vertices, axes = match.groups()
            vertices, axes = tuple(map(int, vertices)), tuple(map(int, axes))
            assert len(vertices) == len(axes)+1
            line = f'(define-fun {name} () Real {minor(vertices, axes)})'
            counts[len(axes)] += 1
        assert not re.search(r'\bG[1-7][1-7]\b', line)
        rewritten.append(line)
    text = prefix+'\n'.join(rewritten)+'\n'
    assert len(re.findall(r'^\(declare-fun \S+ \(\) Real\)', text, re.M)) == 29
    assert text.count('(check-sat)') == 1 and text.endswith('(check-sat)\n')
    assert counts == {1: 84, 2: 168, 3: 70}
    return text, dict(metadata, real_variables=29, metric_equations=21,
                      metric_degree_bound=2, anchor_face=anchor,
                      coordinates='spatial coordinates divided by y',
                      direct_minor_counts=counts, actual_minor_degree_bound=3,
                      nonedge_translate_inequalities=252,
                      removed_gram_completion_equations=10)


def query_parts(mark, mask, y=10**6, anchor='013'):
    """The compact sign compiler replaces only the Boolean/circuit suffix."""
    text, metadata = generate(mark, mask, y, anchor)
    prefix, suffix = text.split('(declare-fun b1 () Bool)', 1)
    prefix = '\n'.join(line for line in prefix.splitlines()
                       if not re.match(r'\(define-fun m[0-7]{4} ', line)
                       and not re.match(r'\(assert \(distinct m[0-7]{4} 0\)\)', line))+'\n'
    definitions = {}
    for line in suffix.splitlines():
        match = re.fullmatch(r'\(define-fun (a([0-7]+)c([012]+)) \(\) Real .*\)', line)
        if match:
            definitions[match.group(1)] = line
    # The eight strict cyclic horizontal bounds are appended by the full
    # source generator after its circuit suffix, so retain them explicitly.
    for i in range(8):
        j = (i+1) % 8
        prefix += f'(assert ({"<" if i < j else ">"} X{min(i,j)}{max(i,j)} 0))\n'
    return prefix, definitions, metadata


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('output', type=Path)
    parser.add_argument('--mark', type=int, choices=(1, 2), required=True)
    parser.add_argument('--mask', choices=m.MASKS, required=True)
    parser.add_argument('--y', type=int, default=10**6)
    parser.add_argument('--anchor', choices=('013', '023'), default='013')
    args = parser.parse_args()
    start = time.monotonic()
    text, metadata = generate(args.mark, args.mask, args.y, args.anchor)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(text)
    print(json.dumps(dict(metadata, bytes=len(text), generation_seconds=time.monotonic()-start)), flush=True)


if __name__ == '__main__':
    if not __debug__:
        raise RuntimeError('run with assertions enabled')
    main()
