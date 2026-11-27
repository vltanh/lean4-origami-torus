#!/usr/bin/env python3
"""Exact face and marking checks for ray1_geometry.md; no solver or sampling."""
from itertools import combinations, product
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'type4_focus'))
from type4_gap_enum import F, E, SH


def edge(i, j):
    return tuple(sorted((i, j)))


FACES = {frozenset(face) for face in F}
EDGES = set(E)
K = {e: SH[0].get(''.join(map(str, e)), (0, 0)) for e in E}
K.update({(j, i): (-m, -n) for (i, j), (m, n) in list(K.items())})


def period(cycle):
    return tuple(sum(K[i, j][axis]
                     for i, j in zip(cycle, cycle[1:] + cycle[:1]))
                 for axis in (0, 1))


def annuli(A, B):
    cut = {edge(i, j) for cap in (A, B) for i, j in combinations(cap, 2)}
    incidence = {}
    for index, face in enumerate(F):
        for e in combinations(sorted(face), 2):
            incidence.setdefault(e, []).append(index)
    adjacency = {index: set() for index in range(len(F))}
    for e, adjacent in incidence.items():
        assert len(adjacent) == 2
        if e not in cut:
            i, j = adjacent
            adjacency[i].add(j)
            adjacency[j].add(i)
    remaining = set(adjacency)
    result = []
    while remaining:
        queue = [remaining.pop()]
        component = set()
        while queue:
            index = queue.pop()
            component.add(index)
            for neighbor in adjacency[index] & remaining:
                remaining.remove(neighbor)
                queue.append(neighbor)
        result.append({frozenset(F[index]) for index in component})
    assert len(result) == 2
    return sorted(result, key=len)


ROWS = [
    ('ray1_1', (0, 1, 4), (3, 7, 5),
     ((0, 3), (1, 3), (4, 3), (4, 7), (4, 5), (0, 5)),
     {'031', '053', '045', '134', '374', '475'},
     {2, 6}, {(1, 5)}, {(0, 7), (1, 7)}),
    ('ray1_3', (0, 1, 4), (2, 5, 6),
     ((0, 2), (1, 2), (1, 5), (1, 6), (4, 6), (4, 2)),
     {'012', '024', '152', '146', '165', '264'},
     {3, 7}, {(0, 5), (4, 5)}, {(0, 6)}),
    ('ray1_5', (0, 3, 4), (1, 6, 2),
     ((0, 1), (3, 1), (4, 1), (4, 6), (4, 2), (0, 2)),
     {'012', '031', '024', '134', '146', '264'},
     {5, 7}, {(3, 6)}, {(0, 6), (3, 2)}),
]


def main():
    for name, A, B, cycle, expected_faces, extras, additional, missing in ROWS:
        assert period(A) == period(B) == (-1, 0)
        bare, other = annuli(A, B)
        assert (len(bare), len(other)) == (6, 10)
        assert bare == {frozenset(map(int, face)) for face in expected_faces}
        cap_vertices = set(A + B)
        assert set().union(*bare) == cap_vertices
        assert set().union(*other) - cap_vertices == extras

        slice_faces = set()
        a_edges, b_edges, word = [], [], []
        for (i, j), (k, l) in zip(cycle, cycle[1:] + cycle[:1]):
            assert i in A and k in A and j in B and l in B
            assert (i == k) != (j == l)
            face = frozenset((i, j, k, l))
            assert len(face) == 3 and face in bare
            slice_faces.add(face)
            if j == l:
                a_edges.append((i, k))
                word.append(f'A{i}{k}')
            else:
                b_edges.append((j, l))
                word.append(f'B{j}{l}')
        assert slice_faces == bare
        assert a_edges == list(zip(A, A[1:] + A[:1]))
        assert b_edges == list(zip(B, B[1:] + B[:1]))

        grid = set(product(A, B))
        actual = {(i, j) for i, j in grid if edge(i, j) in EDGES}
        assert set(cycle) <= actual
        assert actual - set(cycle) == additional
        assert grid - actual == missing
        assert 3 - len(additional) >= 1
        print(name, '6+10 faces;', ','.join(word),
              '; additional', sorted(additional), '; missing', sorted(missing))

    for A, B in [((0, 1, 4), (5, 6, 7)),
                 ((0, 3, 4), (2, 5, 6)),
                 ((3, 4, 5), (1, 2, 6))]:
        first, second = annuli(A, B)
        assert (len(first), len(second)) == (8, 8)
        caps = set(A + B)
        assert len(set().union(*first) - caps) == 1
        assert len(set().union(*second) - caps) == 1
    print('PASS exact ray-1 annulus, edge-word, and missing-chord checks')


if __name__ == '__main__':
    main()
