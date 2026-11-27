#!/usr/bin/env python3
"""Exact combinatorial certificates for Type 4's strict-support proof.

No solver or floating-point geometry is used. The geometric implications are
proved in global_attack_support.md; this checks their entire finite input.
"""

from itertools import combinations


FACES = tuple(tuple(map(int, s)) for s in
              "012 031 024 053 045 152 134 146 165 264 257 276 374 356 367 475".split())
EDGES = {tuple(sorted(e)) for f in FACES for e in combinations(f, 2)}
LINKS = (
    (1, 2, 4, 5, 3),
    (0, 2, 5, 6, 4, 3),
    (0, 1, 5, 7, 6, 4),
    (0, 1, 4, 7, 6, 5),
    (0, 2, 6, 1, 3, 7, 5),
    (0, 3, 6, 1, 2, 7, 4),
    (1, 4, 2, 7, 3, 5),
    (2, 5, 4, 3, 6),
)
# Every listed K5 lies in the corresponding closed vertex neighborhood.
CLOSED_NEIGHBORHOOD_K5 = (
    (0, 1, 2, 4, 5),
    (0, 1, 2, 4, 5),
    (0, 1, 2, 4, 5),
    (0, 1, 3, 4, 5),
    (0, 1, 2, 4, 5),
    (0, 1, 2, 4, 5),
    (1, 2, 4, 5, 6),
    (2, 4, 5, 6, 7),
)


def is_clique(vertices):
    return all(tuple(sorted(e)) in EDGES for e in combinations(vertices, 2))


def check():
    assert len(EDGES) == 24
    assert len(set(map(frozenset, FACES))) == 16
    certificates = []
    for v, link in enumerate(LINKS):
        assert len(link) == len(set(link))
        assert v not in link
        actual = {tuple(sorted(set(f) - {v})) for f in FACES if v in f}
        claimed = {tuple(sorted((link[i], link[(i + 1) % len(link)])))
                   for i in range(len(link))}
        assert claimed == actual
        neighbors = {w for e in EDGES if v in e for w in e if w != v}
        assert set(link) == neighbors
        clique = CLOSED_NEIGHBORHOOD_K5[v]
        assert len(clique) == len(set(clique)) == 5
        assert set(clique) <= neighbors | {v}
        assert is_clique(clique)

        for i, a in enumerate(link):
            for j in range(i + 1, len(link)):
                b = link[j]
                if tuple(sorted((a, b))) in EDGES:
                    continue  # Opposite rays would put v on actual edge ab.
                arcs = (link[i:j + 1], link[j:] + link[:i + 1])
                witnesses = [(arc, tuple(sorted((v, *triple))))
                             for arc in arcs for triple in combinations(arc, 3)
                             if is_clique((v, *triple))]
                assert witnesses, (v, a, b)
                arc, tetrahedron = witnesses[0]
                assert arc[0] in (a, b) and arc[-1] in (a, b)
                assert arc[0] != arc[-1]
                assert set(tetrahedron) - {v} <= set(arc)
                assert len(set(tetrahedron)) == 4 and v in tetrahedron
                certificates.append((v, (a, b), arc, tetrahedron))

    tetrahedra = tuple(q for q in combinations(range(8), 4) if is_clique(q))
    assert len(tetrahedra) == 23
    assert len(certificates) == 20
    # Every possible interior vertex of every planar K4 is covered by the
    # nonplanar-star argument, rather than merely selected anchor cliques.
    for q in tetrahedra:
        for v in q:
            assert set(q) - {v} <= set(LINKS[v])
            assert is_clique(CLOSED_NEIGHBORHOOD_K5[v])

    print("PASS 8 exact link cycles and 8 closed-neighborhood K5 certificates")
    print("PASS all 23 K4s, all 92 possible interior-vertex incidences")
    print("PASS all 20 nonedge antipodal-pair cases have a semicircle K4")
    for v, pair, arc, clique in certificates:
        print(f"v={v}; pair={pair}; arc={''.join(map(str, arc))}; "
              f"K4={''.join(map(str, clique))}")


if __name__ == "__main__":
    check()
