#!/usr/bin/env python3
"""Replay the finite Type 5 cover against the actual Lean/research inputs.

This checks the combinatorial part of the reduction, not geometric localization
or infeasibility.  Run with --write to refresh coverage.json after an audited
input change; the default checks its exact contents and source hashes.
"""
import ast
from fractions import Fraction as Q
from hashlib import sha256
from itertools import combinations, permutations, product
import json
from pathlib import Path
import re
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
FOCUS = ROOT / "research/type5_focus"
INPUTS = [
    "research/type5_focus/cases.json",
    "research/type5_focus/lutz_faces.json",
    "research/type5_focus/fixed_elongated/generate.py",
    "research/type5_focus/fixed_elongated/README.md",
    "OrigamiTorus/Type5/Reconstruction.lean",
    "OrigamiTorus/Winding/WindingCocycle.lean",
    "OrigamiTorus/Winding/WindingOrbits.lean",
]


def read(path):
    return (ROOT / path).read_text()


def lean_list(text, pattern):
    match = re.search(pattern, text, flags=re.S)
    assert match, pattern
    return ast.literal_eval(match[1])


def main():
    cases = json.loads((FOCUS / "cases.json").read_text())
    candidates = [c for c in cases if c["type"] == 5 and c["sharp"]]
    assert len(candidates) == 1
    case = candidates[0]
    faces = [tuple(map(int, f)) for f in
             json.loads((FOCUS / "lutz_faces.json").read_text())["5"].split()]
    lean_faces = lean_list(read(INPUTS[4]), r"def faces : List Triangle :=\s*(\[.*?\])")
    assert faces == lean_faces, "Research face list differs from Lean"
    coefficients = dict(lean_list(read(INPUTS[5]),
        r"def coefficients.*?\| \.type5 =>\s*(\[.*?\])"))
    lean_reps = lean_list(read(INPUTS[6]),
        r"def representatives.*?\| \.type5, \.ray =>\s*(\[.*?\])")
    marking = tuple(tuple(p) for p in case["marking"])
    assert [marking] == lean_reps
    assert case["basis"] == [[0, 1, 4], [0, 1, 5]]
    edges = sorted({tuple(sorted(e)) for f in faces for e in combinations(f, 2)})
    assert len(faces) == 16 and len(edges) == 24
    original = {tuple(v["edge"]): tuple(v["shift"]) for v in case["edge_shifts"]}
    assert set(original) == set(edges)
    for e in edges:
        c = coefficients.get(e, (0, 0))
        assert original[e] == tuple(sum(c[i] * marking[i][j] for i in (0, 1))
                                    for j in (0, 1)), (e, "cocycle transcription")
    winding = dict(original)
    winding.update({(j, i): tuple(-v for v in k) for (i, j), k in original.items()})
    winding.update({(i, i): (0, 0) for i in range(8)})
    gauge = {i: winding[1, i] for i in range(8)}
    winding = {e: tuple(k[t] + gauge[e[0]][t] - gauge[e[1]][t] for t in (0, 1))
               for e, k in winding.items()}
    assert all(winding[1, i] == (0, 0) for i in range(8))
    assert all(tuple(sum(winding[e][t] for e in ((i, j), (j, k), (k, i)))
                     for t in (0, 1)) == (0, 0) for i, j, k in faces)

    # A label is incident to the following closed half-turns.  This avoids
    # selecting representative numerical positions in the two open strips.
    incident = ({-1, 0}, {0}, {0, 1}, {1})

    def allowed(i, j, lift):
        return bool(incident[i] & {h + 2 * lift for h in incident[j]})

    cells = set()
    for labels in product(range(4), repeat=8):
        if labels[1] >= 2 or labels.count(0) < 3 or labels.count(2) < 3:
            continue
        domains = [[0] if i == 1 else
                   [q for q in (-1, 0, 1) if allowed(labels[1], labels[i], q)]
                   for i in range(8)]
        for lifts in product(*domains):
            if all(allowed(labels[i], labels[j], lifts[j] - lifts[i] + winding[i, j][1])
                   for i, j in edges):
                cells.add((labels, lifts))
    assert len(cells) == 36

    perm = (6, 5, 2, 4, 3, 1, 0, 7)
    assert {frozenset(perm[v] for v in f) for f in faces} == {frozenset(f) for f in faces}
    reflect = lambda k: (k[0] + k[1], -k[1])
    shift = {i: winding[perm[1], perm[i]] for i in range(8)}
    assert all(winding[perm[i], perm[j]] ==
               tuple(reflect(k)[t] + shift[j][t] - shift[i][t] for t in (0, 1))
               for (i, j), k in winding.items())

    def mirror(cell):
        a, q = cell
        b4 = [a[i] - a[1] + 4 * q[i] for i in range(8)]
        aa = [(-a[perm[i]]) % 4 for i in range(8)]
        if aa[1] >= 2:
            aa = [(v + 2) % 4 for v in aa]
        bb = [-b4[perm[i]] - 4 * shift[i][1] + b4[perm[1]] + 4 * shift[1][1]
              for i in range(8)]
        qq4 = [bb[i] - aa[i] + aa[1] for i in range(8)]
        assert all(v % 4 == 0 for v in qq4)
        return tuple(aa), tuple(v // 4 for v in qq4)

    assert all(mirror(c) in cells and mirror(mirror(c)) == c for c in cells)
    canonical = lambda cell: min(cell, mirror(cell))
    representatives = {canonical(c) for c in cells}
    assert len(representatives) == 19
    assert sum(mirror(c) == c for c in cells) == 2

    def endpoints(cell):
        a, q = cell
        for b in product(*[[v] if v % 2 == 0 else [v, 0, 2] for v in a]):
            if b[1] >= 2:
                continue
            r = [q[i] + int(a[i] == 3 and b[i] == 0) for i in range(8)]
            c = b, tuple(v - r[1] for v in r)
            assert c in cells
            yield c

    proper_endpoints = {e for c in cells for e in endpoints(c) if e != c}
    maximal = cells - proper_endpoints
    assert len(maximal) == 7
    maximal_reps = sorted({canonical(c) for c in maximal})
    assert ["".join(map(str, a)) for a, _ in maximal_reps] == [
        "00120221", "00220231", "00230232", "01200202"]
    blocks = {f"F{i + 1}": {canonical(e) for m in (c, mirror(c)) for e in endpoints(m)}
              for i, c in enumerate(maximal_reps)}
    assert [len(blocks[f"F{i}"]) for i in range(1, 5)] == [5, 9, 9, 3]
    assert set.union(*blocks.values()) == representatives

    def cap_cycle(cap):
        for n in range(3, len(cap) + 1):
            for chosen in combinations(cap, n):
                for tail in permutations(chosen[1:]):
                    cycle = chosen[:1] + tail
                    ee = list(zip(cycle, cycle[1:] + cycle[:1]))
                    if all(e in winding for e in ee) and tuple(
                            sum(winding[e][t] for e in ee) for t in (0, 1)) in ((1, 0), (-1, 0)):
                        return list(cycle)
        raise AssertionError((cap, "no primitive horizontal cycle"))

    cliques = [c for c in combinations(range(8), 5)
               if all(e in edges for e in combinations(c, 2))]
    star_k5 = {str(v): list(next(c for c in cliques if v in c)) for v in range(8)}
    # At a flat star, opposite neighbor rays split the spherical link into
    # minimizing semicircles.  The listed a,x,y,b arc gives incompatible cone
    # coefficients if both radial/diagonal pairs v-x versus a-y and v-y versus
    # x-b are disjoint.  This is the finite input to the generic existing
    # impossible_minimal_arc_of_embedding argument; a-y and x-b need not cross.
    link_cuts = []
    for v in range(8):
        adjacency = {i: [] for e in edges if v in e for i in e if i != v}
        for face in faces:
            if v in face:
                a, b = [i for i in face if i != v]
                adjacency[a].append(b)
                adjacency[b].append(a)
        assert all(len(ns) == 2 for ns in adjacency.values())
        cycle = [min(adjacency), min(adjacency[min(adjacency)])]
        while len(cycle) < len(adjacency):
            cycle.append(next(i for i in adjacency[cycle[-1]] if i != cycle[-2]))
        assert len(set(cycle)) == len(adjacency) and cycle[0] in adjacency[cycle[-1]]
        for ia, ib in combinations(range(len(cycle)), 2):
            a, b = cycle[ia], cycle[ib]
            if tuple(sorted((a, b))) in edges:
                continue
            arcs = [(a, b, cycle[ia + 1:ib]),
                    (b, a, cycle[ib + 1:] + cycle[:ia])]
            witnesses = [(c, x, y, d) for c, d, arc in arcs
                         for x, y in combinations(arc, 2)
                         if tuple(sorted((c, y))) in edges and tuple(sorted((x, d))) in edges]
            assert witnesses, (v, a, b, "antipodal obstruction missing")
            link_cuts.append({"vertex": v, "link": cycle,
                              "missing_pair": sorted((a, b)), "ordered_arc": list(witnesses[0])})
    assert len(link_cuts) == 21
    nonclique_triples = sorted({tuple(sorted([cut["vertex"]] + cut["missing_pair"]))
                               for cut in link_cuts})
    clique_triples = {c for c in combinations(range(8), 3)
                      if all(e in edges for e in combinations(c, 2))}
    assert len(clique_triples) == 34 and len(nonclique_triples) == 21
    assert clique_triples | set(nonclique_triples) == \
        set(combinations(range(8), 3)) - {(0, 6, 7)}
    clique4 = [list(c) for c in combinations(range(8), 4)
               if all(e in edges for e in combinations(c, 2))]
    assert len(clique4) == 23
    possibly_flat = []
    for i, j in edges:
        other = sorted(next(v for v in f if v not in (i, j)) for f in faces if i in f and j in f)
        assert len(other) == 2
        if tuple(other) not in edges:
            possibly_flat.append({"edge": [i, j], "opposite_pair": other})
    assert len(possibly_flat) == 9

    # Verify the numerical margins, separately from the geometric argument.
    eps, y = Q(1, 1000), 10**6
    beta = Q(45, 2) / (eps * y)
    assert 16 * eps + beta + Q(103, 2 * y) < Q(1, 25)
    dlo, dhi = Q(119, 250), Q(131, 250)
    assert dlo == 1 - Q(13, 25) - 4 * eps and dhi == Q(13, 25) + 4 * eps
    assert (dlo - 4 * eps) * (1 - beta) - 4 * eps - Q(51, y) > Q(9, 20)
    assert Q(9, 20) - 2 * eps - Q(1, y) > Q(11, 25)

    result = {
        "schema": 1,
        "scope": "Exact finite-cover/data audit; not a cell exclusion or Lean proof of localization.",
        "input_sha256": {p: sha256((ROOT / p).read_bytes()).hexdigest() for p in INPUTS},
        "target": {"real_part": "1/2", "imaginary_part": y, "epsilon": str(eps)},
        "lean_data_agreement": {"faces": True, "sharp_marking": True, "edge_cocycle": True},
        "counts": {"raw_cells": len(cells), "representatives": len(representatives),
                   "fixed_by_reflection": 2, "maximal_raw_cells": 7,
                   "clique_triples": 34, "additional_noncollinear_triples": 21},
        "representatives": [
            {"id": "".join(map(str, a)), "q": list(q),
             "blocks": [name for name, members in blocks.items() if (a, q) in members],
             "cap_cycles": [cap_cycle([i for i in range(8) if a[i] == lab]) for lab in (0, 2)],
             "orbit_size": 1 if mirror((a, q)) == (a, q) else 2}
            for a, q in sorted(representatives)],
        "star_k5_witnesses": star_k5,
        "antipodal_link_cut_witnesses": link_cuts,
        "nonclique_triples_with_antipodal_obstruction": [list(c) for c in nonclique_triples],
        "clique4": clique4,
        "possibly_uncreased_edges": possibly_flat,
        "remaining_geometric_assembly": [
            "Extract coherent lifted-face data from the chosen definition of a quotient realization.",
            "Instantiate the existing shortest-edge and winding-orbit theorems on those data.",
            "Prove the quantitative two-gap localization; only its rational margins are replayed here.",
            "Instantiate the antipodal link-cut obstruction and flat-star strict support for Type 5 using the listed witnesses, then rule out planar K4s.",
            "Prove metric reconstruction and full simplex-intersection soundness, and exclude the full cell systems."
        ],
    }
    manifest = HERE / "coverage.json"
    if sys.argv[1:] == ["--write"]:
        manifest.write_text(json.dumps(result, indent=2) + "\n")
    else:
        assert not sys.argv[1:], "usage: verify_coverage.py [--write]"
        assert json.loads(manifest.read_text()) == result, "Coverage manifest/source hashes differ"
    print("PASS: Lean inputs agree; 36 cells / 19 representatives; F1-F4 cover 5/9/9/3 cells.")
    print("PASS: primitive cap cycles; 21 antipodal link cuts; 8 K5 star witnesses; 23 K4s; rational margins.")
    print("Scope: no full elongated cell has been excluded by this checker.")


if __name__ == "__main__":
    main()
