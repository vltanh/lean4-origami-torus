#!/usr/bin/env python3
"""Exact local Radon sign gates for the two Type 4 K5 cores.

This enumerates sixteen sign masks, not metric solutions.  The geometric
premises are strict support, strict K4 determinants, and embedded faces.
"""
from itertools import combinations

ANCHORS = (1, 4, 5, 6)
FACES = {tuple(sorted(map(int, f))) for f in
         "012 031 024 053 045 152 134 146 165 264 257 276 374 356 367 475".split()}
EDGES = {e for f in FACES for e in combinations(f, 2)}
EXPECTED = {
    2: {(1,), (6,), (1, 4), (1, 6), (4, 5), (5, 6)},
    3: {(1,), (6,), (1, 5), (1, 6), (4, 5), (4, 6)},
}

for root in (2, 3):
    vertices = tuple(sorted(ANCHORS + (root,)))
    assert all(e in EDGES for e in combinations(vertices, 2))
    allowed = set()
    for mask in range(16):
        negative = tuple(v for i, v in enumerate(ANCHORS) if mask & (1 << i))
        # r_root - sum(lambda_v*r_v) = 0, sum(lambda_v)=1.
        pos = set(negative) | {root}
        neg = set(ANCHORS) - set(negative)
        # An empty part contradicts affine balance.  A singleton part
        # puts one vertex inside the convex hull of its four neighbors.
        if min(len(pos), len(neg)) < 2:
            continue
        triple = tuple(sorted(pos if len(pos) == 3 else neg))
        pair = tuple(sorted(neg if len(pos) == 3 else pos))
        assert pair in EDGES
        if triple in FACES:
            continue  # The complementary edge pierces this actual face.
        allowed.add(negative)
    assert allowed == EXPECTED[root]
    gate = 4 if root == 2 else 5
    assert all(6 not in negative or gate not in negative for negative in allowed)
    print("PASS root", root, "allowed negative lambda subsets:",
          sorted(allowed, key=lambda s: (len(s), s)))
    print(f"PASS root {root}: lambda_6 < 0 implies lambda_{gate} > 0")

print("PASS all 32 local sign masks; no metric exclusion asserted")
