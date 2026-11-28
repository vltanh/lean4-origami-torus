"""Verify angular obstructions for generic Type 5 embeddings of the hexagonal torus."""

from itertools import combinations, permutations
import json
from pathlib import Path

import numpy as np

from scripts.type5_planar_masks import common_clauses, grassmann_pluecker, literal, mask_clauses
from .separation import refute

VERTICES = range(8)
QUARTETS = list(combinations(VERTICES, 4))
ANGLES = [(a, b, c) for a in VERTICES for b, c in combinations(VERTICES, 2) if a not in (b, c)]
# Headings in units of pi/6 for the six unit periods in the hexagonal basis.
HEADINGS = {(1, 0): 0, (0, 1): 2, (-1, 1): 4, (-1, 0): 6, (0, -1): -4, (1, -1): -2}


def angle(a, b, c):
    return ANGLES.index((a, min(b, c), max(b, c)))


def wrap(t):
    return (t + 6) % 12 - 6


def angular_system(complex_):
    edges = sorted(complex_.edges)
    faces = {tuple(sorted(f)) for f in complex_.faces}
    directions = {e: [] for e in edges}
    cycles = []

    def directed(i, j):
        return edges.index(tuple(sorted((i, j)))), 6 * int(i > j)

    for a, b, c in combinations(VERTICES, 3):
        cycle = [(a, b), (b, c), (c, a)]
        if not all(tuple(sorted(e)) in complex_.edges for e in cycle):
            continue
        period = tuple(map(sum, zip(*(complex_.shift[e] for e in cycle), strict=True)))
        if period == (0, 0):
            assert (a, b, c) in faces
            continue
        assert (a, b, c) not in faces
        heading = HEADINGS[period]
        cycles.append((cycle, heading))
        for i, j in cycle:
            directions[tuple(sorted((i, j)))].append(heading + 6 * int(i > j))
    assert len(cycles) == 18

    # A positive component along every incident cycle period selects a single
    # angular interval for each of the 24 edges. Its endpoints are integers.
    bounds = []
    for headings in directions.values():
        first = headings[0]
        centers = [first + wrap(h - first) for h in headings]
        lo, hi = max(centers) - 3, min(centers) + 3
        assert lo < hi and all(abs(lo - h) <= 3 and abs(hi - h) <= 3 for h in centers)
        bounds.append((lo, hi))

    # Each row is coefficients on the physical angles, then on the marked
    # directions, then the constant term. Equalities vanish, inequalities
    # are strictly negative. The angles and directions use the same unit.
    equalities, inequalities = [], []
    row_size = len(ANGLES) + len(edges) + 1
    for face in complex_.faces:
        for k, a in enumerate(face):
            b, c = face[(k+1) % 3], face[(k+2) % 3]
            i, u = directed(a, b)
            j, v = directed(a, c)
            lo, hi = bounds[j][0] - bounds[i][1] + v-u, bounds[j][1] - bounds[i][0] + v-u
            turns = [n for n in range(-4, 5) if lo + 12*n < 6 and hi + 12*n > 0]
            assert -36 < lo <= hi < 36 and len(turns) == 1
            row = [0]*row_size
            row[angle(a, b, c)] = 1
            row[len(ANGLES)+i], row[len(ANGLES)+j], row[-1] = 1, -1, u-v-12*turns[0]
            equalities.append(row)
    for a in VERTICES:
        row = [0]*row_size
        for f in complex_.faces:
            if a in f:
                b, c = [i for i in f if i != a]
                row[angle(a, b, c)] = 1
        row[-1] = -12
        equalities.append(row)

    reflected_bounds = []
    for cycle, heading in cycles:
        offsets = []
        for i, j in cycle:
            e, rev = directed(i, j)
            lo, hi = bounds[e]
            candidates = [rev-heading+12*n for n in range(-4, 5)
                          if -3 <= lo+rev-heading+12*n and hi+rev-heading+12*n <= 3]
            offset, = candidates
            offsets.append((e, offset))
        for k, (a, b) in enumerate(cycle):
            c = cycle[k-1][0]
            i, u = offsets[k-1]
            j, v = offsets[k]
            for sign in (1, -1):
                row = [0]*row_size
                row[angle(a, b, c)] = -1
                row[len(ANGLES)+i], row[len(ANGLES)+j], row[-1] = sign, sign, sign*(u+v)
                inequalities.append(row)
                # The two neighboring unit periods give alpha > |delta_i-delta_j| - pi/3.
                other = row.copy()
                other[len(ANGLES)+j] = -sign
                other[-1] = sign*(u-v) - 2
                reflected_bounds.append(other)
    for i, (lo, hi) in enumerate(bounds):
        for sign, constant in ((1, -hi), (-1, lo)):
            row = [0]*row_size
            row[len(ANGLES)+i], row[-1] = sign, constant
            inequalities.append(row)
    return equalities, inequalities + reflected_bounds


def sign_orbits(complex_, patterns):
    """Check that the spatial hypotheses force one of the supplied sign patterns."""
    faces = {frozenset(f) for f in complex_.faces}
    autos = [p for p in permutations(VERTICES) if all(frozenset(p[i] for i in f) in faces for f in faces)]
    assert len(autos) == 6
    actions = [[literal(tuple(p[i] for i in q)) for q in QUARTETS] for p in autos]
    # A change of labels acts on the periods by an isometry at the hexagon.
    loops = [(0, 1, 4), (0, 1, 5)]

    def winding(t):
        return tuple(map(sum, zip(*(complex_.shift[t[i], t[(i+1) % 3]] for i in range(3)), strict=True)))

    def norm(u):
        return u[0]**2 + u[0]*u[1] + u[1]**2

    for p in autos:
        x, y = [winding(tuple(p[i] for i in t)) for t in loops]
        assert [winding(t) for t in loops] == [(-1, 1), (-1, 0)]
        A, B = tuple(-v for v in y), tuple(a-b for a, b in zip(x, y, strict=True))
        assert norm(A) == norm(B) == norm(tuple(a-b for a, b in zip(A, B, strict=True))) == 1
        g = [(0, 0) if i == 1 else complex_.shift[p[1], p[i]] for i in VERTICES]
        for i, j in complex_.edges:
            m, n = complex_.shift[i, j]
            assert all(complex_.shift[p[i], p[j]][k]+g[i][k]-g[j][k] == m*A[k]+n*B[k]
                       for k in range(2))

    clauses = [r for r in common_clauses() if max(map(abs, r)) <= 70]
    last = 70
    for a in VERTICES:
        choices = []
        neighbors = {i for i in VERTICES if tuple(sorted((i, a))) in complex_.edges}
        for f in sorted(tuple(sorted(f)) for f in faces if a in f):
            last += 1
            choices.append(last)
            sides = [literal((*f, i)) for i in sorted(neighbors-set(f))]
            clauses.extend([[-last, *sides], [-last, *(-s for s in sides)]])
        clauses.append(choices)
    seen = set()
    for s in patterns:
        for action in actions:
            model = tuple(s[abs(k)-1] * (1 if k > 0 else -1) for k in action)
            model = tuple(k*model[0] for k in model)
            assert model not in seen
            seen.add(model)
            clauses.append([-k*i for i, k in enumerate(model, 1)])
    assert len(seen) == 4506
    refute(clauses, last)
    return autos


def bits(mask):
    return int.from_bytes(np.packbits(mask, bitorder="little").tobytes(), "little")


def projection_orders(patterns, ranks):
    # For each affine dependence, the positive and negative coefficients
    # cannot occupy disjoint height intervals in any linear projection.
    forbidden = []
    for labels in combinations(VERTICES, 5):
        heights = ranks[:, labels]
        cuts = {}
        for mask in range(1, 31):
            if mask in cuts:
                continue
            left = heights[:, [i for i in range(5) if mask & (1 << i)]]
            right = heights[:, [i for i in range(5) if not mask & (1 << i)]]
            bad = bits((left.max(1) < right.min(1)) | (right.max(1) < left.min(1)))
            cuts[mask] = cuts[31-mask] = bad
        minors = [literal(labels[:i]+labels[i+1:]) * (-1)**i for i in range(5)]
        forbidden.append((minors, cuts))

    permitted = []
    for s in patterns:
        allow = (1 << len(ranks)) - 1
        for minors, cuts in forbidden:
            mask = sum(1 << i for i, m in enumerate(minors) if s[abs(m)-1]*m > 0)
            allow &= ~cuts[mask]
        permitted.append(allow)
    return permitted


def check_clique_separation(complex_, cliques, separation):
    """Refute a crossing using only affine determinant identities and the supplied signs."""
    clauses = []
    for p in combinations(VERTICES, 2):
        for a, b, c, d in combinations(sorted(set(VERTICES)-set(p)), 4):
            terms = [literal((*p, a, b)), literal((*p, c, d)), -literal((*p, a, c)),
                     literal((*p, b, d)), literal((*p, a, d)), literal((*p, b, c))]
            clauses.extend(grassmann_pluecker(terms))
    for labels in combinations(VERTICES, 5):
        row = [(-1)**k * literal(labels[:k]+labels[k+1:]) for k in range(5)]
        clauses.extend([row, [-k for k in row]])

    failures = []
    for edge, face in sorted(complex_.disjoint):
        labels = tuple(sorted((*edge, *face)))
        row = [(-1)**k * (1 if i in edge else -1) * literal(labels[:k]+labels[k+1:])
               for k, i in enumerate(labels)]
        for side in (1, -1):
            variable = 71+len(failures)
            failures.append(variable)
            clauses.extend([[-variable, side*k] for k in row])
    clauses.append(failures)
    for code, extra in separation.items():
        fixed = [literal(q) * (1 if code & (1 << k) else -1) for k, q in enumerate(cliques)]
        assert 4 <= len(extra) <= 7 and all(1 <= abs(v) <= 70 for v in extra)
        assert all(QUARTETS[abs(v)-1] not in cliques for v in extra)
        refute(clauses+[[v] for v in fixed+extra], failures[-1])


def verify(complex_):
    data = json.loads(Path(__file__).with_name("hex_angle_certificates.json").read_text())
    patterns = [tuple(2*((int(s, 16) >> i) & 1)-1 for i in range(70)) for s in data["patterns"]]
    autos = sign_orbits(complex_, patterns)
    orders = [p for p in permutations(VERTICES) if p[0] < p[-1]]
    ranks = np.argsort(orders, axis=1)
    permitted = projection_orders(patterns, ranks)
    a, b, c = np.array(ANGLES).T
    between = (ranks[:, b] < ranks[:, a]) != (ranks[:, c] < ranks[:, a])
    equalities, inequalities = angular_system(complex_)
    rows = equalities + inequalities
    excluded = set()
    for proof in data["multipliers"]:
        assert all(0 <= i < len(rows) for i, w in proof)
        assert all(w >= 0 for i, w in proof if i >= len(equalities))
        assert any(w > 0 and i >= len(equalities) for i, w in proof)
        combined = [sum(w*rows[i][j] for i, w in proof) for j in range(len(rows[0]))]
        assert not any(combined[len(ANGLES):-1])
        # Each spatial angle is six times the probability of betweenness.
        # Bound every integer dot product before using NumPy's fixed width.
        weights = [6*w for w in combined[:len(ANGLES)]]
        assert sum(map(abs, weights)) + abs(combined[-1]) < 2**62
        negative = bits(between @ np.asarray(weights, dtype=np.int64) + combined[-1] < 0)
        excluded.update(i for i, allow in enumerate(permitted) if not (allow & negative))
    # Each of the five anchor tetrahedra is a clique, so its side of face
    # 125 is strict even before passing to general position.
    height_minors = [literal((1, 2, 5, i)) for i in (0, 3, 4, 6, 7)]
    split = {i for i, s in enumerate(patterns)
             if len({s[abs(k)-1] * (1 if k > 0 else -1) for k in height_minors}) > 1}
    assert len(patterns) == 751 and len(excluded) == 401
    assert len(split) == 236 and split <= excluded
    # Each surviving orbit has a supporting winding triangle sharing an
    # anchor edge with 125. Normalize that edge to 12 by a hexagonal symmetry.
    facets = {tuple(sorted(p[i] for i in t)) for p in autos for t in ((1, 2, 3), (1, 2, 6))}
    for t in facets:
        assert all(e in complex_.edges for e in combinations(t, 2))
        assert frozenset(t) not in {frozenset(f) for f in complex_.faces}
        assert tuple(map(sum, zip(*(complex_.shift[t[i], t[(i+1) % 3]] for i in range(3)),
                                  strict=True))) in HEADINGS
    for i, s in enumerate(patterns):
        if i not in excluded:
            assert any(len({s[abs(k)-1]*(1 if k > 0 else -1)
                            for k in (literal((*t, j)) for j in VERTICES if j not in t)}) == 1
                       for t in facets)
    # Clique tetrahedra keep their signs in the limit. Quotient these
    # signs by global reversal and the same six marked symmetries.
    cliques = [q for q in QUARTETS if all(e in complex_.edges for e in combinations(q, 2))]
    maps = [[literal(tuple(p[a] for a in q)) for q in QUARTETS] for p in autos]
    indices = [QUARTETS.index(q) for q in cliques]
    separation = {int(k, 16): v for k, v in data["separation"].items()}
    classes = set()
    for i, s in enumerate(patterns):
        if i in excluded:
            continue
        words, normalized = [], []
        for relabel in maps:
            signs = [s[abs(k)-1]*(1 if k > 0 else -1) for k in relabel]
            normalized.append([v*signs[indices[0]] for v in signs])
            words.append(sum(1 << j for j, k in enumerate(indices) if normalized[-1][k] > 0))
        word = min(words)
        classes.add(word)
        assert any(w == word and all(row[abs(k)-1]*k > 0 for k in separation[word])
                   for w, row in zip(words, normalized, strict=True))
    assert len(cliques) == 23 and len(classes) == 12
    assert sorted(classes) == [int(code, 16) for code in data["clique_classes"]]
    assert set(separation) == classes
    check_clique_separation(complex_, cliques, separation)
    # These nine strict projected signs put the two triangles 012 and 256
    # in the intersecting cones of Type5.ProjectedFaces at vertex 2.
    strict = {row[0] for row in mask_clauses(11149) if len(row) == 1}
    positive = [(0, 1, 2), (0, 1, 3), (0, 2, 3), (0, 1, 6),
                (0, 5, 6), (1, 2, 5), (2, 5, 6)]
    negative = [(0, 3, 5), (1, 2, 6)]
    assert {literal(q) for q in positive} | {-literal(q) for q in negative} <= strict
    print(f"Certified {len(excluded)} hexagonal angular exclusions in {len(patterns)} spatial sign orbits.")
    print(f"Certified {len(classes)} clique classes with four to seven additional signs per class.")
