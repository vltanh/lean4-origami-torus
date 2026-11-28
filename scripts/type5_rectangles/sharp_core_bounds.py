"""The compact sharp-ray core polytope and the four intrinsic area bounds."""

from itertools import combinations, combinations_with_replacement, product

from flint import fmpq

from .chart import cross, subtract
from .reduced import CYCLES


def core_halfspaces(complex_):
    # U = 1/|B|². Each intrinsic pair is stored as 4U(p.A, p.B).
    # A row (a, b) denotes a.v <= b in these eight coordinates and U.
    rows = []
    for i, k in combinations(range(1, 6), 2):
        if (i, k) == (3, 4):
            continue
        m, n = complex_.shift[i, k]
        for (h, v), sign in product(((1, 0), (0, 1), (-1, 1)), (-1, 1)):
            row = [0]*9
            for label, factor in ((i, -sign), (k, sign)):
                if label != 1:
                    offset = 2*(label-2)
                    row[offset] = factor*h
                    row[offset+1] = factor*v
            row[8] = sign*(h*(4*m+2*n)+v*2*m) - (2 if v == 0 else 0)
            bound = (2 if v else 0)-sign*v*4*n
            rows.append((tuple(row), bound))
    return rows


def vertices(rows):
    """Clip the initial box, carrying exact vertex/facet incidences."""
    intervals = [(-2, 2)]*8 + [(0, 1)]
    cuts = []
    for i, (low, high) in enumerate(intervals):
        for sign, bound in ((-1, -low), (1, high)):
            row = [0]*9
            row[i] = sign
            cuts.append((tuple(row), bound))

    def slack(row, bound, point):
        return bound - sum(c*x for c, x in zip(row, point, strict=True) if c)

    active = {tuple(map(fmpq, v)): sum(1 << i for i, (row, bound) in enumerate(cuts)
                                      if slack(row, bound, v) == 0)
              for v in product(*intervals)}
    for row, bound in rows:
        if (row, bound) in cuts:
            continue
        points = list(active)
        values = [slack(row, bound, v) for v in points]
        outside = [i for i, value in enumerate(values) if value < 0]
        bit = 1 << len(cuts)
        next_active = {v: (active[v] | bit if value == 0 else active[v])
                       for v, value in zip(points, values, strict=True) if value >= 0}
        if outside:
            # Vertices of each old facet, stored as a bit set.
            incidences = [0]*len(cuts)
            for i, v in enumerate(points):
                mask = active[v]
                while mask:
                    first = mask & -mask
                    incidences[first.bit_length()-1] |= 1 << i
                    mask ^= first
            for i, inside_slack in enumerate(values):
                if inside_slack <= 0:
                    continue
                v = points[i]
                for j in outside:
                    w = points[j]
                    common = active[v] & active[w]
                    if common.bit_count() < 8:
                        continue
                    # The minimal common face is an edge exactly when its
                    # only vertices are v and w.
                    pair = (1 << i) | (1 << j)
                    shared = (1 << len(points))-1
                    mask = common
                    while mask and shared != pair:
                        first = mask & -mask
                        shared &= incidences[first.bit_length()-1]
                        mask ^= first
                    if shared == pair:
                        t = inside_slack/(inside_slack-values[j])
                        cut_vertex = tuple(x+t*(y-x) for x, y in zip(v, w, strict=True))
                        next_active[cut_vertex] = common | bit
        active = next_active
        cuts.append((row, bound))
    return sorted(active)


def area_bounds(complex_, point):
    u = point[8]
    p = {1: (0, 0), **{i: point[2*(i-2):2*(i-1)] for i in range(2, 6)}}
    anchor = cross(p[5], p[2])
    bounds = [anchor, 4*u-anchor]
    for j in (0, 6, 7):
        lifted = {}
        for i in p:
            m, n = complex_.shift[i, j]
            lifted[i] = (p[i][0]-(4*m+2*n)*u, p[i][1]-2*m*u-4*n)
        area = 0
        for f in complex_.faces:
            if j in f:
                k = f.index(j)
                area += cross(lifted[f[(k+1) % 3]], lifted[f[(k+2) % 3]])
        bounds.extend([area-4*u, 20*u-area])
    return bounds


def verify(complex_):
    rows = core_halfspaces(complex_)
    # This point is strict in the starting box and in every cutting halfspace,
    # so each intermediate polytope is full-dimensional.
    interior = [fmpq(a, 6) for a in (-1, -11, 5, 2, -2, 6, -5, -11, 3)]
    assert all(sum(a*x for a, x in zip(row, interior, strict=True)) < bound for row, bound in rows)
    for j, cycle in CYCLES.items():
        for i, k in zip(cycle, cycle[1:]+cycle[:1], strict=True):
            if (i, k) != (3, 4):
                coherent = subtract(complex_.shift[i, j], complex_.shift[k, j])
                assert coherent != complex_.shift[i, k]
    corners = vertices(rows)
    ends = [v for v in corners if v[-1] == 1]
    assert len(corners) == 39 and len(ends) == 34
    assert all(v[-1] in (0, 1) for v in corners)
    assert all(x.q == 1 for v in corners for x in v)
    values = [area_bounds(complex_, v) for v in corners]
    for i, j in combinations_with_replacement(range(len(corners)), 2):
        mid = tuple((x+y)/2 for x, y in zip(corners[i], corners[j], strict=True))
        for m, a, b in zip(area_bounds(complex_, mid), values[i], values[j], strict=True):
            assert 4*m-a-b >= 0
    # Strictness in the relative interiors, including the endpoint U = 1.
    for column in zip(*(area_bounds(complex_, v) for v in ends), strict=True):
        assert max(column) > 0
    print("Certified 39 sharp-ray core vertices and the anchor and three star area bounds.", flush=True)
