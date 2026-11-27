#!/usr/bin/env python3
"""Exhaust every pair of noncollinear limiting cap shapes for canonical ray 3.

The 121 cases distinguish no collinear triple, one distinct collinear
triple, and one coincident vertex pair.  Vanishing graph edges retain
nonzero normalized directions.  See exhaustive_cap_shapes.md for the
geometric argument and the use of the boundary trapezoid inequality.
"""
from collections import Counter
from itertools import combinations, product

import sympy as s

import solver_chambers as chambers

A = (0, 1, 4, 5)
B = (2, 3, 6, 7)
CAPS = (A, B)
RINGS = tuple(tuple(zip(cap, cap[1:] + cap[:1])) for cap in CAPS)


def cross(a, b):
    return a[0]*b[1] - a[1]*b[0]


def minus(a, b):
    return a[0]-b[0], a[1]-b[1]


def shape_classes(cap):
    triples = tuple(combinations(cap, 3))
    result = [{'name': 'Q', 'kind': 'Q', 'zero': set(), 'vectors': None, 'areas': None}]
    result += [{'name': 'F' + ''.join(map(str, tri)), 'kind': 'F', 'zero': {tri},
                'vectors': None, 'areas': None} for tri in triples]
    for pair in combinations(cap, 2):
        coordinates = {v: (int(i == 1), int(i == 2))
                       for i, v in enumerate(v for v in cap if v != pair[1])}
        coordinates[pair[1]] = coordinates[pair[0]]
        areas = {tri: cross(minus(coordinates[tri[1]], coordinates[tri[0]]),
                            minus(coordinates[tri[2]], coordinates[tri[0]])) for tri in triples}
        vectors = tuple(minus(coordinates[b], coordinates[a]) for a, b in zip(cap, cap[1:] + cap[:1]))
        result.append({'name': 'C' + ''.join(map(str, pair)), 'kind': 'C',
                       'zero': {tri for tri, value in areas.items() if not value},
                       'vectors': vectors, 'areas': areas, 'pair': pair})
    assert len(result) == 11
    return result


def compatible(model, shape, cap, opposite, axial_sign):
    orientation = set()
    for tri in combinations(cap, 3):
        if tri in shape['zero']:
            continue
        values = {axial_sign*chambers.model_sign(model, tri + (v,)) for v in opposite}
        if len(values) != 1:
            return None
        if shape['areas'] is not None:
            orientation.update(value*shape['areas'][tri] for value in values)
    if len(orientation) > 1:
        return None
    return next(iter(orientation)) if orientation else 1


def direction_cells(model, shapes, orientations):
    signs = [(i, 4+j, -chambers.model_sign(model, (a, b, c, d)), False)
             for i, (a, b) in enumerate(RINGS[0])
             for j, (c, d) in enumerate(RINGS[1])]
    equalities = []
    for k, (cap, opposite, shape, orientation) in enumerate(zip(CAPS, CAPS[::-1], shapes, orientations)):
        offset = 4*k
        for i in range(4):
            tri = tuple(cap[(i+j) % 4] for j in range(3))
            strict = tuple(sorted(tri)) not in shape['zero']
            sign = (1 if k == 0 else -1)*chambers.model_sign(model, tri + (opposite[0],))
            signs.append((offset+i, offset+(i+1) % 4, sign, strict))
            if shape['kind'] == 'F' and not strict:
                # The three vertices are distinct, hence the two nonzero edges
                # share a line; either relative direction sign is allowed.
                equalities.append((offset+i, offset+(i+1) % 4, None))
        vectors = shape['vectors']
        if vectors is None:
            continue
        for i, j in combinations(range(4), 2):
            if vectors[i] == (0, 0) or vectors[j] == (0, 0):
                continue  # keep a collapsed edge's independent virtual direction
            value = cross(vectors[i], vectors[j])
            if value:
                signs.append((offset+i, offset+j, orientation*(1 if value > 0 else -1), True))
            else:
                dot = sum(a*b for a, b in zip(vectors[i], vectors[j]))
                equalities.append((offset+i, offset+j, 1 if dot > 0 else -1))

    for tail in product((-1, 1), repeat=7):
        z = (1,) + tail
        if any(sign is not None and z[i]*z[j] != sign for i, j, sign in equalities):
            continue
        reach = [0]*8
        strict_pairs = []
        for i, j, _ in equalities:
            reach[i] |= 1 << j
            reach[j] |= 1 << i
        for i, j, sign, strict in signs:
            if z[i]*z[j]*sign < 0:
                i, j = j, i
            reach[i] |= 1 << j
            if strict:
                strict_pairs.append((i, j))
        for k in range(8):
            for i in range(8):
                if (reach[i] >> k) & 1:
                    reach[i] |= reach[k]
        if any((reach[j] >> i) & 1 for i, j in strict_pairs):
            continue
        same_line = lambda i, j: i == j or ((reach[i] >> j) & 1 and (reach[j] >> i) & 1)
        yield z, same_line


def main():
    if not __debug__:
        raise RuntimeError('run with assertions enabled')
    symmetries = chambers.marked_symmetries()
    n, clauses, *_ = chambers.base_formula()
    models = chambers.enumerate_models(n, clauses, symmetries)
    cap_models = {model for model in models if all(
        len({chambers.model_sign(model, tri + (v,)) for v in opposite}) == 1
        for cap, opposite in ((A, B), (B, A)) for tri in combinations(cap, 3))}
    assert len(cap_models) == 16
    mirror = (1, 0, 7, 6, 5, 4, 3, 2)
    assert any(entry['phase_preserving'] and tuple(entry['permutation']) == mirror
               for entry in symmetries)
    assert {mirror[0], mirror[4]} == {1, 5} and {mirror[3], mirror[7]} == {2, 6}

    counts = Counter()
    table = []
    for sa, sb in product(shape_classes(A), shape_classes(B)):
        cells = 0
        category = None
        for model in models:
            oa = compatible(model, sa, A, B, 1)
            ob = compatible(model, sb, B, A, -1)
            if oa is None or ob is None:
                continue
            for z, same_line in direction_cells(model, (sa, sb), (oa, ob)):
                cells += 1
                assert sa['kind'] != 'F' and sb['kind'] != 'F'
                special = (sa['name'], sb['name']) in (('C04', 'C37'), ('C15', 'C26'))
                if special:
                    assert model not in cap_models
                    category = 'two_V_shapes'
                    if sa['name'] == 'C04':
                        # A=(a,-a,p,-p), B=(c,d,-d,-c).
                        first = (same_line(0, 4) and same_line(2, 5)
                                 and z[0]*z[4] == -1 and z[2]*z[5] == 1)
                        second = (same_line(0, 5) and same_line(2, 4)
                                  and z[0]*z[5] == 1 and z[2]*z[4] == -1)
                        assert first != second
                else:
                    assert model in cap_models
                    choices = []
                    for parity in (0, 1):
                        group = (parity, parity+2, parity+4, parity+6)
                        if all(same_line(i, j) for i in group for j in group):
                            assert z[parity]*z[parity+2] == -1
                            assert z[parity+4]*z[parity+6] == -1
                            choices.append(parity)
                    assert choices
                    # A coincident opposite pair has two nonparallel arms and
                    # cannot have either common-base parity.  The graph check
                    # already excludes it, but record this classification gate.
                    for shape, cap in ((sa, A), (sb, B)):
                        if shape['kind'] == 'C':
                            i, j = map(cap.index, shape['pair'])
                            assert (i-j) % 4 in (1, 3)
                    category = 'trapezoids_with_positive_heights'
        if cells == 0:
            category = 'no_direction_cells'
        counts[category] += 1
        table.append((sa['name'], sb['name'], category, cells))
    assert sum(counts.values()) == 121
    assert counts['two_V_shapes'] == 2
    print('PASS exhaustive 121 noncollinear-cap shape pairs:', dict(counts), flush=True)
    print('surviving direction-cell totals:', dict(Counter(
        {kind: sum(cells for _, _, category, cells in table if category == kind)
         for kind in counts})), flush=True)

    # The only nontrapezoid cells are strictly incompatible with the stress mask.
    al, u, ch, de, k = s.symbols('alpha u chi delta k')
    rhs = (al-u)*(ch-de)
    ac, ad, pc, pd = s.symbols('ac ad pc pd')
    mask_weights = 3*al*ch + al*de + u*ch + 3*u*de
    masked_dots = pc + pd - ac - ad
    assert s.expand(mask_weights - masked_dots - 2*(al+u)*(ch+de)
                    - (rhs - masked_dots)) == 0
    dot_first = u*de + al*ch - (u*ch+al*de)*k
    dot_second = -u*ch - al*de + (u*de+al*ch)*k
    assert s.expand(dot_first-rhs-(u*ch+al*de)*(1-k)) == 0
    assert s.expand(dot_second-rhs+(u*de+al*ch)*(1-k)) == 0
    print('PASS exact strict V/V stress identities; each coefficient positive and k<1', flush=True)
    print('Metric conclusion uses the closed-base trapezoid inequality and normalized-minor boundary bridge in cap_limit.md.')


if __name__ == '__main__':
    main()
