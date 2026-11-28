#!/usr/bin/env python3
"""Uniform first transverse stretch for the marking-1 mask-04 limit.

Usage: python remaining_ray1_mask04_blowup.py OUTPUT

Twenty of the 24 closed horizontal order cells are excluded by exact
weak-slope CNFs. The four surviving Boolean relaxations have one of
h1,h3,h5,h7 equal to zero and all other horizontal weights equal to1/2.
Vertical edges are retained explicitly; no zero coordinate is divided.
"""

import argparse
from itertools import combinations, product
import json
from pathlib import Path

import sympy as s

import remaining_ray1_mask04 as limit
import solver_remaining_chambers as shared
from solver_sat import FastSAT
from verify_nonparallel_corner import allowed_sum

A, B = limit.A, limit.B
EDGES = tuple(combinations(A, 2))+tuple(combinations(B, 2))
EDGE_INDEX = {frozenset(edge): index for index, edge in enumerate(EDGES)}
A_ORDERS = dict(limit.A_LINES, II_sum=(0, -1, 1, 0),
                II_sum_left=(0, -1, 0, 0), II_sum_right=(0, 0, 1, 0),
                I_zero=(0, -1, -1, -2))
B_ORDERS = dict(limit.B_LINES, II_sum=(0, -1, 1, 0),
                II_sum_left=(0, 0, 1, 0), II_sum_right=(0, -1, 0, 0),
                I_zero=(0, 1, 1, 2))
INTERIOR = ('I', 'II', 'II_left', 'II_right')
ENDPOINTS = ('I_zero', 'II_sum', 'II_sum_left', 'II_sum_right')
CASES = (tuple(product(INTERIOR, repeat=2))
         +tuple((name, 'II_both') for name in ENDPOINTS)
         +tuple(('II_both', name) for name in ENDPOINTS))
SURVIVORS = {('II_sum_left', 'II_both'): 3,
             ('II_sum_right', 'II_both'): 1,
             ('II_both', 'II_sum_left'): 5,
             ('II_both', 'II_sum_right'): 7}

# Complete weak orders of three scalar slopes. Every allowed triple is
# (sign(s1-s0), sign(s2-s0), sign(s2-s1)).
SLOPE_ORDERS = {
    tuple(limit.sign(values[j]-values[i]) for i, j in ((0, 1), (0, 2), (1, 2)))
    for values in product(range(3), repeat=3)
}
assert len(SLOPE_ORDERS) == 13


class SlopeModel:
    def __init__(self, x_a, x_b):
        self.n, original, *_ = shared.base_formula()
        self.clauses = [list(row) for row in original]
        self.trits = {}
        self.x = dict(zip(A, x_a)) | dict(zip(B, x_b))
        self.x_signs = [limit.sign(self.x[j]-self.x[i]) for i, j in EDGES]
        nonvertical = [i for i, value in enumerate(self.x_signs) if value]
        vertical = [i for i, value in enumerate(self.x_signs) if not value]
        assert nonvertical
        for i, j in combinations(nonvertical, 2):
            self.new_trit(('slope', i, j))
        for i in vertical:
            self.new_trit(('vertical', i))

        # Reverse every nonvertical vector, when necessary, to make its
        # horizontal coordinate positive. Its slope is unchanged.
        for i, j, k in combinations(nonvertical, 3):
            forms = [(('slope', i, j), 1), (('slope', i, k), 1),
                     (('slope', j, k), 1)]
            for values in product((-1, 0, 1), repeat=3):
                if values not in SLOPE_ORDERS:
                    self.clauses.append(sum((self.deny(form, value)
                                             for form, value in zip(forms, values)), []))

        # Exact triangle identities, including zero horizontal edges.
        for cap in (A, B):
            for a, b, c in combinations(cap, 3):
                first = self.cross((a, b), (a, c))
                self.equal(first, self.cross((a, b), (b, c)))
                self.equal(first, self.cross((a, c), (b, c)))
                if self.x[a] == self.x[b] == self.x[c]:
                    forms = [self.vertical((a, b)), self.vertical((b, c)),
                             self.vertical((a, c))]
                    for values in product((-1, 0, 1), repeat=3):
                        if not allowed_sum(*values):
                            self.clauses.append(sum((self.deny(form, value)
                                                     for form, value in zip(forms, values)), []))

        # Only nonzero limiting mixed determinants fix a generic sign.
        # Both cap tetrahedra are left unrestricted.
        for quad in limit.Q:
            upper = tuple(vertex for vertex in quad if vertex in A)
            lower = tuple(vertex for vertex in quad if vertex in B)
            if len(upper) == 2:
                form = self.cross(upper, lower)
                literal = limit.literal(upper+lower)
            elif len(upper) in (1, 3):
                triple, other, orientation = ((upper, lower, -1) if len(upper) == 3
                                               else (lower, upper, 1))
                a, b, c = triple
                form = self.cross((a, b), (a, c))
                literal = orientation*limit.literal(triple+other)
            else:
                continue
            if form:
                positive, negative = self.bits(form)
                self.clauses.extend([[-positive, literal], [-negative, -literal]])

        # A nontrivial transverse stretch cannot leave all cap vectors
        # on the same line: at least one vertical edge is nonzero or
        # two nonvertical edge slopes differ.
        nontrivial = [literal for i in vertical for literal in self.trits['vertical', i]]
        nontrivial += [literal for i in nonvertical[1:]
                      for literal in self.trits['slope', nonvertical[0], i]]
        self.clauses.append(nontrivial)

    def new_trit(self, key):
        self.trits[key] = self.n+1, self.n+2
        self.n += 2
        self.clauses.append([-self.n+1, -self.n])

    def bits(self, form):
        key, orientation = form
        return self.trits[key] if orientation > 0 else self.trits[key][::-1]

    def deny(self, form, value):
        positive, negative = self.bits(form)
        return ([-positive] if value == 1 else [-negative] if value == -1
                else [positive, negative])

    @staticmethod
    def oriented_edge(edge):
        index = EDGE_INDEX[frozenset(edge)]
        return index, (1 if tuple(edge) == EDGES[index] else -1)

    def vertical(self, edge):
        index, orientation = self.oriented_edge(edge)
        assert not self.x_signs[index]
        return ('vertical', index), orientation

    def cross(self, left, right):
        i, a = self.oriented_edge(left)
        j, b = self.oriented_edge(right)
        if i == j:
            return 0
        xi, xj = self.x_signs[i], self.x_signs[j]
        if xi and xj:
            return ('slope', min(i, j), max(i, j)), a*b*xi*xj*(1 if i < j else -1)
        if xi:
            return ('vertical', j), a*b*xi
        if xj:
            return ('vertical', i), -a*b*xj
        return 0

    def equal(self, left, right):
        if left == 0 and right == 0:
            return
        if left == 0:
            left, right = right, left
        if right == 0:
            self.clauses.extend([[-value] for value in self.bits(left)])
            return
        for a, b in zip(self.bits(left), self.bits(right)):
            self.clauses.extend([[-a, b], [-b, a]])


def exact_checks():
    assert len(CASES) == len(set(CASES)) == 24
    assert set(SURVIVORS) <= set(CASES)
    # det(u,u+v)=det(u,v)=det(u+v,v), without a nonzero-vector
    # hypothesis. These are the identities used in every triangle.
    ux, uy, vx, vy = s.symbols('ux uy vx vy')
    cross = lambda a, b: a[0]*b[1]-a[1]*b[0]
    u, v = (ux, uy), (vx, vy)
    total = (ux+vx, uy+vy)
    assert s.expand(cross(u, total)-cross(u, v)) == 0
    assert s.expand(cross(total, v)-cross(u, v)) == 0
    xa, xb, sa, sb, height = s.symbols('xa xb sa sb height')
    assert s.expand(cross((xa, xa*sa), (xb, xb*sb))-xa*xb*(sb-sa)) == 0
    assert cross((0, height), (xb, xb*sb)) == -height*xb
    assert cross((xa, xa*sa), (0, height)) == xa*height

    # Verify the parity and axial sign for each type of mixed bracket.
    x = s.symbols('x0:8')
    y = s.symbols('y0:8')
    points = {i: (x[i], y[i], 1 if i in A else 0) for i in range(8)}
    vector = lambda i, j: (x[j]-x[i], y[j]-y[i])
    for quad in limit.Q:
        upper = tuple(vertex for vertex in quad if vertex in A)
        lower = tuple(vertex for vertex in quad if vertex in B)
        if len(upper) in (0, 4):
            continue
        if len(upper) == 2:
            order = upper+lower
            expected = cross(vector(*upper), vector(*lower))
        else:
            triple, other, orientation = ((upper, lower, -1) if len(upper) == 3
                                           else (lower, upper, 1))
            a, b, c = triple
            order = triple+other
            expected = orientation*cross(vector(a, b), vector(a, c))
        first, *rest = order
        actual = s.Matrix([[points[i][axis]-points[first][axis] for axis in range(3)]
                           for i in rest]).det()
        assert s.expand(actual-expected) == 0
    return {'horizontal_order_cases': 24, 'weak_three_slope_orders': 13,
            'mixed_determinant_identities': 68,
            'retains_zero_horizontal_edges': True}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('output', type=Path)
    args = parser.parse_args()
    args.output.mkdir(parents=True, exist_ok=True)
    record = {'exact_checks': exact_checks(), 'cases': []}
    for upper, lower in CASES:
        model = SlopeModel(A_ORDERS[upper], B_ORDERS[lower])
        name = upper+'__'+lower
        shared.common.write_cnf(args.output/(name+'.cnf'), model.n, model.clauses)
        with FastSAT(model.n, model.clauses) as solver:
            status = solver.check()
            expected = 1 if (upper, lower) in SURVIVORS else -1
            assert status == expected, (upper, lower, status)
            row = {'upper': upper, 'lower': lower, 'variables': model.n,
                   'clauses': len(model.clauses), 'status': 'SAT' if status == 1 else 'UNSAT'}
            if status == 1:
                row['zero_horizontal_edge'] = SURVIVORS[upper, lower]
                row['boolean_model'] = solver.model(model.n)
            record['cases'].append(row)
    assert sum(row['status'] == 'UNSAT' for row in record['cases']) == 20
    (args.output/'coverage.json').write_text(json.dumps(record, indent=2)+'\n')
    print(json.dumps({'cases': 24, 'UNSAT': 20, 'remaining_zero_edges': [1, 3, 5, 7],
                      'status': 'four endpoint families remain'}))


if __name__ == '__main__':
    if not __debug__:
        raise RuntimeError('run with assertions enabled')
    main()
