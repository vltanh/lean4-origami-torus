#!/usr/bin/env python3
"""Exact cycle/diameter linking bounds for the seven sharp-ray markings.

Standard library only. This checks integer winding data and exhausts simple
cycles; the geometric implication is proved in cycle_thresholds.md.
"""
from fractions import Fraction as Q
from itertools import combinations, permutations
from pathlib import Path
import json

EXPECTED = {
    't4_ray_1.smt2': (Q(25, 4), (1, 3, 6, 4, 5), (1, -2)),
    't4_ray_2.smt2': (Q(4), (2, 4, 3, 5), (1, -2)),
    't5_ray_1.smt2': (Q(25, 4), (0, 2, 3, 1, 5), (-1, 2)),
    't7_ray_1.smt2': (Q(77, 12), (0, 3, 6, 1, 4, 7, 2, 5), (-4, 3)),
    't7_ray_2.smt2': (Q(85, 12), (0, 3, 6, 1, 4, 7, 2, 5), (-1, 3)),
    't7_ray_3.smt2': (Q(4), (0, 2, 4, 6), (1, -2)),
    't7_ray_4.smt2': (Q(63, 16), tuple(range(8)), (-3, 4)),
}


def winding(cycle, shifts):
    edges = list(zip(cycle, cycle[1:] + cycle[:1]))
    assert all(edge in shifts for edge in edges)
    return tuple(sum(shifts[edge][j] for edge in edges) for j in (0, 1))


def threshold(cycle, shifts):
    m, n = winding(cycle, shifts)
    assert n != 0
    return (len(cycle) ** 2 - (Q(m) + Q(n, 2)) ** 2) / (n ** 2)


def verify():
    cases = json.loads((Path(__file__).resolve().parent / 'cases.json').read_text())
    selected = [case for case in cases if case['sharp']]
    assert {case['file'] for case in selected} == set(EXPECTED)
    for case in selected:
        shifts = {tuple(row['edge']): tuple(row['shift']) for row in case['edge_shifts']}
        assert len(shifts) == 24
        shifts.update({(j, i): (-m, -n) for (i, j), (m, n) in list(shifts.items())})
        bound, certificate, period = EXPECTED[case['file']]
        assert len(set(certificate)) == len(certificate)
        assert winding(certificate, shifts) == period
        assert threshold(certificate, shifts) == bound

        best = None
        count = 0
        for size in range(3, 9):
            for vertices in combinations(range(8), size):
                # Least vertex first and the second below the last removes
                # precisely cyclic rotations and reversal.
                for tail in permutations(vertices[1:]):
                    if tail[0] > tail[-1]:
                        continue
                    cycle = vertices[:1] + tail
                    edges = list(zip(cycle, cycle[1:] + cycle[:1]))
                    if not all(edge in shifts for edge in edges):
                        continue
                    m, n = winding(cycle, shifts)
                    if n == 0:
                        assert abs(m) < size
                        continue
                    candidate = threshold(cycle, shifts)
                    assert candidate > 0
                    best = candidate if best is None else min(best, candidate)
                    count += 1
        assert best == bound
        if case['file'] == 't7_ray_4.smt2':
            assert winding((0, 2, 4, 6), shifts) == (1, 0)
            assert winding((1, 3, 5, 7), shifts) == (1, 0)
        print(f"PASS {case['file']}: y^2 >= {bound} forces q(1,0)=0; "
              f"cycle {certificate}, period {period}; {count} nonhorizontal simple cycles")
    print('PASS exact winding certificates and optimality among cycle/diameter tests')


if __name__ == '__main__':
    verify()
