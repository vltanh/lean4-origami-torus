#!/usr/bin/env python3
"""Project regular C0 endpoint-cap topology onto 18 planar angle chambers.

Usage: python exhaustive_c0_angles.py OUTPUT_DIRECTORY

Assumes noncollinear endpoint triangles123 and067, and0<u,v<1/2.
Actual anchor minors remain weak; the signs belong to a generic
completion. Outputs two UNSAT coverage formulas for independent replay.
This does not assert metric infeasibility of any angular chamber.
"""

import argparse
from itertools import combinations
import json
from pathlib import Path

import solver_remaining_chambers as common
from solver_sat import FastSAT
from solver_chambers import write_cnf

PAIRS = tuple(combinations(range(2, 8), 2))
ANCHORS = tuple(common.common.lit((0, 1)+pair) for pair in PAIRS)
EXPECTED = {
    '+-------------+', '+------------++', '+----------+-++',
    '+--------+----+', '+--------+-+--+', '+--------+-+-++',
    '+--+-+-+-+-++-+', '+--+-+-+++--+-+', '+--+-+-+++-++-+',
    '+-+------+----+', '+-+------+-+--+', '+-+--+-+++--+-+',
    '+-++-+-+++--+-+', '+-++-+-+++-++-+', '++------------+',
    '++-----------++', '+++-----------+', '+++------+----+',
}


def cap_units(lower_orientation):
    assert lower_orientation in (-1, 1)
    units = []
    for triangle, sign in (((1, 2, 3), -1), ((0, 6, 7), lower_orientation)):
        for vertex in range(8):
            if vertex not in triangle:
                units.append([sign*common.common.lit(triangle+(vertex,))])
    return units


def build(directory):
    n, base, *_ = common.base_formula()
    negative = base+cap_units(-1)
    with FastSAT(n, negative) as solver:
        assert solver.check() == -1
    positive = base+cap_units(1)
    patterns = []
    with FastSAT(n, positive) as solver:
        while solver.check() == 1:
            model = solver.model()
            values = tuple(model[variable-1] for variable in ANCHORS)
            patterns.append(values)
            solver.add([-variable*value for variable, value in zip(ANCHORS, values)])
        assert solver.check() == -1
    words = {''.join('+' if value > 0 else '-' for value in row) for row in patterns}
    assert words == EXPECTED and len(patterns) == 18
    patterns.sort()
    coverage = positive+[[-variable*value for variable, value in zip(ANCHORS, row)]
                         for row in patterns]
    directory.mkdir(parents=True, exist_ok=True)
    write_cnf(directory/'c0_opposite_cap_orientation.cnf', n, negative)
    write_cnf(directory/'c0_anchor_coverage.cnf', n, coverage)
    result = {'pairs': PAIRS, 'anchor_variables': ANCHORS,
              'patterns': [''.join('+' if value > 0 else '-' for value in row) for row in patterns],
              'cap_units': {'negative': cap_units(-1), 'positive': cap_units(1)},
              'assumptions': ['noncollinear projected123 and067', '0<u,v<1/2'],
              'actual_minor_semantics': 'weak signs of a generic completion',
              'metric_exclusion': False}
    (directory/'c0_anchor_chambers.json').write_text(json.dumps(result, indent=2)+'\n')
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('output', type=Path)
    args = parser.parse_args()
    result = build(args.output)
    print(json.dumps({'angular_chambers': len(result['patterns']),
                      'independent_coverage_formulas': 2,
                      'metric_exclusion': False}), flush=True)


if __name__ == '__main__':
    if not __debug__:
        raise RuntimeError('run with assertions enabled')
    main()
