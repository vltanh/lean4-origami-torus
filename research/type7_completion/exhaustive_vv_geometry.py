#!/usr/bin/env python3
"""Exclude both possible V/V cap alignments by weak point signs alone.

Usage: python exhaustive_vv_geometry.py [OUTPUT_DIRECTORY]
The optional directory receives two necessary CNFs.  Both are already
contradictory by unit propagation; no metric inequality or positive
lower bound for an arm ratio is used.  See exhaustive_vv_geometry.md.
"""
from itertools import combinations
from pathlib import Path
import sys

import sympy as s

import solver_chambers as chambers
from verify_nonparallel_corner import SAT


def vertical_base_stress():
    """The four common bases cannot all have zero physical weight."""
    mask = s.Matrix([[1, 0, 1, 1], [1, 0, 0, 0],
                     [1, 1, 1, 0], [0, 0, 1, 0]])
    dot = s.Symbol('dot')
    for active, expected in (((0, 2), 1), ((1, 3), 0)):
        weights = [s.Rational(1, 2) if i in active else 0 for i in range(4)]
        signs = [0]*4
        signs[active[0]], signs[active[1]] = 1, -1
        stress = s.expand(sum(mask[i, j]*(weights[i]*weights[j]
                                          - signs[i]*signs[j]*dot)
                              for i in range(4) for j in range(4)))
        assert stress == expected and stress != s.Rational(1, 2)


def cases():
    r, u = s.symbols('r u', positive=True)
    n, base, *_ = chambers.base_formula()
    assert base[0] == [1]
    # The displayed affine frame has a fixed orientation.  Retain both
    # global signs of the generic necessary orientation formula.
    base = [list(row) for row in base[1:]]
    quads = tuple(combinations(range(8), 4))
    for alignment in (1, 2):
        points = {
            0: (0, 0, 0), 1: (1, 0, 0), 4: (0, 0, 0),
            5: (0, 1, 0), 2: (0, 0, 1),
        }
        points.update(
            {3: (-r, 0, 1), 6: (-r, u, 1), 7: (-r, 0, 1)}
            if alignment == 1 else
            {3: (0, -r, 1), 6: (u, -r, 1), 7: (0, -r, 1)})
        units = []
        discarded_variable = []
        zeros = 0
        for index, quad in enumerate(quads, 1):
            anchor, *others = quad
            bracket = s.factor(s.Matrix([
                [points[v][k]-points[anchor][k] for k in range(3)]
                for v in others]).det())
            if not bracket:
                zeros += 1
                continue
            if bracket == r-u:
                discarded_variable.append(quad)
                continue
            # These identities establish constant signs for every r,u>0,
            # including all relative ratios and arbitrarily small arms.
            assert bracket in {1, -1, r, -r, u, -u, r*u, -r*u}
            units.append([int(s.sign(bracket))*index])
        assert discarded_variable == [(1, 2, 5, 6)]
        assert zeros == 37 and len(units) == 32
        yield f'vv_alignment_{alignment}', n, base + units


def main():
    if not __debug__:
        raise RuntimeError('run with assertions enabled')
    output = Path(sys.argv[1]) if len(sys.argv) > 1 else None
    if output is not None:
        output.mkdir(parents=True, exist_ok=True)
    vertical_base_stress()
    print('PASS vertical-base stress: the two parities give 1 and 0, '
          'both different from the required 1/2', flush=True)
    for name, n, clauses in cases():
        if SAT(n, clauses).check() != -1:
            raise AssertionError(f'{name}: necessary formula was not UNSAT')
        if output is not None:
            text = f'p cnf {n} {len(clauses)}\n'
            text += ''.join(' '.join(map(str, row))+' 0\n' for row in clauses)
            (output / f'{name}.cnf').write_text(text)
        print(f'PASS {name}: {n} variables, {len(clauses)} clauses; '
              '32 fixed mixed signs, all remaining signs free', flush=True)


if __name__ == '__main__':
    main()
