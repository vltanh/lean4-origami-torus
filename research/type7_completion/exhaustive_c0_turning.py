#!/usr/bin/env python3
"""Exact algebra and finite consequences of the regular ray-1 C0 turn bound.

Usage: python exhaustive_c0_turning.py
       python exhaustive_c0_turning.py OUTPUT --cells C0_FULL_CELLS_JSON

The analytical angle inequalities are proved in the companion note.
This verifier checks their polynomial identities and the metric/bracket
bindings, then optionally exports complete filtered Boolean covers.
"""

import argparse
from itertools import combinations
import json
from pathlib import Path

import sympy as sym

import exhaustive_c0_angles as angles
import exhaustive_c0_cells as cells
import solver_remaining_limit as reduction
from solver_chambers import write_cnf

METRIC_SIGNS = (((2, 3, 6, 7), 1), ((0, 2, 3, 7), 1), ((1, 2, 6, 7), -1))
UNIFORM_COUNTS = (24, 12, 8, 32, 20, 8, 1, 25, 7, 20, 8, 1, 7, 1, 12, 0, 8, 8)
DIAGONAL_COUNTS = (0, 0, 4, 8, 8, 5, 0, 0, 0, 8, 8, 0, 0, 0, 0, 0, 4, 5)


def verify():
    s = sym.symbols('s0:8')
    h = [(1-value)/2 for value in s]
    d = [value/2 for value in s]

    def simplex_zero(expression):
        assert sym.cancel(expression.subs(s[0], 1-sum(s[1:]))) == 0

    D = s[2]+s[3]+s[4]+s[5]+s[6]+s[1]*s[7]
    U, V = s[1]+s[6], s[2]+s[7]
    W = 1-U-V
    simplex_zero(2*h[1]*h[7]-d[0]-D/2)
    simplex_zero(W-s[0]-(s[3]+s[4]+s[5]))
    positive = (s[2]*(s[0]+s[2]+s[3]+s[4]+s[5]+s[7])
                +s[6]*(s[0]+s[1]+s[2]+s[3]+s[4]+s[5]+s[6])
                +s[3]+s[4]+s[5])
    simplex_zero(D-U*V-positive)
    for i, j in ((1, 2), (6, 7)):
        base = (s[i]+s[j])/2
        tangent_squared = (base**2-(h[i]-h[j])**2)/((h[i]+h[j])**2-base**2)
        assert sym.cancel(tangent_squared-s[i]*s[j]/(1-s[i]-s[j])) == 0
    gap = 2*h[4]-d[3]/h[2]-d[5]/h[6]
    gap_certificate = (2*(d[0]+d[1]+d[7])
                       +2*d[2]*(1-d[3]/h[2])+2*d[6]*(1-d[5]/h[6]))
    simplex_zero(gap-gap_certificate)

    shifts, _, edges = reduction.axis.case_data(1)
    lengths = list(sym.symbols('h0:7'))
    lengths.append(sym.Rational(7, 2)-sum(lengths))
    deficits = [sym.Rational(1, 2)-value for value in lengths]
    x = [sym.Integer(0)]
    for i in range(7):
        x.append(sym.expand(x[-1]-lengths[i]-shifts[i, i+1][0]
                            -sym.Rational(shifts[i, i+1][1], 2)))
    p = [sym.zeros(2, 1), sym.zeros(2, 1)]
    p.extend(sym.Matrix(sym.symbols(f'p{i}x p{i}y')) for i in range(2, 8))
    T = {(i, j): sym.expand((p[j]-p[i]).dot(p[j]-p[i])
                           -(x[j]-x[i]+shifts[i, j][0]+sym.Rational(shifts[i, j][1], 2))**2)
         for i, j in edges}
    core = T[0, 1]-T[0, 2]-T[1, 7]+T[2, 7]
    assert sym.expand(core+2*(p[2].dot(p[7])+lengths[1]*lengths[7]-deficits[0])) == 0
    E, F, Y = p[3]-p[2], p[7]-p[6], p[5]-p[4]
    u = sym.Symbol('u')
    C = (1-2*u)*(T[2, 4]-T[3, 4]-T[2, 5]+T[3, 5])
    Drow = u*(T[4, 7]-T[4, 6]-T[5, 7]+T[5, 6])
    assert sym.expand(C+2*(1-2*u)*(E.dot(Y)-lengths[2]*lengths[4]+deficits[3])) == 0
    assert sym.expand(Drow-2*u*(F.dot(Y)-lengths[6]*lengths[4]+deficits[5])) == 0
    assert sym.expand(T[4, 5]-(Y.dot(Y)-lengths[4]**2)) == 0
    Urow = 2*u*T[3, 4]+(1-2*u)*T[4, 6]-2*u*(1-2*u)*T[3, 6]
    Vrow = 2*u*T[3, 5]+(1-2*u)*T[5, 6]-2*u*(1-2*u)*T[3, 6]
    Srow = (T[4, 5]-2*u*T[3, 5]-(1-2*u)*T[5, 6]-2*u*T[3, 4]
            -(1-2*u)*T[4, 6]+4*u*(1-2*u)*T[3, 6])
    assert sym.expand(Urow+Vrow+Srow-T[4, 5]) == 0
    v = sym.Symbol('v')
    levels = [0, sym.Rational(1, 2), sym.Rational(1, 2), sym.Rational(1, 2), u, v, 0, 0]
    points = [point.col_join(sym.Matrix([level])) for point, level in zip(p, levels)]

    def cross(a, b):
        return sym.det(sym.Matrix.hstack(a, b))

    def bracket(quad):
        first, *rest = quad
        return sym.expand(sym.det(sym.Matrix.hstack(*(points[j]-points[first] for j in rest))))

    assert sym.expand(2*bracket((2, 3, 6, 7))-cross(E, F)) == 0
    assert sym.expand(2*bracket((0, 2, 3, 7))-cross(E, p[7])) == 0
    assert sym.expand(2*bracket((1, 2, 6, 7))-cross(p[2], F)) == 0
    assert sym.expand(2*bracket((2, 3, 4, 5)).subs(v, u)-(1-2*u)*cross(E, Y)) == 0
    assert sym.expand(bracket((4, 5, 6, 7)).subs(v, u)-u*cross(Y, F)) == 0
    return {'mark': 1, 'regular_C0_only': True, 'strict_metric_signs': METRIC_SIGNS,
            'diagonal_exclusion': '[2345]<=0 and [4567]<=0',
            'whole_C0_excluded': False}


def filter_cells(source, directory):
    record = json.loads(source.read_text())
    assert record['generic_models'] == 669 and len(record['cells']) == 18
    quads = tuple(map(tuple, record['quads']))
    assert quads == tuple(combinations(range(8), 4))
    metric_literals = [sign*cells.common.common.lit(quad) for quad, sign in METRIC_SIGNS]
    diagonal_clause = [cells.common.common.lit(quad) for quad in ((2, 3, 4, 5), (4, 5, 6, 7))]
    n, base, *_ = cells.common.base_formula()
    base += angles.cap_units(1)+[[literal] for literal in metric_literals]
    directory.mkdir(parents=True, exist_ok=True)
    output = {'strict_metric_signs': METRIC_SIGNS, 'cells': [], 'whole_C0_excluded': False}
    for index, cell in enumerate(record['cells']):
        assert cell['index'] == index and cell['anchor_word'] == cells.words()[index]
        formula = base+[[variable*sign] for variable, sign in
                        zip(angles.ANCHORS, cells.signed_word(cell['anchor_word']))]
        members = [member for member in cell['members']
                   if all(member[abs(literal)-1]*(1 if literal > 0 else -1) > 0
                          for literal in metric_literals)]
        diagonal = [member for member in members if any(member[literal-1] > 0
                                                        for literal in diagonal_clause)]
        assert len(members) == UNIFORM_COUNTS[index]
        assert len(diagonal) == DIAGONAL_COUNTS[index]
        for label, rows, extra in (('uniform', members, []), ('diagonal', diagonal, [diagonal_clause])):
            coverage = formula+extra+[[-(i+1)*sign for i, sign in enumerate(member)] for member in rows]
            # This deterministic order gives a RUP-only trace for the one
            # packet whose initial source order required a non-RUP step.
            if (index, label) == (9, 'uniform'):
                coverage.reverse()
            write_cnf(directory/f'cell_{index:02d}_{label}.cnf', n, coverage)
        output['cells'].append({'index': index, 'anchor_word': cell['anchor_word'],
                                'uniform_members': members, 'diagonal_members': diagonal})
    assert sum(len(cell['uniform_members']) for cell in output['cells']) == 202
    assert sum(len(cell['diagonal_members']) for cell in output['cells']) == 50
    (directory/'turning_cells.json').write_text(json.dumps(output, separators=(',', ':'))+'\n')
    return output


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('output', type=Path, nargs='?')
    parser.add_argument('--cells', type=Path)
    args = parser.parse_args()
    result = verify()
    if args.output is not None:
        if args.cells is None:
            parser.error('--cells is required with OUTPUT')
        filtered = filter_cells(args.cells, args.output)
        result.update(uniform_models=sum(len(cell['uniform_members']) for cell in filtered['cells']),
                      diagonal_models=sum(len(cell['diagonal_members']) for cell in filtered['cells']),
                      coverage_cnfs=36)
    print(json.dumps(result), flush=True)


if __name__ == '__main__':
    if not __debug__:
        raise RuntimeError('run with assertions enabled')
    main()
