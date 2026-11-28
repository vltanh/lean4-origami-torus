#!/usr/bin/env python3
"""Keep the complete regular-C0 topology within each of 18 anchor cells.

Usage: python exhaustive_c0_cells.py OUTPUT [--queries --mark 1|2]

Exports one forced-sign and one complete-model coverage CNF per cell,
checked SAT witnesses for every nonunanimous sign, and exact decision
diagrams. Optional 20-real limiting queries retain all 70 weak signs.
No cell or marking is declared metrically infeasible.
"""

import argparse
from functools import lru_cache
from itertools import combinations
import json
from pathlib import Path
import time

import exhaustive_c0_angles as angles
import solver_remaining_chambers as common
from solver_chambers import write_cnf
from solver_sat import FastSAT

Q = tuple(combinations(range(8), 4))
EXPECTED_COUNTS = (68, 36, 37, 112, 80, 44, 1, 26, 7, 80, 48, 1, 7, 1, 36, 4, 37, 44)
EXPECTED_FIXED = (39, 52, 50, 34, 38, 40, 70, 61, 65, 38, 43, 70, 65, 70, 52, 68, 50, 40)


def words():
    return sorted(angles.EXPECTED, key=lambda word: tuple(1 if sign == '+' else -1 for sign in word))


def signed_word(word):
    return tuple(1 if sign == '+' else -1 for sign in word)


def valid_assignment(assignment, clauses):
    return all(any(assignment[abs(literal)-1]*(1 if literal > 0 else -1) > 0
                   for literal in clause) for clause in clauses)


def check_diagram(diagram, members, fixed):
    """Count every accepted generic word, then check every listed word.

    This differs from the producer's suffix-set construction. Counting
    skipped levels is essential: checking listed words alone would not
    detect additional accepted sign choices.
    """
    order, nodes, root = diagram['order'], diagram['nodes'], diagram['root']
    assert set(order) == set(range(70))-set(fixed)
    assert len(order) == len(set(order))
    position = {variable: index for index, variable in enumerate(order)}
    for identifier, (variable, high, low) in enumerate(nodes, 2):
        assert variable in position
        assert 0 <= high < identifier and 0 <= low < identifier and high != low

    @lru_cache(maxsize=None)
    def count(identifier, level):
        if identifier == 0:
            return 0
        if identifier == 1:
            return 2**(len(order)-level)
        variable, high, low = nodes[identifier-2]
        next_level = position[variable]
        assert next_level >= level
        return 2**(next_level-level)*(count(high, next_level+1)+count(low, next_level+1))

    assert count(root, 0) == len(members)
    assert len(set(members)) == len(members)
    for member in members:
        assert all(member[index] == sign for index, sign in fixed.items())
        identifier = root
        while identifier >= 2:
            variable, high, low = nodes[identifier-2]
            identifier = high if member[variable] > 0 else low
        assert identifier == 1


def topology_lines(cell, name):
    """Actual zero minors can take either branch; only cap units are strict."""
    lines = []
    strict = {abs(clause[0])-1 for clause in angles.cap_units(1)}
    for index, sign in cell['fixed']:
        operator = ('>' if sign > 0 else '<') if index in strict else ('>=' if sign > 0 else '<=')
        lines.append(f'(assert ({operator} {name(Q[index])} 0))')

    def child(identifier):
        return 'false' if identifier == 0 else 'true' if identifier == 1 else f'choice{identifier}'

    for identifier, (index, high, low) in enumerate(cell['diagram']['nodes'], 2):
        minor = name(Q[index])
        expression = (f'(or (and (>= {minor} 0) {child(high)}) '
                      f'(and (<= {minor} 0) {child(low)}))')
        lines.append(f'(define-fun choice{identifier} () Bool {expression})')
    lines.append(f"(assert {child(cell['diagram']['root'])})")
    return lines


def build(directory):
    started = time.monotonic()
    n, base, *_ = common.base_formula()
    positive = base+angles.cap_units(1)
    directory.mkdir(parents=True, exist_ok=True)
    cnf_directory = directory/'cnfs'
    cnf_directory.mkdir(exist_ok=True)
    cells, all_members = [], set()
    for index, word in enumerate(words()):
        units = [[variable*sign] for variable, sign in zip(angles.ANCHORS, signed_word(word))]
        formula = positive+units
        members, witnesses, seen = [], [], set()
        with FastSAT(n, formula) as solver:
            while solver.check() == 1:
                member = tuple(solver.model())
                members.append(member)
                literals = {(i+1)*sign for i, sign in enumerate(member)}
                if literals-seen:
                    assignment = solver.model(n)
                    assert tuple(assignment[:70]) == member
                    assert valid_assignment(assignment, formula)
                    witnesses.append(assignment)
                    seen |= literals
                solver.add([-(i+1)*sign for i, sign in enumerate(member)])
            assert solver.check() == -1
        members.sort()
        assert len(members) == EXPECTED_COUNTS[index]
        assert not all_members & set(members)
        all_members.update(members)
        fixed = {i: members[0][i] for i in range(70)
                 if all(member[i] == members[0][i] for member in members)}
        assert len(fixed) == EXPECTED_FIXED[index]
        needed = {sign*(i+1) for i in range(70) if i not in fixed for sign in (-1, 1)}
        represented = {(i+1)*sign for witness in witnesses for i, sign in enumerate(witness[:70])}
        assert needed <= represented
        diagram = common.decision_diagram(members, fixed)
        check_diagram(diagram, members, fixed)
        forced = formula+[[-(i+1)*sign for i, sign in sorted(fixed.items())]]
        coverage = formula+[[-(i+1)*sign for i, sign in enumerate(member)] for member in members]
        forced_name, coverage_name = f'cell_{index:02d}_forced.cnf', f'cell_{index:02d}_coverage.cnf'
        write_cnf(cnf_directory/forced_name, n, forced)
        write_cnf(cnf_directory/coverage_name, n, coverage)
        cell = {'index': index, 'anchor_word': word, 'members': members,
                'fixed': sorted(fixed.items()), 'diagram': diagram,
                'nonunanimity_witnesses': witnesses,
                'forced_cnf': forced_name, 'coverage_cnf': coverage_name}
        cells.append(cell)
        (directory/f'cell_{index:02d}_topology.smt2.inc').write_text(
            '\n'.join(topology_lines(cell, lambda quad: 'D'+''.join(map(str, quad))))+'\n')
    assert len(all_members) == 669
    result = {'assumptions': ['regular C0 endpoint caps', '0<u,v<1/2'],
              'asymptotic_limit_only': True, 'metric_exclusion': False,
              'quads': Q, 'boolean_variables': n, 'cells': cells,
              'generic_models': len(all_members), 'producer_seconds': time.monotonic()-started}
    (directory/'c0_full_cells.json').write_text(json.dumps(result, separators=(',', ':'))+'\n')
    return result


@lru_cache(maxsize=4)
def metric_prefix(mark, quarter=False):
    """Exact necessary metric prefix, sharing all geometry across the cells."""
    import sympy as sym
    import exhaustive_remaining_axis as axis
    import solver_remaining_limit as reduction

    shifts, faces, edges = axis.case_data(mark)
    assert edges == reduction.EDGES
    assert all(shifts[edge][1] == reduction.SHIFTS[edge][1] for edge in edges)
    u, v = sym.symbols('u v')
    x = [sym.Integer(0)]+list(sym.symbols('x1:8'))
    p = [sym.zeros(2, 1), sym.zeros(2, 1)]
    p.append(sym.Matrix(sym.symbols('p2x p2y')))
    p.append(sym.Matrix([sym.Symbol('p3x'), 0]))
    p.extend(sym.Matrix(sym.symbols(f'p{i}x p{i}y')) for i in range(4, 8))
    variables = x[1:]+[coordinate for point in p[2:] for coordinate in point if coordinate != 0]
    substitution = {u: sym.Rational(1, 4), v: sym.Rational(1, 4)} if quarter else {}
    if not quarter:
        variables += [u, v]
    assert len(variables) == (18 if quarter else 20)
    intrinsic = [0, sym.Rational(1, 2), sym.Rational(1, 2), sym.Rational(1, 2), 1-u, -v, 0, 0]
    levels = [0, sym.Rational(1, 2), sym.Rational(1, 2), sym.Rational(1, 2), u, v, 0, 0]
    points = [point.col_join(sym.Matrix([level])) for point, level in zip(p, levels)]
    horizontal, vertical, residuals = {}, {}, []
    for i, j in edges:
        horizontal[i, j] = x[j]-x[i]+shifts[i, j][0]+sym.Rational(shifts[i, j][1], 2)
        vertical[i, j] = intrinsic[j]-intrinsic[i]+shifts[i, j][1]
        horizontal[j, i], vertical[j, i] = -horizontal[i, j], -vertical[i, j]
        residuals.append(sym.expand((p[j]-p[i]).dot(p[j]-p[i])-horizontal[i, j]**2))
    h = [-horizontal[i, (i+1) % 8] for i in range(8)]
    assert sym.expand(sum(h)-sym.Rational(9-2*mark, 2)) == 0
    rows = reduction.closed_c0_rows().subs({reduction.A: 1-u, reduction.B: -v})
    values = [sym.Rational(1, 2)]*3+[1-u, -v, 0]
    assert all(sym.expand(value) == 0 for value in rows*reduction.original_system(values))
    metric = [sym.expand(value) for value in rows[:, :24]*sym.Matrix(residuals)]
    assert len(metric) == 12
    generators = tuple(dict.fromkeys([*variables, u, v]))
    assert all(sym.Poly(value, *generators).total_degree() <= 4 for value in metric)

    def smt(expression):
        return axis._smt(sym.expand(sym.sympify(expression).subs(substitution)))

    lines = ['(set-logic QF_NRA)']+[f'(declare-fun {variable} () Real)' for variable in variables]
    if not quarter:
        lines += ['(assert (> u 0))', '(assert (< u (/ 1 2)))',
                  '(assert (> v 0))', '(assert (< v (/ 1 2)))']
    for point in p[2:]:
        lines.append(f'(assert (<= {smt(point.dot(point))} 144))')
    for i, j in edges:
        for value in (horizontal[i, j], vertical[i, j]):
            lines.append(f'(assert (<= {smt(value)} (/ 1 2)))')
            lines.append(f'(assert (>= {smt(value)} (- (/ 1 2))))')
    lines += [f'(assert (>= {smt(value)} 0))' for value in h]
    areas = {}
    for i, j, k in faces:
        area = horizontal[i, j]*vertical[i, k]-horizontal[i, k]*vertical[i, j]
        areas[i, j, k] = sym.expand(area)
        lines.append(f'(assert (>= {smt(area)} 0))')
    assert sym.expand(sum(areas.values())-2) == 0
    assert sym.expand(2*areas[3, 1, 0]-(1-h[1]-h[2])) == 0
    lines += [f'(assert (= {smt(value)} 0))' for value in metric]
    lines += [f'(assert (= p3x {smt(1-h[1]-h[2])}))',
              '(assert (> p3x 0))', '(assert (< p2y 0))']
    for quad in Q:
        first, *rest = quad
        minor = sym.det(sym.Matrix.hstack(*(points[j]-points[first] for j in rest)))
        assert sym.Poly(sym.expand(minor), *generators).total_degree() <= 3
        lines.append(f"(define-fun D{''.join(map(str, quad))} () Real {smt(minor)})")
    return '\n'.join(lines)+'\n'


def verify_queries(record):
    """Parse every marking/parameter variant and check the known witness."""
    import sympy as sym
    from remaining_verify import parse_count

    parsed = []
    for mark in (1, 2):
        for quarter in (False, True):
            prefix = metric_prefix(mark, quarter)
            counts = []
            for cell in record['cells']:
                text = prefix+'\n'.join(topology_lines(cell, lambda quad: 'D'+''.join(map(str, quad))))
                text += '\n(check-sat)\n'
                assert text.count('(declare-fun ') == (18 if quarter else 20)
                counts.append(parse_count(text))
            parsed.append({'mark': mark, 'quarter': quarter, 'queries': len(counts),
                           'assertions': counts})
    example = angles.verify_regular_angular_counterexample()
    levels = [0, sym.Rational(1, 2), sym.Rational(1, 2), sym.Rational(1, 2),
              sym.Rational(1, 4), sym.Rational(1, 4), 0, 0]
    points = [sym.Matrix([sym.sympify(value) for value in point]+[level])
              for point, level in zip(example['P'], levels)]
    values = [int(sym.sign(sym.simplify(sym.Matrix.hstack(
        *(points[j]-points[quad[0]] for j in quad[1:])).det()))) for quad in Q]
    strict = {abs(clause[0])-1 for clause in angles.cap_units(1)}

    def accepts(cell, signs):
        if any(signs[i]*sign < 0 or (i in strict and signs[i] == 0) for i, sign in cell['fixed']):
            return False

        @lru_cache(maxsize=None)
        def walk(identifier):
            if identifier < 2:
                return bool(identifier)
            index, high, low = cell['diagram']['nodes'][identifier-2]
            return ((signs[index] >= 0 and walk(high))
                    or (signs[index] <= 0 and walk(low)))

        return walk(cell['diagram']['root'])

    for cell in record['cells']:
        assert not accepts(cell, values)
        zero_noncap = tuple(sign if i in strict else 0 for i, sign in enumerate(cell['members'][0]))
        assert accepts(cell, zero_noncap)
    return {'parsed': parsed, 'regular_angular_witness_rejected_by_all_cells': True,
            'all_noncap_zero_choices_preserved': True, 'nonlinear_search_performed': False}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('output', type=Path)
    parser.add_argument('--queries', action='store_true')
    parser.add_argument('--mark', type=int, choices=(1, 2), default=1)
    parser.add_argument('--quarter', action='store_true')
    parser.add_argument('--verify-queries', action='store_true')
    args = parser.parse_args()
    result = build(args.output)
    if args.queries:
        prefix = metric_prefix(args.mark, args.quarter)
        for cell in result['cells']:
            text = prefix+'\n'.join(topology_lines(cell, lambda quad: 'D'+''.join(map(str, quad))))
            text += '\n(check-sat)\n'
            (args.output/f"ray{args.mark}_cell_{cell['index']:02d}.smt2").write_text(text)
    if args.verify_queries:
        (args.output/'query_verification.json').write_text(json.dumps(verify_queries(result), indent=2)+'\n')
    print(json.dumps({'cells': len(result['cells']), 'generic_models': result['generic_models'],
                      'forced_signs': [len(cell['fixed']) for cell in result['cells']],
                      'decision_nodes': [len(cell['diagram']['nodes']) for cell in result['cells']],
                      'cnfs': 36, 'producer_seconds': result['producer_seconds'],
                      'metric_exclusion': False}), flush=True)


if __name__ == '__main__':
    if not __debug__:
        raise RuntimeError('run with assertions enabled')
    main()
