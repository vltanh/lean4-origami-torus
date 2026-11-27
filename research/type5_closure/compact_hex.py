#!/usr/bin/env python3
"""Complete quadratic-metric/cubic-sign queries for Type 5 at the hexagon.

Examples:
  python compact_hex.py --b11 all --output /tmp/type5-b11.smt2
  python compact_hex.py --b11 1 --output /tmp/type5-b11-01.smt2
  python compact_hex.py --orbit 1 --output /tmp/type5-orbit-001.smt2

The orbit index is one-based in the historical 751-entry archive. Completeness
of that archive and its marking symmetries is inherited, not re-proved here.
"""
import argparse
import json
from itertools import combinations, product
from pathlib import Path
from verify_weak_chambers import SOURCE, V, Q, fs, audit, sign
from generate_base import op, add, mul, sub, neg, num, rat, all_, any_, determinant


def generate(patterns):
    lines = ['(set-logic QF_NRA)',
             '; Type 5 at the exact hexagonal metric, norm X^2+3Y^2+Z^2.',
             '; Complete within the selected weak orientation chambers.']

    def declare(name):
        lines.append(f'(declare-fun {name} () Real)')
        return name

    def define(name, expression):
        lines.append(f'(define-fun {name} () Real {expression})')
        return name

    def require(expression):
        lines.append(op('assert', expression))

    def difference(a, b):
        return [sub(x, y) for x, y in zip(a, b)]

    def dot(a, b):
        weights = ('1', '3', '1')
        return add(*(mul(weights[k], x, y) for k, (x, y) in enumerate(zip(a, b))))

    def norm(a):
        return dot(a, a)

    def physical(a, b):
        return [rat(2 * a + b, 2), rat(b, 2)]

    p = {i: ['0', '0'] if i == 1 else [declare(f'p{i}{k}') for k in range(2)] for i in V}
    anchor = {1, 2, 5}
    r = {i: p[i] + ['0'] if i in anchor else [declare(f'r{i}{k}') for k in range(3)] for i in V}

    def direction(i, j):
        return [add(x, k) for x, k in zip(difference(p[j], p[i]), physical(*fs.K[i, j]))]

    # Five radial norm equations and sixteen inner-product equations; all
    # are quadratic. The anchor triangle is aligned with its intrinsic lift.
    for j in V:
        if j not in anchor:
            require(op('=', norm(r[j]), norm(p[j])))
    for i, j in fs.E:
        if 1 not in (i, j) and not {i, j} <= anchor:
            k = physical(*fs.K[i, j])
            slack = sub(neg(dot(difference(p[j], p[i]), k)), mul('(/ 1 2)', norm(k)))
            require(op('=', dot(r[i], r[j]), add(dot(p[i], p[j]), slack)))
        u = direction(i, j)
        for a, b in ((1, 0), (0, 1), (-1, 1)):
            value = add(mul(num(2 * a + b), u[0]), mul(num(3 * b), u[1]))
            require(op('>', value, '(- 1)'))
            require(op('<', value, '1'))
    # Necessary diameter and nonedge contraction bounds. Positive circuits,
    # rather than a generic nonzero-bracket assumption, impose injectivity.
    for i, j in combinations(V, 2):
        distance = define(f'D{i}{j}', norm(difference(r[j], r[i])))
        require(op('<=', distance, '(/ 1 3)'))
        if (i, j) not in fs.E:
            for a, b in product(range(-1, 2), repeat=2):
                displacement = [add(x, y) for x, y in zip(difference(p[j], p[i]), physical(a, b))]
                require(op('<=', distance, norm(displacement)))
    areas = []
    for index, (i, j, k) in enumerate(fs.F):
        u, v = direction(i, j), direction(i, k)
        area = define(f'area{index}', sub(mul(u[0], v[1]), mul(u[1], v[0])))
        areas.append(area)
        require(op('<', area, '0'))
    require(op('=', add(*areas), '(- 1)'))

    minors = {}

    def minor(points, axes):
        key = points, axes
        if key not in minors:
            origin, *rest = points
            matrix = [[sub(r[i][k], r[origin][k]) for k in axes] for i in rest]
            name = 'br' + ''.join(map(str, points)) + 'c' + ''.join(map(str, axes))
            minors[key] = define(name, determinant(matrix))
        return minors[key]

    brackets = {q: minor(q, (0, 1, 2)) for q in Q}

    def exclude_circuit(positive, negative):
        points = tuple(sorted(positive + negative))
        assert len(points) == 4
        tests = []
        for axes in combinations(range(3), 2):
            coefficients = [minor(points[:i] + points[i + 1:], axes) for i in range(4)]
            signed = [c if ((i % 2 == 0) == (v in positive)) else neg(c)
                      for i, (v, c) in enumerate(zip(points, coefficients))]
            tests.append(any_([all_([op('>', c, '0') for c in signed]),
                               all_([op('<', c, '0') for c in signed])]))
        return op('not', all_([op('=', brackets[points], '0'), any_(tests)]))

    chambers = []
    summaries = []
    for pattern in patterns:
        strict, residual, rounds = audit(pattern)
        # The intrinsic orientation makes det(p2,p5)>0. Reflect space once
        # so bracket(1,2,5,3)>0, which removes no congruence class.
        reflection = sign(pattern, (1, 2, 5, 3))
        conditions = []
        for q, character in zip(Q, pattern):
            s = reflection * (1 if character == '+' else -1)
            comparison = ('>' if s > 0 else '<') if q in strict else ('>=' if s > 0 else '<=')
            conditions.append(op(comparison, brackets[q], '0'))
        conditions.extend(exclude_circuit(a, b) for a, b in residual)
        chambers.append(all_(conditions))
        summaries.append((len(strict), len(residual), rounds))
    require(any_(chambers))
    lines.append('(check-sat)')
    result = '\n'.join(lines) + '\n'
    assert result.count('(declare-fun') == 29
    return result, summaries


def main():
    parser = argparse.ArgumentParser()
    choice = parser.add_mutually_exclusive_group(required=True)
    choice.add_argument('--b11', help='all or a one-based B1.1 chamber index')
    choice.add_argument('--orbit', type=int, help='one-based historical archive index')
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    if args.b11:
        branches = json.loads((SOURCE / 'branch_ledger' / 'branches.json').read_text())
        patterns = next(b for b in branches if b['id'] == 'B1.1')['chambers']
        if args.b11 != 'all':
            index = int(args.b11)
            assert 1 <= index <= len(patterns)
            patterns = [patterns[index - 1]]
    else:
        archive = json.loads((SOURCE / 'full_sign_orbits5.json').read_text())
        assert 1 <= args.orbit <= len(archive)
        patterns = [archive[args.orbit - 1]]
    system, summaries = generate(patterns)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(system)
    print('Generated', len(patterns), 'complete weak chambers; 29 real variables.')
    print('(strict brackets, residual circuits, propagation rounds):', summaries)


if __name__ == '__main__':
    main()
