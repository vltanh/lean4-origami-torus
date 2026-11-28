#!/usr/bin/env python3
"""Exact symbolic replay of both shared ray-1/2 quadratic face charts.

This checks polynomial identities, degree bounds, all 322 coordinate
minors, and literal preservation of every unaffected original condition.
It also parses all 28 marking/mask/anchor queries. No NRA search is used.
"""

from itertools import combinations, permutations
import re
import sympy as sym

import solver_remaining_face as producer
from remaining_verify import parse_count
from verify_projected_metric import evaluate, parse


def determinant(matrix):
    size = len(matrix)
    return sum((-1)**sum(p[i] > p[j] for i, j in combinations(range(size), 2))
               *sym.prod(matrix[i][p[i]] for i in range(size))
               for p in permutations(range(size)))


def is_metric(form):
    return (form[0] == 'assert' and len(form[1]) == 3 and form[1][0] == '='
            and isinstance(form[1][2], str) and re.fullmatch(r'D[0-7]{2}', form[1][2]))


def unchanged_conditions(text, mark, mask, y):
    """Bind the rewrite to the full original query, not a reduced fixture."""
    original, _ = producer.original.generate(mark, mask, y)
    before = parse(original.split('(define-fun G11 () Real', 1)[0])
    prefix, suffix = text.split('(declare-fun b1 () Bool)', 1)
    after = []
    for form in parse(prefix):
        if form[0] == 'declare-fun' and re.fullmatch(r'p[0-7]_[012]', form[1]):
            continue
        if form[0] == 'define-fun' and re.fullmatch(r'z[0-7]{2}', form[1]):
            after.append(['declare-fun', form[1], [], 'Real'])
        elif form[0] == 'define-fun' and re.fullmatch(r'm[0-7]{4}', form[1]):
            continue
        elif (form[0] == 'assert' and form[1][0] == 'distinct'
              and re.fullmatch(r'm[0-7]{4}', form[1][1])):
            continue
        elif not is_metric(form):
            after.append(form)
    assert before == after
    old_suffix = original.split('(declare-fun b1 () Bool)', 1)[1]

    def without_minors(source):
        return [line for line in source.splitlines()
                if not re.match(r'\(define-fun a[0-7]+c[012]+ ', line)]

    assert without_minors(suffix) == without_minors(old_suffix)
    assert text.count('(assert (ite b') == 70
    assert len(re.findall(r'^\(declare-fun \S+ \(\) Bool\)', text, re.M)) == 382
    assert sum(line.startswith('(assert (<= z') for line in text.splitlines()) == 252


def exact_chart(mark, anchor, y=10**6):
    text, metadata = producer.generate(mark, '03', y, anchor)
    forms = parse(text)
    declarations = [form[1] for form in forms
                    if form[0] == 'declare-fun' and form[3] == 'Real']
    assert len(declarations) == 29
    environment = {name: sym.Symbol(name) for name in declarations}
    variables = tuple(environment.values())
    x = [sym.Integer(0)]+[environment[f'x{i}'] for i in range(1, 8)]
    v = [sym.Integer(0)]+[environment[f'v{i}'] for i in range(1, 8)]
    shifts, faces, edges = producer.case_data(mark)
    anchors = tuple(map(int, anchor))
    assert anchors[0] == 0 and any(set(face) == set(anchors) for face in faces)
    points = {0: (sym.Integer(0),)*3}
    for i in range(1, 8):
        if i in anchors:
            m, n = shifts[0, i]
            points[i] = ((x[i]+m+sym.Rational(n, 2))/y, v[i]+n, sym.Integer(0))
        else:
            points[i] = tuple(environment[f'p{i}_{axis}'] for axis in range(3))

    def distance(i, j):
        return sum((points[j][axis]-points[i][axis])**2 for axis in range(3))

    def intrinsic(i, j):
        m, n = shifts[i, j]
        return (x[j]-x[i]+m+sym.Rational(n, 2))**2/y**2+(v[j]-v[i]+n)**2

    def degree(value):
        return sym.Poly(value, *variables).total_degree()

    metrics, minors, cliques, nonedges = set(), set(), set(), set()
    for form in forms:
        if form[0] == 'define-fun' and form[3] == 'Real':
            name = form[1]
            if name == 'long_link':
                continue  # Its Boolean arithmetic is preserved verbatim.
            environment[name] = evaluate(form[4], environment)
            match = re.fullmatch(r'a([0-7]+)c([012]+)', name)
            if match:
                support, axes = (tuple(map(int, value)) for value in match.groups())
                first, *rest = support
                expected = determinant([[points[i][axis]-points[first][axis]
                                         for axis in axes] for i in rest])
                assert sym.expand(environment[name]-expected) == 0, name
                assert degree(environment[name]) <= len(axes)
                minors.add((support, axes))
            elif re.fullmatch(r'm[0-7]{4}', name):
                support = tuple(map(int, name[1:]))
                first, *rest = support
                expected = determinant([[points[i][axis]-points[first][axis]
                                         for axis in range(3)] for i in rest])
                assert sym.expand(environment[name]-expected) == 0
                assert degree(environment[name]) <= 3
                cliques.add(support)
            elif re.fullmatch(r'z[0-7]{2}', name):
                i, j = map(int, name[1:])
                assert sym.expand(environment[name]-distance(i, j)) == 0
                assert degree(environment[name]) <= 2
                nonedges.add((i, j))
        elif is_metric(form):
            i, j = map(int, form[1][2][1:])
            residual = evaluate(form[1][1], environment)-environment[form[1][2]]
            assert sym.expand(residual-(distance(i, j)-intrinsic(i, j))) == 0
            assert degree(residual) <= 2
            metrics.add((i, j))
    assert metrics == set(edges)-set(combinations(anchors, 2)) and len(metrics) == 21
    assert all(sym.expand(distance(i, j)-intrinsic(i, j)) == 0
               for i, j in combinations(anchors, 2))
    assert nonedges == {(0, 4), (1, 5), (2, 6), (3, 7)}
    assert cliques == {quad for quad in combinations(range(8), 4)
                       if set(combinations(quad, 2)) <= set(edges)}
    assert minors == {(support, axes) for size in (1, 2, 3)
                      for support in combinations(range(8), size+1)
                      for axes in combinations(range(3), size)}
    assert len(minors) == 322 and len(cliques) == 16
    assert metadata['metric_degree_bound'] == 2
    # Scaling every spatial coordinate by positive 1/y multiplies a
    # k-dimensional affine minor by exactly y**(-k), preserving zeros.
    scale = sym.Symbol('s', positive=True)
    generic = sym.Matrix(3, 3, lambda i, j: sym.Symbol(f'q{i}{j}'))
    for size in (1, 2, 3):
        matrix = generic[:size, :size]
        assert sym.expand((scale*matrix).det()-scale**size*matrix.det()) == 0
    print(f'PASS ray{mark}, face{anchor}: 21 quadratic metrics, 322 exact minors, all zero boundaries', flush=True)


def main():
    for mark in (1, 2):
        for anchor in ('013', '023'):
            exact_chart(mark, anchor)
            for mask in producer.m.MASKS:
                text, _ = producer.generate(mark, mask, anchor=anchor)
                unchanged_conditions(text, mark, mask, 10**6)
                count = parse_count(text)
            print(f'PASS ray{mark}, face{anchor}: seven full queries preserve original conditions and parse ({count} assertions)', flush=True)
    print('No marking or mask exclusion is claimed.')


if __name__ == '__main__':
    if not __debug__:
        raise RuntimeError('run with assertions enabled')
    main()
