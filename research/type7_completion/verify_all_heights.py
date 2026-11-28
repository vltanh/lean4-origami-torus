#!/usr/bin/env python3
"""Replay the full finite-height-tail sources, without deciding feasibility.

This binds the emitted metric equations to the original squared distances
as polynomial identities in t, checks all actual affine minors, and checks
the complete formulas against the preceding fixed-height implementation.
The latter comparison includes all Boolean clauses and actual circuits.
No t=0 specialization is used, and a successful replay is not an exclusion.
"""

from functools import lru_cache
import hashlib
import json
import re

import sympy as s

import exhaustive_remaining_axis as axis
from remaining_verify import parse_count
from verify_projected_metric import parse


# Captured from the unmodified fixed-height generator at PR commit 2d4aea7.
LEGACY = {
    (1, 32): '01a4b0aa6617732117f68936a2b394bcf938f4d97b75ce518b1ace453675b003',
    (1, 37): 'ae7ad285d80a33feaa00bc0d95cee37e02c2ef8a7c2bf8c14c0324d85add4849',
    (1, 1000000): '195774e41b430b1c279e63c229e79f9754d3392ae6ae49e41df1a882a7609c3c',
    (2, 32): 'bd6dacbcc228aa2e0dbe22654aa57ed6c6db65819b0967047f7e2792ed0ae863',
    (2, 37): 'a1e027e20e2319f944a669d6461dc149a36cde6d01dcf858259bfd13a5f3a0ce',
    (2, 1000000): '8a13f7befef754f1367daa188e64ab77ecd668de1b3c5434dfe32bef69609bf2',
}


def freeze(value):
    return tuple(map(freeze, value)) if isinstance(value, list) else value


@lru_cache(maxsize=None)
def polynomial(term):
    if isinstance(term, str):
        try:
            return s.Rational(term)
        except (TypeError, ValueError):
            return s.Symbol(term)
    operator, *arguments = term
    values = [polynomial(argument) for argument in arguments]
    if operator == '+':
        return s.Add(*values)
    if operator == '*':
        return s.Mul(*values)
    if operator == '-':
        return -values[0] if len(values) == 1 else values[0]-values[1]
    if operator == '/':
        assert len(values) == 2 and values[1].is_Rational and values[1] != 0
        return values[0]/values[1]
    raise ValueError(operator)


def normalizer(t_value=None):
    def normalize_polynomial(term):
        value = polynomial(term)
        if t_value is not None:
            value = value.subs(s.Symbol('t'), t_value)
        return ('polynomial', s.srepr(s.expand(value)))

    @lru_cache(maxsize=None)
    def normalize(term):
        if not term:
            return term
        if isinstance(term, str):
            if term == 't' and t_value is not None:
                return ('polynomial', s.srepr(t_value))
            return term
        if term[0] in ('+', '-', '*', '/'):
            try:
                return normalize_polynomial(term)
            except ValueError:
                pass  # Boolean-conditioned linking sums are identical schema.
        if term[0] in ('=', '<', '>', '<=', '>=', 'distinct') and len(term) == 3:
            try:
                return (term[0], normalize_polynomial(('-', term[1], term[2])))
            except ValueError:
                pass
        if term[0] == 'define-fun' and term[3] == 'Real':
            try:
                return (*term[:4], normalize_polynomial(term[4]))
            except ValueError:
                pass
        return tuple(normalize(child) for child in term)
    return normalize


def bind_metric_and_minors(forms, mark):
    t, w = s.symbols('t w')
    x = [s.Integer(0)]+list(s.symbols('x1:8'))
    v = [s.Integer(0)]+list(s.symbols('v1:8'))
    v[6] = v[3]-s.Rational(1, 2)
    z = list(v)
    z[4], z[5] = 2*v[3]-v[4], 2*v[3]-v[5]-1
    H = [s.Integer(0)]+list(s.symbols('H1:8'))
    omega = [s.Integer(0)]*8
    omega[6] = w
    p = [s.zeros(2, 1) for _ in range(8)]
    for i in (2, 4, 5, 6, 7):
        p[i] = s.Matrix(s.symbols(f'p{i}u p{i}v'))
    p[3] = s.Matrix([s.Symbol('p3u'), 0])
    points = [point.col_join(s.Matrix([z[i]+t*H[i]])) for i, point in enumerate(p)]
    shifts, _, edges = axis.case_data(mark)
    real_definitions = {row[1]: polynomial(freeze(row[4])) for row in forms
                        if row[0] == 'define-fun' and row[3] == 'Real'
                        and re.fullmatch(r'(?:[XVDz][0-7]{2}|m[0-7]{4}|a[0-7]+c[012]+)', row[1])}
    metric = [polynomial(freeze(row[1][1])) for row in forms
              if row[0] == 'assert' and row[1][0] == '=' and row[1][2] == '0']
    assert len(metric) == 24
    product_rows = [row[1] for row in forms if row[0] == 'assert'
                    and row[1][0] == '=' and isinstance(row[1][1], list)
                    and row[1][1][0] == '*' and 't' in row[1][1]
                    and any(isinstance(item, str) and item.startswith('q') for item in row[1][1])]
    assert len(product_rows) == 6
    products = {next(item for item in row[1] if isinstance(item, str) and item.startswith('q')):
                polynomial(freeze(row[2])) for row in product_rows}
    for (i, j), equation in zip(edges, metric):
        X = x[j]-x[i]+shifts[i, j][0]+s.Rational(shifts[i, j][1], 2)
        V = v[j]-v[i]+shifts[i, j][1]
        actual_V = V+t*(omega[j]-omega[i])
        assert s.expand(real_definitions[f'X{i}{j}']-X) == 0
        assert s.expand(real_definitions[f'V{i}{j}']-actual_V) == 0
        assert s.expand(real_definitions[f'D{i}{j}']-t*X**2-actual_V**2) == 0
        transverse = (p[j]-p[i]).dot(p[j]-p[i])
        original = t*(transverse-X**2)+(points[j][2]-points[i][2])**2-actual_V**2
        base_product = s.expand((z[j]-z[i])**2-V**2)
        name = f'q{i}{j}'
        if name in products:
            assert s.expand(products[name]-base_product) == 0
            correction = t*s.Symbol(name)-base_product
        else:
            assert base_product == 0
            correction = 0
        assert s.expand(t*equation-original-correction) == 0
        assert s.Poly(equation).total_degree() <= 3
    count = 0
    for name, value in real_definitions.items():
        if not name.startswith('a') or 'c' not in name:
            continue
        vertex_text, axis_text = name[1:].split('c')
        vertices, axes = tuple(map(int, vertex_text)), tuple(map(int, axis_text))
        origin, *others = vertices
        expected = s.Matrix([[points[j][k]-points[origin][k] for k in axes]
                             for j in others]).det()
        assert s.expand(value-expected) == 0
        assert not value.free_symbols or s.Poly(value).total_degree() <= 4
        count += 1
    assert count == 322
    return count


def verify():
    axis.verify()  # Uniform rational bounds and all marked gauge identities.
    records = []
    for mark in (1, 2):
        text, metadata = axis.generate(mark, 32, all_heights=True)
        forms = parse(text)
        assert parse_count(text) == 9361
        declarations = [row for row in forms if row[0] == 'declare-fun' and row[-1] == 'Real']
        assert len(declarations) == 39
        assert ['declare-fun', 't', [], 'Real'] in declarations
        t_bounds = [['assert', ['>', 't', '0']],
                    ['assert', ['<=', 't', ['/', '1', '1024']]]]
        assert all(forms.count(row) == 1 for row in t_bounds)
        assert metadata['necessary_system_only'] and not metadata['limit_at_zero']
        minors = bind_metric_and_minors(forms, mark)
        # The remaining entire formulas agree with the original fixed-y
        # sources. This includes weak actual-zero coupling and all circuits.
        trimmed = [row for row in forms if row not in t_bounds
                   and row != ['declare-fun', 't', [], 'Real']]
        for y in (32, 37, 1000000):
            fixed, _ = axis.generate(mark, y)
            assert hashlib.sha256(fixed.encode()).hexdigest() == LEGACY[mark, y]
            normalize_symbolic = normalizer(s.Rational(1, y*y))
            normalize_fixed = normalizer()
            left = [normalize_symbolic(freeze(row)) for row in trimmed]
            right = [normalize_fixed(freeze(row)) for row in parse(fixed)]
            assert left == right, (mark, y, next(i for i, pair in enumerate(zip(left, right))
                                               if pair[0] != pair[1]))
        records.append({'marking': mark, 'metric_identities_for_symbolic_t': 24,
                        'product_identities': 6, 'actual_minors': minors,
                        'actual_circuit_partitions': metadata['circuit_partitions'],
                        'legacy_specializations': 3, 'feasibility_decided': False})
    return records


if __name__ == '__main__':
    if not __debug__:
        raise RuntimeError('run with assertions enabled')
    print(json.dumps(verify()), flush=True)
    print('PASS full height-tail source replay; neither marking is excluded.')
