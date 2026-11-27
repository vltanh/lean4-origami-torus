#!/usr/bin/env python3
"""Exclude the final common-line blow-up with two noncollinear caps.

Usage: python remaining_two_triangles_blowup.py [OUTPUT_DIRECTORY]

The 16 exact zero-cone supports reduce to four patterns, all mapped to
one triangle pair with 0 < lambda < infinity. Exact direction/sign
implications and the regular metric argument are documented in
remaining_two_triangles_blowup.md. This is an asymptotic exclusion.
"""

from collections import Counter
from itertools import combinations
import json
from pathlib import Path
import sys

import sympy as s

import common_line_trapezoids
from remaining_one_v import DirectionalModel, topology
from remaining_two_triangles_metric import exact_checks
import solver_chambers as chambers
from verify_linking import SAT

A, B = (0, 1, 4, 5), (2, 3, 6, 7)
HALF = s.Rational(1, 2)
RELABEL = (1, 4, 7, 2, 5, 0, 3, 6)


def positive_parameter_sign(expression, parameter):
    """Certify a nonzero rational function's sign for every parameter > 0."""
    numerator, denominator = s.fraction(s.cancel(expression))

    def polynomial_sign(polynomial):
        coefficients = s.Poly(s.expand(polynomial), parameter).all_coeffs()
        assert any(coefficients)
        if all(value >= 0 for value in coefficients):
            return 1
        assert all(value <= 0 for value in coefficients), polynomial
        return -1

    return polynomial_sign(numerator)*polynomial_sign(denominator)


def shape_cover():
    """Map each entire positive-height family, not a sampled triangle."""
    parameter = s.symbols('lambda', positive=True)
    shapes = [
        (1, (0, 3), (0, 1),
         [(0, 0), (0, -1), (HALF, -1), (0, 0)],
         [(0, 0), (0, -parameter), (0, -parameter), (HALF, 0)]),
        (1, (1, 2), (2, 3),
         [(0, 0), (HALF, -1), (HALF, -1), (HALF, 0)],
         [(0, 0), (-HALF, -parameter), (0, -parameter), (0, 0)]),
        (-1, (0, 1), (1, 2),
         [(0, 0), (0, -1), (0, -1), (HALF, 0)],
         [(0, 0), (-HALF, parameter), (-HALF, parameter), (-HALF, 0)]),
        (-1, (2, 3), (0, 3),
         [(0, 0), (-HALF, -1), (0, -1), (0, 0)],
         [(0, 0), (0, parameter), (-HALF, parameter), (0, 0)]),
    ]
    phase = [row for row in chambers.marked_symmetries() if row['phase_preserving']]
    result = []
    for orientation, zeros_a, zeros_b, aa, bb in shapes:
        points = dict(zip(A, map(s.Matrix, aa))) | dict(zip(B, map(s.Matrix, bb)))
        for cap, expected in ((A, zeros_a), (B, zeros_b)):
            actual = tuple(i for i in range(4)
                           if points[cap[(i+1) % 4]][0] == points[cap[i]][0])
            assert actual == expected
        choices = []
        for symmetry in phase:
            permutation = symmetry['permutation']
            translated = {i: points[permutation[i]]-points[permutation[0 if i in A else 2]]
                          for i in range(8)}
            if (translated[5] != s.zeros(2, 1) or translated[1][0] != 0
                    or translated[4][1] != translated[1][1]
                    or translated[6] != translated[3] or translated[3][0] != 0
                    or translated[7][1] != 0):
                continue
            horizontal = s.cancel(translated[4][0]/HALF)
            normal = translated[1][1]
            if horizontal not in (-1, 1) or translated[7][0] != translated[4][0] or normal == 0:
                continue
            new_parameter = s.cancel(translated[3][1]/normal)
            if new_parameter not in (parameter, 1/parameter):
                continue
            change = s.diag(horizontal, -1/normal)
            canonical = {
                0: (0, 0), 1: (0, -1), 4: (HALF, -1), 5: (0, 0),
                2: (0, 0), 3: (0, -new_parameter),
                6: (0, -new_parameter), 7: (HALF, 0),
            }
            assert all(all(s.cancel(value) == 0 for value in
                           change*translated[i]-s.Matrix(canonical[i])) for i in range(8))
            choices.append({'permutation': permutation, 'horizontal_reflection': int(horizontal),
                            'normal_scale': str(-1/normal), 'new_lambda': str(new_parameter)})
        assert choices
        result.append({'orientation': orientation, 'zero_a_edges': zeros_a,
                       'zero_b_edges': zeros_b, 'canonical_map': choices[0]})
    assert len(result) == 4
    assert any(tuple(row['permutation']) == RELABEL for row in phase)

    # The selected relabeling has positive parity on the one bracket
    # used in the metric proof and produces the stated normal profile.
    mapped = tuple(RELABEL[i] for i in (0, 3, 4, 7))
    assert mapped == (1, 2, 5, 6)
    aa, bb = shapes[0][-2:]
    original = dict(zip(A, map(s.Matrix, aa))) | dict(zip(B, map(s.Matrix, bb)))
    translated = {i: original[RELABEL[i]]-original[RELABEL[0 if i in A else 2]]
                  for i in range(8)}
    assert [translated[i][0] for i in range(8)] == [0, HALF, 0, -HALF, 0, 0, -HALF, -HALF]
    assert [translated[i][1] for i in range(8)] == [0, 0, 0, 0, 1, 1, -parameter, -parameter]
    return result


def direction_model():
    parameter, epsilon, eta, ax, ay, bx, by = s.symbols('lambda epsilon eta ax ay bx by')
    vectors = [(1, 0), (0, 1), (HALF, -1), (HALF, parameter), (ax, ay), (bx, by)]
    forms, pairs = {}, {}
    for i, j in combinations(range(6), 2):
        expression = s.expand(vectors[i][0]*vectors[j][1]-vectors[i][1]*vectors[j][0])
        if expression.has(ax, ay, bx, by):
            name = f'p{i}{j}'
            forms[name], pairs[i, j] = expression, (name, 1)
        else:
            pairs[i, j] = positive_parameter_sign(expression, parameter)
    model = DirectionalModel.__new__(DirectionalModel)
    model.n, original = topology()
    model.clauses, model.trits = [list(row) for row in original], {}
    for key in forms:
        model.trits[key] = model.n+1, model.n+2
        model.n += 2
        model.clauses.append([-model.n+1, -model.n])
    model.clauses.append([*model.trits['p04'], *model.trits['p14']])
    model.clauses.append([*model.trits['p05'], *model.trits['p15']])
    model.rank_two_axioms(6, pairs)
    points = {
        0: (0, 0, 0), 1: (0, -1, 0), 4: (HALF, -1, 0),
        5: (-epsilon*ax, -epsilon*ay, 0),
        2: (0, 0, 1), 3: (0, -parameter, 1),
        6: (eta*bx, -parameter+eta*by, 1), 7: (HALF, 0, 1),
    }
    counts = Counter()
    for quad in chambers.Q:
        first, *rest = quad
        polynomial = s.expand(s.Matrix([[points[i][axis]-points[first][axis]
                                         for axis in range(3)] for i in rest]).det())
        for scale, pair in ((epsilon, {0, 5}), (eta, {3, 6})):
            if pair <= set(quad):
                polynomial = s.cancel(polynomial/scale)
                assert polynomial.is_polynomial(epsilon, eta, parameter, ax, ay, bx, by)
        leading = s.expand(polynomial.subs({epsilon: 0, eta: 0}))
        if not leading:
            counts['zero'] += 1
            continue
        if leading.has(ax, ay, bx, by):
            matches = []
            for key, form in forms.items():
                coefficient = s.cancel(leading/form)
                if not coefficient.has(ax, ay, bx, by):
                    matches.append((key, positive_parameter_sign(coefficient, parameter)))
            assert len(matches) == 1, (quad, leading, matches)
            model.bracket_link(chambers.lit(quad), *matches[0])
            counts['direction'] += 1
        else:
            model.clauses.append([chambers.lit(quad)*positive_parameter_sign(leading, parameter)])
            counts['constant'] += 1
    assert dict(counts) == {'constant': 36, 'direction': 27, 'zero': 7}
    return model, dict(counts)


def finite_checks():
    model, counts = direction_model()
    # p04=ay, p14=-ax, p05=by, p15=-bx.
    expected = {'p04': 0, 'p14': 1, 'p05': 0, 'p15': -1}
    violation = sum((model.deny(key, value) for key, value in expected.items()), [])
    violation.append(-chambers.lit((1, 2, 5, 6)))
    implication = model.clauses+[violation]
    assert SAT(model.n, implication).check() == -1

    # A small supplementary enumeration records all weak cap-sign choices.
    selector, models = SAT(model.n, model.clauses), []
    while selector.check() == 1:
        values = tuple(selector.model())
        assert len(values) == 70
        models.append(values)
        selector.add([-(i+1)*value for i, value in enumerate(values)])
    assert len(models) == 4
    cap_indices = {chambers.Q.index(A), chambers.Q.index(B)}
    for index in range(70):
        assert len({values[index] for values in models}) == (2 if index in cap_indices else 1)
    completions = model.clauses+[
        [-(i+1)*value for i, value in enumerate(values)] for values in models]
    assert SAT(model.n, completions).check() == -1
    print('PASS every lambda>0: both missing-base directions and [1256]>=0', flush=True)
    print('PASS exactly four generic completions; all 68 non-cap signs fixed', flush=True)
    return model.n, implication, completions, models, counts


def main():
    if len(sys.argv) > 2:
        raise SystemExit(__doc__)
    output = Path(sys.argv[1]) if len(sys.argv) == 2 else None
    if output:
        output.mkdir(parents=True, exist_ok=True)
    # This independently replays the entire 16-support antecedent cover.
    common_line_trapezoids.main()
    maps = shape_cover()
    n, implication, completions, models, counts = finite_checks()
    metric = exact_checks()
    if output:
        chambers.write_cnf(output/'two_triangles_implication.cnf', n, implication)
        chambers.write_cnf(output/'two_triangles_completions.cnf', n, completions)
        (output/'two_triangles_certificate.json').write_text(json.dumps({
            'shape_maps': maps, 'parameter_domain': '0 < lambda < infinity',
            'metric_relabel': RELABEL, 'counts': counts, 'metric': metric,
            'generic_completions': models}, indent=2)+'\n')
    print('PASS all 16 zero-cone supports with two noncollinear stretched caps', flush=True)
    print('Scope: unbounded-sequence blow-up exclusion; no explicit numerical height or Lean theorem')


if __name__ == '__main__':
    if not __debug__:
        raise RuntimeError('run with assertions enabled')
    main()
