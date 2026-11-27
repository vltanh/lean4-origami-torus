#!/usr/bin/env python3
"""Exact algebra and output checks for f1_algebra_projective.py; no UNSAT claim."""
from itertools import combinations
import json
import sympy as s
import f1_algebra_projective as p


def evaluate(expression, values):
    if isinstance(expression, str):
        if expression in values:
            return values[expression]
        if expression in ('true', 'false'):
            return expression == 'true'
        return s.Rational(expression)
    op, *args = expression
    args = [evaluate(a, values) for a in args]
    if op == '+':
        return sum(args)
    if op == '*':
        return s.prod(args)
    if op == '-':
        return -args[0] if len(args) == 1 else args[0] - args[1]
    if op in ('/', 'positive_div'):
        if op == 'positive_div':
            assert args[1] > 0
        return args[0] / args[1]
    if op == 'and':
        return all(args)
    if op == 'or':
        return any(args)
    if op == 'not':
        return not args[0]
    if op == '=>':
        return not args[0] or args[1]
    if op == 'ite':
        return args[1] if args[0] else args[2]
    return {'=': lambda: args[0] == args[1],
            'distinct': lambda: args[0] != args[1],
            '>': lambda: args[0] > args[1],
            '>=': lambda: args[0] >= args[1],
            '<': lambda: args[0] < args[1],
            '<=': lambda: args[0] <= args[1]}[op]()


def check_polynomializer():
    # Both signs of a variable divisor are essential to the reduction.
    expressions = p.parse('''
      (+ (/ x d) (/ y e))
      (- (/ x d) (/ y e))
      (* (/ x d) (/ y e))
      (/ (+ x y) (- d e))
      (/ (/ x d) (/ y e))
    ''')
    for d in (-3, 2):
        for e in (-2, 5):
            values = dict(x=s.Rational(3, 7), y=s.Rational(-5, 11), d=s.Rational(d), e=s.Rational(e))
            for expression in expressions:
                n, denominator = p.Polynomialize().arithmetic(expression)
                nn = evaluate(p.parse(n)[0], values)
                dd = evaluate(p.parse(denominator)[0], values)
                assert dd > 0
                assert nn / dd == evaluate(expression, values)
                for comparison in ('=', 'distinct', '<', '<=', '>', '>='):
                    query = [comparison, expression, ['/', 'y', 'd']]
                    transformed = p.Polynomialize().boolean(query)
                    assert evaluate(query, values) == evaluate(p.parse(transformed)[0], values)
    # Positive compound denominators must remain opaque.  Factoring them
    # into signed x,y,z and using their ordinary monomial LCM would wrongly
    # produce the negative denominator x*y*z in this example.
    expression = p.parse('(+ (positive_div 1 (* x y)) (positive_div 1 (* x z)))')[0]
    polynomial = p.Polynomialize()
    nn, dd = polynomial.arithmetic(expression)
    values = {name: s.Rational(-1) for name in ('x', 'y', 'z')}
    assert evaluate(p.parse(dd)[0], values) > 0
    assert evaluate(p.parse(nn)[0], values)/evaluate(p.parse(dd)[0], values) == 2
    assert len(polynomial.denominators[dd]) == 2
    # Shared squared divisors survive aliases and are used once in a mixed
    # sum, instead of being multiplied into a fourth or sixth power.
    polynomial = p.Polynomialize()
    for command in p.parse('(define-fun a () Real (/ x d)) (define-fun b () Real (/ y d)) (define-fun c () Real (+ a b 1))'):
        polynomial.command(command)
    assert list(polynomial.denominators[polynomial.env['c'][1]].values()) == [1]
    assert polynomial.boolean(p.parse('(> a b)')[0]) == '(> a_n b_n)'
    values = dict(x=s.Rational(2), y=s.Rational(3), d=s.Rational(-7))
    for command in p.parse('\n'.join(polynomial.lines)):
        if command[0] == 'define-fun':
            values[command[1]] = evaluate(command[-1], values)
    cn, cd = polynomial.env['c']
    assert values[cd] > 0 and values[cn]/values[cd] == s.Rational(2, 7)
    print('PASS signed rational elimination and polynomial comparisons')
    print('PASS positive-atom denominator LCM, repeated aliases, and negative-factor counterexample')


def check_symbolic():
    a, b, c = s.symbols('a b c', nonzero=True)
    matrix = s.Matrix([[0, 0, a, b], [0, 0, 0, c], [a, 0, 0, 0], [b, c, 0, 0]])
    inverse_scaled = s.Matrix([[0, 0, c, 0], [0, 0, -b, a], [c, -b, 0, 0], [0, a, 0, 0]])
    assert matrix * inverse_scaled == a*c*s.eye(4)
    # Independent cofactor certificate for denominator coverage.  The six
    # columns have a five-dimensional Gram representation of rank five;
    # removing the final column leaves a unitriangular change of basis.
    hh = s.Matrix(s.symbols('h0:4'))
    theta = s.Matrix(s.symbols('theta0:4'))
    tt, rr, ww = s.symbols('t r w', nonzero=True)
    hk = inverse_scaled*hh/(a*c)
    transform = s.zeros(5, 6)
    transform[:4, :4] = s.eye(4)
    transform[:4, 4] = hk
    transform[:4, 5] = tt*hk + theta
    transform[4, 4], transform[4, 5] = 1, tt
    kernel = s.Matrix([-value for value in theta] + [-tt, 1])
    assert transform*kernel == s.zeros(5, 1)
    assert transform[:, :5].det() == 1
    assert s.simplify(matrix.det()*rr/(a*c) - a*c*rr) == 0
    assert s.diag(-1, -1/ww).det() == 1/ww
    for position in range(4):
        denominator = -a*c*theta[position]
        assert s.simplify(ww*a*c*rr*theta[position]**2
                          - ww*rr*denominator**2/(a*c)) == 0
    print('PASS symbolic cofactor denominator coverage: det G = w*r*D^2/(A*C)')
    ak, al, ck, cl, t = s.symbols('ak al ck cl t')
    denominator, numerator = al-t*ak, t*ck-cl
    assert s.expand(denominator*(cl-t*ck)+numerator*(al-t*ak)) == 0
    assert s.expand(denominator*ck+numerator*ak-(al*ck-ak*cl)) == 0
    # The same factor covers every Schur complement entry; no sign choice
    # or square root remains after requiring r>0.
    r, vi, vj, dij, ni = s.symbols('r vi vj dij ni', nonzero=True)
    assert s.simplify((r*dij-vi*vj)/r - (dij-vi*vj/r)) == 0
    print('PASS symbolic pivot inverse, linear elimination, and rank-one identities')
    a0, a1, a3, a5, b0, b2, b5, alpha, beta = s.symbols('a0 a1 a3 a5 b0 b2 b5 alpha beta')
    five = s.Matrix([[0, 0, a0, b0, a5], [0, 0, 0, a1, b5],
                     [a0, 0, 0, 0, b2], [b0, a1, 0, 0, a3],
                     [a5, b5, b2, a3, 0]])
    residual = b0*b2*b5-a0*a3*b5-a1*a5*b2
    assert s.expand(five.det()-2*a0*a1*residual) == 0
    assert s.expand(residual.subs({a0: 0, a1: alpha*b0, b5: alpha*a5+beta*b2}, simultaneous=True)
                    - beta*b0*b2*b2) == 0
    assert s.expand(residual.subs({a1: 0, a0: beta*b0, b2: alpha*b5+beta*a3}, simultaneous=True)
                    - alpha*b0*b5*b5) == 0
    print('PASS additional five-ray cubic inequality identity and both zero-slack cases')


def check_localization():
    union = p.f1_localization()
    witnesses = json.loads((p.HERE.parent/'type5_focus/fixed_elongated/phase_witnesses.json').read_text())
    cells = [(a, q) for a, q in sorted(p.old.rep) if ''.join(map(str, a)) in p.F1_CELLS]
    for index, (a, q) in enumerate(cells):
        label = ''.join(map(str, a))
        raw = list(map(s.Rational, witnesses[label]))
        values = {'b1': s.Rational(0)}
        for j, i in enumerate(v for v in p.old.V if v != 1):
            values[f'x{i}'] = raw[j]
            values[f'b{i}'] = s.Rational(a[i]-a[1], 4)+q[i]+raw[j+7]/10**6
        assert evaluate(union[index+1], values), label
        assert evaluate(union, values)
    print('PASS five-cell localization in common normalized coordinates on all five exact phase witnesses')


def signed_example(w, swap=False):
    metric = s.diag(1, 1, 1, -1, -1)
    first = s.eye(5)
    first[2, 2] = first[3, 3] = s.Rational(5, 3)
    first[2, 3] = first[3, 2] = s.Rational(4, 3)
    second = s.eye(5)
    second[2, 2] = second[4, 4] = s.Rational(13, 5)
    second[2, 4] = second[4, 2] = s.Rational(12, 5)
    transform = second * first
    if swap:
        permutation = s.eye(5)
        permutation.row_swap(3, 4)
        transform = permutation * transform
    assert transform.T * metric * transform == metric
    vectors = {
        2: s.Matrix([1, 0, 0, 1, 0]),
        5: s.Matrix([0, 1, 0, 0, 1]),
        7: s.Matrix([s.Rational(1, 2), 0, 0, s.Rational(-1, 2), 0]),
        4: s.Matrix([s.Rational(1, 2), s.Rational(1, 2), 0, s.Rational(-1, 2), s.Rational(-1, 2)]),
    }
    vectors = {i: transform * value for i, value in vectors.items()}
    vectors.update({
        1: s.zeros(5, 1),
        0: s.Matrix([s.Rational(2, 3), s.Rational(2, 3), s.Rational(1, 3), 1, 0]),
        3: s.Matrix([s.Rational(1, 3), s.Rational(2, 3), s.Rational(2, 3), 0, 1]),
        6: s.Matrix([s.Rational(2, 3), s.Rational(1, 3), s.Rational(2, 3), s.Rational(3, 5), s.Rational(4, 5)]),
        8: s.Matrix([0, 0, 0, -1, 0]),
        9: s.Matrix([0, 0, 0, 0, -1/s.sqrt(w)]),
    })
    assert all((value.T*metric*value)[0] == 0 for i, value in vectors.items() if i < 8)
    return metric, vectors


def check_exact_core(w, swap):
    signed_metric, vectors = signed_example(w, swap)
    H = lambda i, j: (vectors[i].T*signed_metric*vectors[j])[0]
    matrix = s.Matrix([[H(i, j) for j in p.BASIS] for i in p.BASIS])
    ac = H(2, 7)*H(5, 4)
    inverse = matrix.inv()
    residual = lambda i, j: ac*(H(i, j) - (s.Matrix([[H(i, k) for k in p.BASIS]]) * inverse
                                         * s.Matrix([H(k, j) for k in p.BASIS]))[0])
    chart = max((8, 9), key=lambda i: residual(i, i))
    ratio = residual(chart, 17-chart)/residual(chart, chart)
    assert residual(chart, chart) > 0 and abs(ratio) <= 1
    audit = {}
    p.generate(w=w, chart=chart, full=False, audit=audit)
    values = {'pc_t': ratio}
    for i in range(8):
        values[f'x{i}'] = H(i, 8)
        values[f'b{i}'] = H(i, 9)
    for i, j in combinations(range(8), 2):
        values[f's1_{i}{j}'] = H(i, j)
    for command in audit['injection']:
        if command[0] == 'define-fun':
            values[command[1]] = evaluate(command[-1], values)
        elif command[0] == 'assert':
            assert evaluate(command[1], values), (w, chart, command)
    for key, expression in audit['substitutions'].items():
        assert evaluate(expression, values) == values[key], key
    for expression in audit['metric']:
        assert evaluate(expression, values)
    for command in audit['coordinate_definitions']:
        values[command[1]] = evaluate(command[-1], values)
    homogeneous = {i: s.Matrix([evaluate(value, values) for value in row])
                   for i, row in audit['coordinates'].items()}
    assert all(row[5] > 0 for row in homogeneous.values())
    coordinates = {i: s.Matrix(row[:5])/row[5] for i, row in homogeneous.items()}
    reconstructed_metric = s.diag(1, 1, 1, 1, 1/(ac*residual(chart, chart)))
    reconstructed_metric[:4, :4] = inverse
    for i in range(8):
        for j in range(8):
            assert (coordinates[i].T*reconstructed_metric*coordinates[j])[0] == (
                vectors[i][:3, 0].T*vectors[j][:3, 0])[0]
    incident_homogeneous = {i: s.Matrix([evaluate(value, values) for value in row])
                           for i, row in audit['incidence_coordinates'].items()}
    assert incident_homogeneous[3][3] != 0
    assert all(row[3] == 1 for i, row in incident_homogeneous.items() if i != 3)
    incident = {i: s.Matrix(row[:3])/row[3] for i, row in incident_homogeneous.items()}
    anchor_metric = s.Matrix([[(vectors[i][:3, 0].T*vectors[j][:3, 0])[0]
                              for j in (2, 5, 4)] for i in (2, 5, 4)])
    assert anchor_metric.det() > 0
    for i in range(8):
        assert incident[i] == s.Matrix([(vectors[j][:3, 0].T*vectors[i][:3, 0])[0]
                                        for j in (2, 5, 4)])
        for j in range(8):
            assert (incident[i].T*anchor_metric.inv()*incident[j])[0] == (
                vectors[i][:3, 0].T*vectors[j][:3, 0])[0]
    # Positive homogeneous scaling preserves determinant signs and zeros,
    # including every axis choice used by the complete circuit tests.
    for count in range(2, 6):
        for vertices in combinations(range(8), count):
            for axes in combinations(range(5), count-1):
                unscaled = s.Matrix([[coordinates[i][axis] for axis in axes]+[1] for i in vertices])
                scaled = s.Matrix([[homogeneous[i][axis] for axis in axes]+[homogeneous[i][5]] for i in vertices])
                assert scaled.det() == s.prod(homogeneous[i][5] for i in vertices)*unscaled.det()
    print(f'PASS exact rank-three sample: w={w}, chart={chart}, four recovered slacks, all Gram entries and affine minors')


def check_circuit_pruning():
    vertices = range(8)
    cliques = {quad for quad in combinations(vertices, 4)
               if all(edge in p.old.E for edge in combinations(quad, 2))}
    assert len(cliques) == 23
    assert all(any(set(edge) <= set(face) for face in p.old.faces) for edge in p.old.E)
    clique_triples = {tri for tri in combinations(vertices, 3)
                      if all(edge in p.old.E for edge in combinations(tri, 2))}
    extra = json.loads((p.HERE/'coverage.json').read_text())['nonclique_triples_with_antipodal_obstruction']
    strict = clique_triples | {tuple(sorted(tri)) for tri in extra}
    assert len(strict) == 55
    for tri in combinations(vertices, 3):
        if any(edge in p.old.E for edge in combinations(tri, 2)):
            assert tri in strict
        else:
            assert tri == (0, 6, 7)
    print('PASS circuit pruning: all pairs distinct, all relevant triples noncollinear, 23 clique quadruples independent')
    totals = {}
    for count in (4, 5):
        support_total, simplex_total = 0, 0
        for subset in combinations(vertices, count):
            if subset in cliques:
                continue
            support = set(p.circuit_partitions(subset, simplex=False, support=True))
            simplex = set(p.circuit_partitions(subset, simplex=True, support=False))
            assert not support & simplex
            assert all(subset[0] in part for part in support | simplex)
            for vertex in subset:
                neighbors = tuple(i for i in subset if i != vertex)
                if all(tuple(sorted((vertex, other))) in p.old.E for other in neighbors):
                    canonical = (vertex,) if vertex == subset[0] else neighbors
                    assert canonical in support
            support_total += len(support)
            simplex_total += len(simplex)
        totals[count] = support_total, simplex_total
    assert totals == {4: (83, 126), 5: (150, 138)}, totals
    print('PASS strict-support cover: 83 four-point and 150 five-point additional partitions, including size-four positive parts')


def check_signed_circuit_signs():
    """Exhaust both signs of D3 and every cofactor zero/sign stratum.

    Replacing the positive D3^2 row by its signed quotient by D3 changes
    every cofactor except the one omitting vertex 3 by that same factor.
    The production predicate instead multiplies the affine coefficient at
    vertex 3 by its row weight.  The two sign vectors differ only by a common
    nonzero factor, absorbed by the two-sided circuit predicate.
    """
    from itertools import product

    truth = {}
    for special, positive, denominator_sign, raw in product(
            (False, True), (False, True), (-1, 1), (-1, 0, 1)):
        expression = p.parse(p.signed_cofactor_test('c', 3 if special else 10, positive))[0]
        actual = bool(evaluate(expression, {'c': raw, 'pc_den3_positive': denominator_sign > 0}))
        corrected = raw * (denominator_sign if special else 1)
        assert actual == (corrected > 0 if positive else corrected < 0)
        truth[special, positive, denominator_sign, raw] = actual

    checked = 0
    for count in range(2, 6):
        # -1 also checks supports which do not contain vertex 3.
        for special in range(-1, count):
            for mask in range(1, 1 << count, 2):
                if mask == (1 << count) - 1:
                    continue
                desired = [((i % 2 == 0) == bool(mask & (1 << i))) for i in range(count)]
                for denominator_sign in (-1, 1):
                    for raw in product((-1, 0, 1), repeat=count):
                        positive_row = [value * (denominator_sign if special >= 0 and i != special else 1)
                                        for i, value in enumerate(raw)]
                        expected = any(all((value > 0 if want == direction else value < 0)
                                           for value, want in zip(positive_row, desired))
                                       for direction in (True, False))
                        actual = any(all(truth[i == special, want == direction, denominator_sign, value]
                                         for i, (value, want) in enumerate(zip(raw, desired)))
                                     for direction in (True, False))
                        assert actual == expected, (count, special, mask, denominator_sign, raw)
                        checked += 1
    assert checked == 50112, checked
    print('PASS signed circuit correction: 50112 cases, both denominator signs and all zero-cofactor strata')


def check_square_support():
    """Replay all 233 support tests on an exact positive Type 5 embedding.

    The existing square certificate encloses its radical coordinates with
    integer intervals at scale 2^200.  No floating-point sign or tolerance is
    used here.  The square uses another marking, which is harmless because
    strict support and these circuit tests depend only on the labeled graph.
    """
    import contextlib
    import io
    import runpy

    source = (p.HERE.parent / 'torus_type5_reconstruction_certificate'
              / 'type5_algebraic_certificate' / 'verify.py')
    with contextlib.redirect_stdout(io.StringIO()):
        model = runpy.run_path(str(source))
    points = dict(model['r'])
    for vertex, (_, _, spatial) in zip(model['L'], model['wins'][0]):
        points[vertex] = spatial
    assert model['E'] == set(p.old.E)
    subtract, determinant = model['sub'], model['det3']
    brackets = {}
    for subset in combinations(range(8), 4):
        a, b, c, d = subset
        interval = determinant(subtract(points[b], points[a]),
                               subtract(points[c], points[a]),
                               subtract(points[d], points[a]))
        # sign() asserts that the entire integer interval is strictly on one
        # side of zero.  This also independently replays general position.
        brackets[subset] = interval.sign()
    totals = {4: 0, 5: 0}
    for count in (4, 5):
        for subset in combinations(range(8), count):
            if count == 4 and all(edge in p.old.E for edge in combinations(subset, 2)):
                continue
            parts = p.circuit_partitions(subset, simplex=False, support=True)
            if count == 4:
                # Nonzero affine rank makes every four-point circuit premise
                # false, regardless of its proposed singleton partition.
                assert brackets[subset] in (-1, 1)
                totals[count] += len(parts)
                continue
            cofactors = [(-1)**i * brackets[subset[:i] + subset[i+1:]]
                         for i in range(5)]
            for first in parts:
                signed = [cofactors[i] if vertex in first else -cofactors[i]
                          for i, vertex in enumerate(subset)]
                # Either common sign would certify the forbidden convex
                # dependence.  A common global determinant convention does
                # not affect this two-sided test.
                assert len(set(signed)) != 1, (subset, first)
                totals[count] += 1
    assert totals == {4: 83, 5: 150}, totals
    print('PASS exact square support: 83 four-point and 150 five-point tests with 200-bit integer intervals')


def check_output():
    cell = next((a, q) for a, q in p.old.rep if ''.join(map(str, a)) == '00120221')
    for chart, union in ((8, False), (9, False), (8, True), (9, True)):
        text = p.generate(chart=chart, full=True, f1_union=True) if union else p.generate(*cell, chart=chart, full=True)
        commands = p.parse(text)
        names = set()
        declared = []

        def expression_check(expression):
            if isinstance(expression, str):
                if expression in ('true', 'false') or p.constant(expression) is not None:
                    return
                assert expression in names, expression
                return
            if expression[0] == '/':
                assert p.constant(expression[2]) not in (None, 0), expression
            for arg in expression[1:]:
                expression_check(arg)

        for command in commands:
            if command[0] == 'declare-fun':
                names.add(command[1])
                declared.append(command[1])
            elif command[0] == 'define-fun':
                expression_check(command[-1])
                assert command[1] not in names
                names.add(command[1])
            elif command[0] == 'assert':
                expression_check(command[1])
        assert len(declared) == 15
        assert all(not name.startswith(('s1_', 'u')) for name in declared)
        print(f'PASS full F1 {"union" if union else "maximal cell"} chart {chart}: 15 declarations, no undefined symbols or variable divisions')


if __name__ == '__main__':
    check_polynomializer()
    check_symbolic()
    check_localization()
    check_circuit_pruning()
    check_signed_circuit_signs()
    check_exact_core(s.Integer(1), False)
    check_exact_core(s.Integer(1), True)
    check_exact_core(s.Integer(10**12), False)
    check_square_support()
    check_output()
    print('PASS projective formulation checks; no cell exclusion or new embedded torus asserted')
