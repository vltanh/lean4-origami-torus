#!/usr/bin/env python3
"""Two complete 15-variable projective charts of the Type 5 signed Gram model.

The output has seven metric equations and no variable denominators.  Each
finite cell is the UNION of charts 8 and 9.  This is a formulation, not an
infeasibility certificate.  The inherited strict-K4 premise is used when
eliminating the three pivot slacks; see f1_algebra_projective.md.
"""
from pathlib import Path
from collections import Counter
import argparse
import re
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent / 'type5_focus' / 'fixed_elongated'))
import cubic as old
import coverage_constraints

BASIS = (2, 5, 7, 4)
OUTSIDE = (0, 3, 6)
MISSING_PIVOT = {0: 7, 3: 4, 6: 7}
F1_CELLS = {'00020220', '00020221', '00020222', '00120220', '00120221'}
op, num, add, mul, sub, neg, det = (
    old.op, old.num, old.add, old.mul, old.sub, old.neg, old.det)


def parse(text):
    tokens = iter(re.findall(r'\(|\)|[^\s()]+', text))

    def one(token):
        if token != '(':
            return token
        result = []
        for token in tokens:
            if token == ')':
                return result
            result.append(one(token))
        raise ValueError('unclosed S-expression')

    return [one(token) for token in tokens]


def sexpr(a):
    return a if isinstance(a, str) else '(' + ' '.join(map(sexpr, a)) + ')'


def plus(*args):
    return add(*(x for x in args if x != '0'))


def times(*args):
    if '0' in args:
        return '0'
    return mul(*(x for x in args if x != '1'))


def constant(expression):
    if isinstance(expression, str):
        try:
            return old.F(expression)
        except ValueError:
            return None
    operation, *arguments = expression
    values = [constant(a) for a in arguments]
    if any(v is None for v in values):
        return None
    if operation == '+':
        return sum(values)
    if operation == '-':
        return -values[0] if len(values) == 1 else values[0] - values[1]
    if operation == '*':
        result = old.F(1)
        for value in values:
            result *= value
        return result
    if operation == '/':
        return values[0] / values[1]
    return None


class Polynomialize:
    """Retain sparse named expressions and strictly positive denominators.

    A rational expression n/d is represented by (n,d), where d>0 is proved
    inductively.  Division by b becomes multiplication by b.num divided by
    b.num^2.  Every variable divisor used by this file is separately required
    nonzero.  Comparisons are then polynomial cross-products with no sign loss.
    """

    def __init__(self):
        self.lines = ['(set-logic QF_NRA)']
        self.env = {}
        # Every key in a factor counter is an independently positive atom:
        # either one whole squared nonzero divisor or an opaque denominator
        # passed through positive_div.  Never factor these atoms into signed
        # subfactors: ordinary monomial LCM would not preserve positivity.
        self.denominators = {'1': Counter()}

    def denominator(self, factors):
        factors = +factors
        value = times(*(atom for atom in sorted(factors) for _ in range(factors[atom])))
        self.denominators.setdefault(value, factors)
        return value

    def positive_atom(self, expression):
        self.denominators.setdefault(expression, Counter({expression: 1}))
        return expression

    def multiply_denominators(self, *values):
        factors = Counter()
        for value in values:
            factors.update(self.denominators[value])
        return self.denominator(factors)

    def common_denominator(self, values):
        factors = Counter()
        for value in values:
            factors |= self.denominators[value]
        return factors

    def arithmetic(self, expression):
        if isinstance(expression, str):
            return self.env.get(expression, (expression, '1'))
        operation, *arguments = expression
        values = [self.arithmetic(a) for a in arguments]
        if operation == '*':
            return times(*(v[0] for v in values)), self.multiply_denominators(*(v[1] for v in values))
        if operation == '-' and len(values) == 1:
            n, d = values[0]
            return ('0' if n == '0' else neg(n)), d
        if operation in ('+', '-'):
            if operation == '-':
                assert len(values) == 2
                values[1] = (neg(values[1][0]), values[1][1])
            common = self.common_denominator([d for _, d in values])
            numerator = plus(*(times(n, self.denominator(common-self.denominators[d]))
                               for n, d in values))
            return numerator, self.denominator(common)
        if operation == 'positive_div':
            # Internal constructor: only the independently proved positive
            # denominator den_0^2 * ac * R_kk is passed here.
            assert len(values) == 2
            (an, ad), (bn, bd) = values
            return times(an, bd), self.multiply_denominators(ad, self.positive_atom(bn))
        if operation == '/':
            assert len(values) == 2
            (an, ad), (bn, bd) = values
            divisor = constant(arguments[1])
            if divisor is not None:
                assert divisor != 0
                return times(an, num(1/divisor)), ad
            square = self.positive_atom(times(bn, bn))
            return times(an, bd, bn), self.multiply_denominators(ad, square)
        raise ValueError(operation)

    def boolean(self, expression):
        if isinstance(expression, str):
            assert expression in ('true', 'false')
            return expression
        operation, *arguments = expression
        if operation in ('and', 'or', 'not', '=>'):
            return op(operation, *(self.boolean(a) for a in arguments))
        assert operation in ('=', 'distinct', '<', '<=', '>', '>=')
        assert len(arguments) == 2
        (an, ad), (bn, bd) = map(self.arithmetic, arguments)
        common = self.common_denominator([ad, bd])
        return op(operation,
                  times(an, self.denominator(common-self.denominators[ad])),
                  times(bn, self.denominator(common-self.denominators[bd])))

    def command(self, command):
        operation = command[0]
        if operation in ('set-logic', 'check-sat'):
            return
        if operation == 'declare-fun':
            self.lines.append(sexpr(command))
            self.env[command[1]] = (command[1], '1')
        elif operation == 'define-fun':
            name = command[1]
            n, d = self.arithmetic(command[-1])
            if d == '1':
                self.lines.append(f'(define-fun {name} () Real {n})')
                self.env[name] = (name, '1')
            else:
                self.lines.append(f'(define-fun {name}_n () Real {n})')
                self.lines.append(f'(define-fun {name}_d () Real {d})')
                self.env[name] = (name + '_n', name + '_d')
                self.denominators[name + '_d'] = self.denominators[d].copy()
        elif operation == 'assert':
            self.lines.append(op('assert', self.boolean(command[1])))
        else:
            raise ValueError(operation)


def f1_localization():
    """Five complete localized domains in common normalized vertical variables.

    The scalar old variable z_i is a physical correction about a cell-dependent
    offset.  Here b_i is the actual normalized lift, so substitute
    z_i = 10^6 * (b_i - offset_i) before taking the disjunction.
    """
    branches = []
    for labels, q in sorted(old.rep):
        if ''.join(map(str, labels)) not in F1_CELLS:
            continue
        replacements = {f'z{i}': parse(times('1000000', sub(f'b{i}', num(old.F(labels[i]-labels[1], 4)+q[i]))))[0]
                        for i in old.V if i != 1}

        def rewrite(expression):
            if isinstance(expression, str):
                return replacements.get(expression, expression)
            return [rewrite(value) for value in expression]

        constraints = []
        for command in parse(old.generate(labels, q, w=10**12, mode='quad', extra=True)):
            if command[0] == 'define-fun' and command[1].startswith('X'):
                break
            if command[0] == 'assert':
                constraints.append(rewrite(command[1]))
        assert constraints
        branches.append(['and', *constraints])
    assert len(branches) == 5
    return ['or', *branches]


def circuit_partitions(vertices, simplex=True, support=True):
    """Canonical positive parts for actual intersections and strict support.

    In support tests the opposite part may contain four neighbors and need
    not be a simplex.  A canonical positive part can therefore have size four.
    """
    result = set()
    if simplex:
        simplices = {(i,) for i in old.V} | set(old.E) | {tuple(sorted(f)) for f in old.faces}
        for length in range(1, min(3, len(vertices)-1) + 1):
            for first in old.combinations(vertices, length):
                second = tuple(i for i in vertices if i not in first)
                if vertices[0] in first and first in simplices and second in simplices:
                    result.add(first)
    if support:
        for vertex in vertices:
            if all(tuple(sorted((vertex, other))) in old.E for other in vertices if other != vertex):
                result.add((vertex,) if vertex == vertices[0] else tuple(i for i in vertices if i != vertex))
    return sorted(result)


def signed_cofactor_test(expression, vertex, positive):
    """Sign of an actual affine coefficient from a raw homogeneous cofactor.

    All homogeneous weights are one except weight_3=D3.  Multiplying each
    raw cofactor by its own row weight recovers the actual affine dependence,
    up to a harmless common factor.  Keep D3 as a Boolean sign condition,
    instead of multiplying it into the polynomial bracket.
    """
    direct = op('>' if positive else '<', expression, '0')
    if vertex != 3:
        return direct
    reverse = op('<' if positive else '>', expression, '0')
    return op('ite', 'pc_den3_positive', direct, reverse)


def generate(labels=None, q=None, w=10**12, chart=8, full=True, audit=None,
             f1_union=False, strengthen=True):
    assert chart in (8, 9)
    assert not f1_union or (labels is None and q is None and w == 10**12)
    other = 17 - chart
    commands = parse(old.generate(labels, q, w=w, mode='quad', extra=True))
    injection, metric = [], []

    def define(name, expression):
        injection.append(f'(define-fun {name} () Real {expression})')
        return name

    def assertion(expression):
        injection.append(op('assert', expression))

    def x(i):
        return '0' if i == 1 else f'x{i}'

    def b(i):
        return f'b{i}'

    def S(i, j):
        return '0' if i == j or 1 in (i, j) else f's1_{min(i,j)}{max(i,j)}'

    def H(i, j):
        if i < 8 and j < 8:
            return S(i, j)
        if i >= 8 and j >= 8:
            return ('(- 1)' if i == 8 else num(-old.F(1, w))) if i == j else '0'
        if i >= 8:
            i, j = j, i
        return x(i) if j == 8 else b(i)

    A, B, C = S(2, 7), S(2, 4), S(5, 4)
    ac = define('pc_ac', times(A, C))
    assertion(op('>', A, '0'))
    assertion(op('>', C, '0'))

    def bilinear(v, u):
        return plus(times(C, plus(times(v[0], u[2]), times(v[2], u[0]))),
                    neg(times(B, plus(times(v[1], u[2]), times(v[2], u[1])))),
                    times(A, plus(times(v[1], u[3]), times(v[3], u[1]))))

    h = {i: [H(j, i) for j in BASIS] for i in (8, 9)}
    residual = {}
    for i, j in ((8, 8), (8, 9), (9, 9)):
        residual[i, j] = residual[j, i] = define(
            f'pc_l{i}{j}', sub(times(ac, H(i, j)), bilinear(h[i], h[j])))
    rkk = residual[chart, chart]
    assertion(op('>', rkk, '0'))
    injection.append('(declare-fun pc_t () Real)')
    assertion(op('<=', '(- 1)', 'pc_t'))
    assertion(op('<=', 'pc_t', '1'))
    metric.extend([op('=', residual[chart, other], times('pc_t', rkk)),
                   op('=', residual[other, other], times('pc_t', 'pc_t', rkk))])

    denominators, numerators, pivot, lhat = {}, {}, {}, {}
    substitutions = {}
    coefficient_cache = {}
    for i in OUTSIDE:
        missing = MISSING_PIVOT[i]
        v = ['0' if j == missing else H(j, i) for j in BASIS]
        unit = ['1' if j == missing else '0' for j in BASIS]
        constant, coefficient = {}, {}
        for j in (8, 9):
            constant[j] = define(f'pc_c{i}_{j}', sub(times(ac, H(i, j)), bilinear(v, h[j])))
            coefficient[j] = (coefficient_cache[missing][0][j] if missing in coefficient_cache else
                              define(f'pc_a{i}_{j}', neg(bilinear(unit, h[j]))))
        di = denominators[i] = (coefficient_cache[missing][1] if missing in coefficient_cache else
                                define(f'pc_den{i}', sub(coefficient[other], times('pc_t', coefficient[chart]))))
        coefficient_cache[missing] = coefficient, di
        ni = numerators[i] = define(
            f'pc_num{i}', sub(times('pc_t', constant[chart]), constant[other]))
        assertion(op('distinct', di, '0'))
        pivot[i] = [define(f'pc_p{i}_{j}', plus(times(di, value), ni if j == missing else '0'))
                    for j, value in zip(BASIS, v)]
        # D_i*c_ik+n_i*alpha_ik cancels its t terms identically.  Keep this
        # degree-five expression, independent of the projective parameter.
        lhat[i] = define(f'pc_v{i}', sub(times(coefficient[other], constant[chart]),
                                        times(coefficient[chart], constant[other])))
        substitutions[S(i, missing)] = op('/', ni, di)
        metric.append(op('=', times(rkk, neg(bilinear(pivot[i], pivot[i]))),
                         times(lhat[i], lhat[i])))
    for i, j in ((0, 3), (3, 6)):
        lij = sub(times(denominators[i], denominators[j], ac, H(i, j)),
                  bilinear(pivot[i], pivot[j]))
        metric.append(op('=', times(rkk, lij), times(lhat[i], lhat[j])))
    n06 = define('pc_num06', plus(times(rkk, bilinear(pivot[0], pivot[6])),
                                  times(lhat[0], lhat[6])))
    d06 = define('pc_den06', times(denominators[0], denominators[6], ac, rkk))
    assert denominators[0] == denominators[6]
    substitutions[S(0, 6)] = op('positive_div', n06, d06)
    assert len(metric) == 7 and len(substitutions) == 4
    for expression in metric:
        injection.append(op('assert', expression))

    polynomial = Polynomialize()
    inserted = False
    for command in commands:
        if command[0] == 'declare-fun' and command[1] in substitutions:
            if not inserted:
                for c in parse('\n'.join(injection)):
                    polynomial.command(c)
                inserted = True
            polynomial.command(parse(f'(define-fun {command[1]} () Real {substitutions[command[1]]})')[0])
        else:
            polynomial.command(command)
    assert inserted

    if f1_union:
        polynomial.command(['assert', f1_localization()])
    if strengthen:
        distances = {(i, j): f'd{i}{j}' for i, j in old.combinations(old.V, 2)}

        def squared_lift(i, j, shift):
            dx = plus(sub(x(j), x(i)), num(old.F(shift[0])+old.F(shift[1], 2)))
            dy = plus(sub(b(j), b(i)), num(shift[1]))
            return plus(times(dx, dx), times(num(w), dy, dy))

        extra = coverage_constraints.noncollinearity_constraints(distances)
        extra += coverage_constraints.unique_lift_constraints(distances, squared_lift)
        for v, cycle in old.links.items():
            def slack(i, j):
                return f's{v}_{min(i,j)}{max(i,j)}'
            aa = [slack(cycle[i], cycle[(i+2)%7]) for i in range(7)]
            bb = [slack(cycle[i], cycle[(i+3)%7]) for i in range(7)]
            for i in range(7):
                lhs = times(bb[i], bb[(i+2)%7], bb[(i+5)%7])
                rhs = plus(times(aa[i], aa[(i+3)%7], bb[(i+5)%7]),
                           times(aa[(i+1)%7], aa[(i+5)%7], bb[(i+2)%7]))
                extra.append(op('assert', op('>=', lhs, rhs)))
        assert len(extra) == 21 + 144 + 21
        # Exact cap Gram identities from f1_geometry.md.  Their horizontal
        # margins are strictly positive, but the SOS remainder may vanish.
        caps = [((1, 0, 4), [x(0), neg(x(4)), plus('1', sub(x(4), x(0)))]),
                ((5, 6, 3), [plus(sub(x(6), x(5)), num(old.F(1, 2))),
                             plus(sub(x(5), x(3)), num(old.F(1, 2))), sub(x(3), x(6))])]
        for (v, i, j), lengths in caps:
            margins = [sub('1', times('2', length)) for length in lengths]
            extra.extend(op('assert', op('>', margin, '0')) for margin in margins)
            dij = distances[min(i, j), max(i, j)]
            dvi = distances[min(v, i), max(v, i)]
            dvj = distances[min(v, j), max(v, j)]
            twice_dot = sub(plus(dvi, dvj), dij)
            determinant4 = sub(times('4', dvi, dvj), times(twice_dot, twice_dot))
            extra.append(op('assert', op('>=', determinant4, times(*margins))))
        for command in parse('\n'.join(extra)):
            polynomial.command(command)

    # Independent five-coordinate reconstruction, emitted only for the verifier.
    coordinates = {}
    for i in (old.V if audit is not None else ()):
        if i == 1:
            coordinates[i] = ['0'] * 5 + ['1']
            continue
        di = denominators.get(i, '1')
        pi = pivot[i] if i in pivot else [H(j, i) for j in BASIS]
        fifth = lhat.get(i, '0')
        components = [plus(pij, times(di, plus(times(x(i), h[8][k]),
                                             times(num(w), b(i), h[9][k]))))
                      for k, pij in enumerate(pi)]
        components.append(plus(fifth, times(di, plus(times(x(i), residual[8, chart]),
                                                    times(num(w), b(i), residual[9, chart])))))
        coordinates[i] = []
        for axis, expression in enumerate([times(di, c) for c in components] + [times(di, di)]):
            name = f'pc_h{i}_{axis}'
            polynomial.command(parse(f'(define-fun {name} () Real {expression})')[0])
            assert polynomial.env[name][1] == '1'
            coordinates[i].append(name)

    signed_coordinates = coordinates
    # A much smaller affine-incidence representation uses the three fixed
    # independent rays 2,5,4.  Inner products with them are an invertible
    # linear map on spatial R^3.  Only G_43 involves a missing distance.
    coordinates = {}
    for i in old.V:
        if i == 1:
            coordinates[i] = ['0', '0', '0', '1']
            continue
        di = denominators[3] if i == 3 else '1'
        entries = []
        for anchor in (2, 5, 4):
            known = plus(times(x(anchor), x(i)), times(num(w), b(anchor), b(i)))
            entry = (plus(numerators[3], times(di, known))
                     if (anchor, i) == (4, 3) else times(di, plus(H(anchor, i), known)))
            entries.append(entry)
        entries.append(di)
        coordinates[i] = []
        for axis, expression in enumerate(entries):
            name = f'pc_g{i}_{axis}'
            polynomial.command(parse(f'(define-fun {name} () Real {expression})')[0])
            assert polynomial.env[name][1] == '1'
            coordinates[i].append(name)
    polynomial.lines.append(f'(define-fun pc_den3_positive () Bool (> {denominators[3]} 0))')

    if audit is not None:
        audit.update(injection=parse('\n'.join(injection)),
                     substitutions={key: parse(value)[0] for key, value in substitutions.items()},
                     coordinates=signed_coordinates,
                     incidence_coordinates=coordinates,
                     coordinate_definitions=[command for command in parse('\n'.join(polynomial.lines))
                                             if command[0] == 'define-fun'
                                             and command[1].startswith(('pc_h', 'pc_g'))],
                     metric=[parse(value)[0] for value in metric],
                     residual=residual, denominators=denominators)

    minors = {}

    def affine(vertices, axes):
        key = vertices, axes
        if key not in minors:
            expression = det([[coordinates[i][axis] for axis in axes] + [coordinates[i][3]]
                              for i in vertices])
            name = 'pc_d' + ''.join(map(str, vertices)) + 'c' + ''.join(map(str, axes))
            polynomial.command(parse(f'(define-fun {name} () Real {expression})')[0])
            minors[key] = name
        return minors[key]

    def any_(args):
        return 'false' if not args else op('or', *args)

    def all_(args):
        return 'true' if not args else op('and', *args)

    # A clique uses only known edge lengths.  Its Gram determinant has degree
    # six in intrinsic coordinates, avoiding a disjunction of ten much
    # higher-degree projective-coordinate minors.
    cliques = set()
    for vertices in old.combinations(old.V, 4):
        if all(e in old.E for e in old.combinations(vertices, 2)):
            cliques.add(vertices)
            origin, *others = vertices

            def distance(i, j):
                return '0' if i == j else f'd{min(i,j)}{max(i,j)}'

            twice_gram = [[sub(plus(distance(origin, i), distance(origin, j)), distance(i, j))
                           for j in others] for i in others]
            polynomial.command(parse(op('assert', op('>', det(twice_gram), '0')))[0])
    if full or strengthen:
        # With the 55-triple theorem, lower supports need no separate circuit
        # test: all pairs are distinct and the only potentially collinear
        # triple, 067, contains no edge and has no disjoint-simplex partition.
        for size in range(4 if strengthen else 2, 6):
            for vertices in old.combinations(old.V, size):
                if vertices in cliques:
                    continue
                parts = circuit_partitions(vertices, simplex=full, support=strengthen)
                if not parts:
                    continue
                rank = all_([op('=', affine(vertices, axes), '0')
                             for axes in old.combinations(range(3), size-1)]) if size <= 4 else 'true'
                for first in parts:
                    tests = []
                    for axes in old.combinations(range(3), size-2):
                        cofactors = [affine(vertices[:i] + vertices[i+1:], axes) for i in range(size)]
                        desired = [((i % 2 == 0) == (v in first)) for i, v in enumerate(vertices)]
                        tests.append(any_([
                            all_([signed_cofactor_test(value, vertex, positive)
                                  for value, vertex, positive in zip(cofactors, vertices, desired)]),
                            all_([signed_cofactor_test(value, vertex, not positive)
                                  for value, vertex, positive in zip(cofactors, vertices, desired)])]))
                    polynomial.lines.append(op('assert', op('not', all_([rank, any_(tests)]))))
    polynomial.lines.append('(check-sat)')
    result = '\n'.join(polynomial.lines) + '\n'
    assert result.count('(declare-fun ') == 15
    # Rational constants are printed as divisions; all divisors in the output
    # are constant.  This postcondition is checked structurally in the verifier.
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('output', type=Path)
    parser.add_argument('--cell', default='00120221', help='one exact cell, F1, all, or hex')
    parser.add_argument('--relax', action='store_true', help='omit simplex exclusions; keep K4 requirements')
    parser.add_argument('--solver', choices=('default', 'nlsat', 'nlsat-no-factor'), default='default')
    parser.add_argument('--statistics', action='store_true', help='append the solver all-statistics query')
    args = parser.parse_args()
    args.output.mkdir(parents=True, exist_ok=True)
    cells = sorted(old.rep)
    if args.cell not in ('all', 'hex', 'F1'):
        cells = [(a, q) for a, q in cells if ''.join(map(str, a)) == args.cell]
        if not cells:
            parser.error('unknown cell')
    if args.cell in ('hex', 'F1'):
        cells = [(None, None)]
    for a, q in cells:
        label = args.cell if a is None else ''.join(map(str, a))
        for chart in (8, 9):
            result = generate(a, q, w=old.F(3,4) if args.cell == 'hex' else 10**12,
                              chart=chart, full=not args.relax, f1_union=args.cell == 'F1')
            check = {'default': '(check-sat)',
                     'nlsat': '(check-sat-using qfnra-nlsat)',
                     'nlsat-no-factor': '(check-sat-using (using-params qfnra-nlsat :factor false))'}[args.solver]
            result = result.replace('(check-sat)', check)
            if args.statistics:
                result += '(get-info :all-statistics)\n'
            path = args.output / f'{label}-chart{chart}.smt2'
            path.write_text(result)
            print(path.name, '15 variables, 7 metric equations,', result.count('(assert '), 'assertions')


if __name__ == '__main__':
    main()
