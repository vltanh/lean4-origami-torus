#!/usr/bin/env python3
"""Eliminate the Gram seed without splitting any of the 268 K4 branches.

The selected K4 mirror fixes one root of a positive-leading quadratic.
All real expressions are interpreted in that quadratic algebra. Every
comparison, including weak inequalities and zero tests in actual circuits,
is replaced by an exact Boolean polynomial sign condition. The resulting
query has 14 intrinsic variables at fixed height, or 15 with t>0 retained.

This is an exact necessary-system projection, not a feasibility verdict.
See branch_metric_root.md for the universal sign lemma and root selection.
"""

import argparse
from fractions import Fraction as F
import hashlib
from itertools import product
import json
from pathlib import Path

import branch_gram_chart as gram
from verify_projected_metric import parse


def emit(term):
    if isinstance(term, str):
        return term
    return '(' + ' '.join(map(emit, term)) + ')'


def atoms(term):
    if isinstance(term, str):
        yield term
    else:
        for item in term:
            yield from atoms(item)


def root_sign(manifest, branch, plan):
    """F'(z)=-g*lambda_0; the two determinants are strict actual K4s."""
    signs = dict(zip(manifest['cliques'], branch['pattern']))
    anchor = tuple(plan['anchors'])
    replacement = (plan['leaves'][0],) + anchor[1:]

    def ordered_sign(quad):
        key = ''.join(map(str, sorted(quad)))
        assert key in signs
        return (1 if signs[key] == '+' else -1) * gram.parity(quad)

    anchor_sign = ordered_sign(anchor)
    replacement_sign = ordered_sign(replacement)
    assert anchor_sign == plan['orientation']
    sigma = -replacement_sign * anchor_sign
    assert sigma in (-1, 1)
    return sigma, {
        'ordered_anchor': anchor,
        'ordered_seed_replacement': replacement,
        'anchor_sign': anchor_sign,
        'replacement_sign': replacement_sign,
        'root_derivative_sign': sigma,
    }


def verify_universal_identities():
    """Exact algebra plus the complete universal sign table; no solver."""
    import sympy as s

    a, b, c, linear, constant, z = s.symbols('A B C a b z')
    discriminant = b*b - 4*a*c
    k = 2*a*constant - linear*b
    resultant = a*constant**2 - b*linear*constant + c*linear**2
    assert s.expand(k*k - linear**2*discriminant - 4*a*resultant) == 0
    assert s.expand((2*a*z+b)**2 - discriminant
                    - 4*a*(a*z*z+b*z+c)) == 0

    # The root sign table uses K and S=T*sqrt(Delta), whose sign is T's.
    # For opposite nonzero signs, K-S has K's sign, so the factorization
    # R=(K+S)(K-S) determines sign(K+S). Axes and equal signs are direct.
    K, S = s.symbols('K S')
    assert s.expand((K+S)*(K-S) - (K*K-S*S)) == 0
    count = 0
    for sign_k, sign_t, sign_r in product((-1, 0, 1), repeat=3):
        if sign_t == 0:
            if sign_r != (1 if sign_k else 0):
                continue
            sign_sum = sign_k
        elif sign_k == 0:
            if sign_r != -1:
                continue
            sign_sum = sign_t
        elif sign_k == sign_t:
            sign_sum = sign_k
        else:
            sign_sum = sign_k * sign_r
        strict = (sign_k > 0 and (sign_t >= 0 or sign_r > 0)) or (
            sign_t > 0 and sign_r < 0)
        weak = (sign_k >= 0 and (sign_t >= 0 or sign_r >= 0)) or (
            sign_t > 0 and sign_r <= 0)
        opposite = (sign_k >= 0 and sign_t <= 0) or (sign_k <= 0 and sign_t >= 0)
        assert opposite == (sign_k * sign_t <= 0)
        zero = sign_r == 0 and opposite
        assert strict == (sign_sum > 0)
        assert weak == (sign_sum >= 0)
        assert zero == (sign_sum == 0)
        count += 1
    assert count == 17

    # The symmetric adjugate is left symbolic. This proves the derivative
    # identity independently of any particular distance or branch assignment.
    h00, h01, h02, h11, h12, h22, g = s.symbols('h00 h01 h02 h11 h12 h22 g')
    H = s.Matrix([[h00, h01, h02], [h01, h11, h12], [h02, h12, h22]])
    u0 = s.Matrix(s.symbols('u0:3'))
    ones = s.ones(3, 1)
    U = u0 + z*ones/2
    quadratic = (U.T*H*U)[0] - g*z
    derivative = (ones.T*H*U)[0] - g
    assert s.expand(s.diff(quadratic, z) - derivative) == 0
    assert s.expand(derivative + g*(1-(ones.T*H*U)[0]/g)) == 0
    assert s.expand(quadratic - ((ones.T*H*ones)[0]*z*z/4
                    + ((ones.T*H*u0)[0]-g)*z + (u0.T*H*u0)[0])) == 0

    # Affine replacement multiplies a homogeneous determinant by lambda_0.
    vertices = [s.Matrix([1, *s.symbols(f'p{i}_0:3')]) for i in range(4)]
    lambdas = s.symbols('lambda0:4')
    leaf = sum((weight*point for weight, point in zip(lambdas, vertices)), s.zeros(4, 1))
    assert s.expand(s.det(s.Matrix.hstack(leaf, *vertices[1:]))
                    - lambdas[0]*s.det(s.Matrix.hstack(*vertices))) == 0
    return {'universal_sign_regimes': count, 'resultant_identity': True,
            'derivative_and_barycentric_identity': True,
            'affine_replacement_determinant_identity': True}


class RootProjection:
    """Interpret a complete Gram query, preserving all Boolean structure."""

    def __init__(self, quadratic_names, sigma):
        assert sigma in (-1, 1)
        self.quadratic_names = tuple(quadratic_names)
        self.sigma = sigma
        self.dag = gram.DAG()
        self.environment = {}
        self.algebra = None
        self.root_definitions = []
        self.root_cache = {}
        self.comparisons = 0
        self.input_real_definitions = 0
        self.boolean_definitions = 0
        self.input_assertions = 0

    def ring(self):
        if self.algebra is None:
            coefficients = [self.environment[name] for name in self.quadratic_names]
            assert all(value.linear == 0 and value.exponent == 0 for value in coefficients)
            self.algebra = gram.QuadraticAlgebra(
                self.dag, *(value.constant for value in coefficients)
            )
        return self.algebra

    def add(self, values):
        if all(value.exponent == 0 for value in values):
            return gram.Element(self.dag.add(*(value.constant for value in values)),
                                self.dag.add(*(value.linear for value in values)))
        return self.ring().add(*values)

    def multiply(self, first, second):
        if first.linear == 0 or second.linear == 0:
            return gram.Element(
                self.dag.mul(first.constant, second.constant),
                self.dag.add(self.dag.mul(first.constant, second.linear),
                             self.dag.mul(first.linear, second.constant)),
                first.exponent + second.exponent,
            )
        return self.ring().mul(first, second)

    def negative(self, value):
        return gram.Element(self.dag.neg(value.constant), self.dag.neg(value.linear), value.exponent)

    def scalar(self, term):
        if isinstance(term, str):
            if term in self.environment:
                return self.environment[term]
            return gram.Element(F(term))
        operator, *arguments = term
        values = [self.scalar(argument) for argument in arguments]
        if operator == '+':
            return self.add(values)
        if operator == '-':
            if len(values) == 1:
                return self.negative(values[0])
            assert len(values) == 2
            return self.add([values[0], self.negative(values[1])])
        if operator == '*':
            result = gram.Element(F(1))
            for value in values:
                result = self.multiply(result, value)
            return result
        if operator == '/':
            assert len(values) == 2
            denominator = values[1]
            assert denominator.linear == 0 and denominator.exponent == 0
            assert isinstance(denominator.constant, F) and denominator.constant != 0
            return self.multiply(values[0], gram.Element(1 / denominator.constant))
        raise ValueError(f'unsupported scalar operation: {operator}')

    def comparison(self, operator, value):
        assert operator in ('>', '>=', '<', '<=', '=', 'distinct')
        self.comparisons += 1
        # All stored denominators are powers of A>0; their exponents may
        # differ between aliases but do not affect any sign or zero test.
        if value.linear == 0:
            return [operator, self.dag.text(value.constant), '0']
        key = (operator, value.constant, value.linear)
        if key in self.root_cache:
            return self.root_cache[key]
        if operator in ('<', '<='):
            expression = self.comparison('>' if operator == '<' else '>=', self.negative(value))
            self.root_cache[key] = expression
            return expression
        if operator == 'distinct':
            expression = ['not', self.comparison('=', value)]
            self.root_cache[key] = expression
            return expression

        d, ring = self.dag, self.ring()
        a, b, c = ring.a, ring.b, ring.c
        linear, constant = value.linear, value.constant
        K = d.sub(d.mul(F(2), a, constant), d.mul(linear, b))
        T = d.mul(F(self.sigma), linear)
        resultant = d.add(d.mul(a, constant, constant),
                         d.neg(d.mul(b, linear, constant)),
                         d.mul(c, linear, linear))
        # 4*A is strictly positive, so the resultant has exactly R's sign.
        # Emit the lower-degree polynomial and avoid the product K*T too.
        k, t, r = map(d.text, (K, T, resultant))
        if operator == '=':
            expression = ['and', ['=', r, '0'],
                          ['or', ['and', ['>=', k, '0'], ['<=', t, '0']],
                           ['and', ['<=', k, '0'], ['>=', t, '0']]]]
        elif operator == '>':
            expression = ['or', ['and', ['>', k, '0'],
                                  ['or', ['>=', t, '0'], ['>', r, '0']]],
                          ['and', ['>', t, '0'], ['<', r, '0']]]
        else:
            assert operator == '>='
            expression = ['or', ['and', ['>=', k, '0'],
                                  ['or', ['>=', t, '0'], ['>=', r, '0']]],
                          ['and', ['>', t, '0'], ['<=', r, '0']]]
        name = f'root_sign_{len(self.root_definitions)}'
        self.root_definitions.append(['define-fun', name, [], 'Bool', expression])
        self.root_cache[key] = name
        return name

    def boolean(self, term):
        if isinstance(term, str):
            return term
        operator, *arguments = term
        if operator in ('>', '>=', '<', '<=', '=', 'distinct'):
            assert len(arguments) == 2
            difference = self.add([self.scalar(arguments[0]), self.negative(self.scalar(arguments[1]))])
            return self.comparison(operator, difference)
        assert operator in ('and', 'or', 'not', 'ite')
        return [operator, *(self.boolean(argument) for argument in arguments)]

    def rewrite(self, text):
        boolean_definitions, assertions = [], []
        check_sat = 0
        for form in parse(text):
            kind = form[0]
            if kind == 'set-logic':
                assert form == ['set-logic', 'QF_NRA']
            elif kind == 'declare-fun':
                _, name, arguments, sort = form
                assert arguments == [] and sort == 'Real'
                if name == 'zseed':
                    self.environment[name] = gram.Element(F(0), F(1))
                else:
                    self.environment[name] = gram.Element(self.dag.variable(name))
            elif kind == 'define-fun':
                _, name, arguments, sort, expression = form
                assert arguments == []
                if sort == 'Real':
                    self.environment[name] = self.scalar(expression)
                    self.input_real_definitions += 1
                else:
                    assert sort == 'Bool'
                    boolean_definitions.append(['define-fun', name, [], 'Bool', self.boolean(expression)])
                    self.boolean_definitions += 1
            elif kind == 'assert':
                assertions.append(['assert', self.boolean(form[1])])
                self.input_assertions += 1
            elif kind == 'check-sat':
                assert form == ['check-sat']
                check_sat += 1
            else:
                raise ValueError(f'unsupported source form: {kind}')
        assert check_sat == 1 and 'zseed' in self.environment
        ring, d = self.ring(), self.dag
        discriminant = d.sub(d.mul(ring.b, ring.b), d.mul(F(4), ring.a, ring.c))
        root_conditions = [
            ['assert', ['>', d.text(ring.a), '0']],
            ['assert', ['>', d.text(discriminant), '0']],
        ]
        roots = set(atoms(self.root_definitions + boolean_definitions + root_conditions + assertions))
        reachable = d.reachable(roots)
        declarations = [['declare-fun', name, [], 'Real'] for name in d.variables]
        result = '\n'.join([
            '(set-logic QF_NRA)', *map(emit, declarations), *d.lines(roots=roots),
            *map(emit, self.root_definitions), *map(emit, boolean_definitions),
            *map(emit, root_conditions), *map(emit, assertions), '(check-sat)',
        ]) + '\n'
        assert 'zseed' not in result
        assert len(assertions) == self.input_assertions
        return result, {
            'real_variables': len(d.variables),
            'dag_nodes': len(reachable),
            'constructed_dag_nodes': len(d.nodes),
            'source_real_definitions': self.input_real_definitions,
            'source_boolean_definitions_retained': len(boolean_definitions),
            'source_assertions_retained': len(assertions),
            'root_sign_predicates': len(self.root_definitions),
            'root_parameter_eliminated': True,
            'weak_zero_conditions_retained': True,
            'positive_resultant_factor_removed': True,
        }


def generate(manifest, branch, mark, y, *, all_heights=False):
    parts = gram.generate_parts(manifest, branch, mark, y, all_heights=all_heights)
    source_text = gram.common.generate_query(parts, manifest['cliques'], branch)
    sigma, root_record = root_sign(manifest, branch, parts[2]['plan'])
    projection = RootProjection(parts[2]['seed_quadratic'], sigma)
    text, metadata = projection.rewrite(source_text)
    assert metadata['real_variables'] == (15 if all_heights else 14)
    return text, {
        **metadata, 'mark': mark, 'minimum_y': y, 'all_heights': all_heights,
        'selected_root': root_record,
        'gram_source_sha256': hashlib.sha256(source_text.encode()).hexdigest(),
        'scope': 'intrinsic-only necessary rewrite; no branch excluded',
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('manifest', type=Path, nargs='?', help='existing axis_chambers.json')
    parser.add_argument('output', type=Path, nargs='?')
    parser.add_argument('--mark', type=int, choices=(1, 2))
    parser.add_argument('--y', type=int, default=32)
    parser.add_argument('--all-heights', action='store_true')
    parser.add_argument('--branch', type=int, action='append', help='unchanged zero-based K4 branch ID')
    args = parser.parse_args()
    identities = verify_universal_identities()
    if args.manifest is None:
        assert args.output is None
        print(json.dumps(identities, sort_keys=True))
        return
    if args.output is None or args.mark is None:
        parser.error('query generation requires OUTPUT and --mark')
    if args.y < 32:
        parser.error('the whole-branch height tail requires --y >= 32')
    data = args.manifest.read_bytes()
    manifest = json.loads(data)
    assert len(manifest['branches']) == 268
    args.output.mkdir(parents=True, exist_ok=True)
    selected = args.branch if args.branch is not None else range(268)
    records = []
    for index in selected:
        assert 0 <= index < 268
        branch = manifest['branches'][index]
        text, metadata = generate(manifest, branch, args.mark, args.y, all_heights=args.all_heights)
        filename = f'ray{args.mark}_axis_k4_{index:03d}.smt2'
        (args.output / filename).write_text(text)
        record = {'branch_id': index, 'pattern': branch['pattern'], 'file': filename,
                  'bytes': len(text), 'sha256': hashlib.sha256(text.encode()).hexdigest(), **metadata}
        records.append(record)
        print(json.dumps(record, sort_keys=True), flush=True)
    result = {'source_manifest_sha256': hashlib.sha256(data).hexdigest(),
              'original_branch_count': 268, 'universal_identities': identities,
              'queries': records, 'excluded_branches': [],
              'status': 'No feasibility decision or full-branch exclusion is claimed.'}
    (args.output / 'branch_metric_root_manifest.json').write_text(json.dumps(result, indent=2) + '\n')


if __name__ == '__main__':
    if not __debug__:
        raise RuntimeError('run with assertions enabled')
    main()
