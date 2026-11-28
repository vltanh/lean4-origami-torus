#!/usr/bin/env python3
"""Put parallel EB/ED zero-edge C1 configurations on one common line.

Twenty source CNFs require independent RUP replay. Together with the
preceding nonparallel-cap exclusion this closes the common-line
reduction for both single-zero order orbits, not their scalar limits.
"""

import argparse
from itertools import product
import json
from pathlib import Path
import time

import sympy as S

import remaining_c1_single_zero_nonparallel as previous
import remaining_c1_zero_common as double_zero
from solver_chambers import write_cnf
from solver_sat import FastSAT

A, B, L = previous.A, previous.B, previous.L


class ParallelModel(previous.NormalizedModel):
    def __init__(self, order, epsilon, eta):
        super().__init__(order, eta)
        assert epsilon in (-1, 1)
        # Keep the same normalized determinant algebra and generic
        # source. Replace only its freely chosen nonparallel U,V
        # orientation hypothesis by the present exact parallel data.
        assert self.clauses[-2] == [self.crosses[1, 2][0]]
        del self.clauses[-2]
        self.clauses.extend(([-self.crosses[1, 2][0]], [-self.crosses[1, 2][1]],
                             [self.crosses[0, 2][0]]))
        # U=epsilon V; orient P cross V positively in this off-line case.
        for first, second in (((0, 1), (0, 2)), ((1, 3), (2, 3))):
            right = self.crosses[second]
            self.sumzero((self.crosses[first][::-1],
                          right if epsilon == 1 else right[::-1]))


def anchor_checks():
    a, k = S.symbols('alpha k')
    rho = S.Rational(1, 2)-(1-a)*k
    assert S.cancel(2*rho/a-(1-2*(1-a)*k)/a) == 0
    assert S.cancel((1-2*(1-a)*k)/a-(1-2*k)/a-2*k) == 0
    # The remaining ED endpoint has rho=1/2 and negative direction.
    assert -2*S.Rational(1, 2)/a == -1/a
    return {'EB_circle_boundaries': double_zero.scalar_checks(),
            'ED_positive_and_negative_anchor_coefficients': True,
            'original_section_and_circle_sources': previous.source_and_metric_checks()}


def off_line_radius(case, epsilon, eta):
    assert case in ('B', 'Dplus', 'Dminus')
    order = 'B' if case == 'B' else 'D'
    chi = (S.Integer(1) if case == 'B' else
           (1-2*(1-A)*L)/A if case == 'Dplus' else -1/A)
    # Orient V cross R positively and divide all crosses by it.
    # P=chi V and U=epsilon V. Multiplication by alpha below clears
    # only a strictly positive known denominator.
    crosses = {(0, 1): 0, (0, 2): 0, (0, 3): chi,
               (1, 2): 0, (1, 3): epsilon, (2, 3): 1}
    n, base, *_ = previous.shared.base_formula()
    assert base[0] == [1]
    clauses = [list(row) for row in base[1:]]
    units, records = [], []
    for quad, coefficients in previous.normalized_forms(order, eta):
        polynomial = S.factor(A*sum(coefficient*crosses[pair]
                                    for pair, coefficient in coefficients.items()))
        assert S.denom(polynomial).free_symbols == set()
        constant, factors = S.factor_list(polynomial)
        sign = int(S.sign(constant))
        assert S.expand(polynomial-constant*S.prod(factor**power for factor, power in factors)) == 0
        for factor, power in factors:
            known = previous.signs.coefficient_sign(factor)
            assert known is not None
            sign *= known**power
        if sign:
            literal = int(sign)*previous.shared.common.lit(quad)
            clauses.append([literal])
            units.append(literal)
        records.append({'quad': quad, 'polynomial': str(polynomial), 'sign': int(sign)})
    return n, clauses, units, records


def build(directory):
    started = time.monotonic()
    directory.mkdir(parents=True, exist_ok=True)
    checks = anchor_checks()
    obligations = []

    def export(filename, n, clauses, claim, **extra):
        with FastSAT(n, clauses) as solver:
            assert solver.check() == -1, filename
        write_cnf(directory/filename, n, clauses)
        obligations.append({'file': filename, 'claim': claim,
                            'variables': n, 'clauses': len(clauses), **extra})

    for order, epsilon, eta in product(('B', 'D'), (-1, 1), (-1, 1)):
        model = ParallelModel(order, epsilon, eta)
        export(f'c1_single_common_{order}_{epsilon}_{eta}_anchor.cnf', model.n, model.clauses,
               'P3 cannot be off the common cap direction',
               omitted_variable_sign_relations=model.omitted)
    for case, epsilon, eta in product(('B', 'Dplus', 'Dminus'), (-1, 1), (-1, 1)):
        n, clauses, units, records = off_line_radius(case, epsilon, eta)
        export(f'c1_single_common_{case}_{epsilon}_{eta}_radius.cnf', n, clauses,
               'R5 cannot be off the common cap direction',
               strict_normalized_minors=units, exact_normalized_signs=records)
    packet = {'domain': 'ray2 C1; EB or ED; parallel cap directions; interior heights',
              'source_checks': checks, 'unsat_obligations': obligations,
              'conclusion': 'all transverse vertices lie on one common line through zero',
              'relative_rate_assumptions': [], 'scalar_families_excluded': False,
              'height_endpoints_excluded': False, 'seconds': time.monotonic()-started}
    (directory/'c1_single_zero_common.json').write_text(json.dumps(packet, indent=2)+'\n')
    return packet


if __name__ == '__main__':
    if not __debug__:
        raise RuntimeError('run with assertions enabled')
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('output', type=Path)
    result = build(parser.parse_args().output)
    print(json.dumps({'unsat_obligations': len(result['unsat_obligations']),
                      'EB_ED_common_line': True, 'scalar_families_excluded': False,
                      'seconds': result['seconds']}))
