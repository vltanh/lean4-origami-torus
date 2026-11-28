#!/usr/bin/env python3
"""Exact finite reduction and metric witnesses for collinear ray-1 C1 limits.

The five exported CNFs require independent RUP replay.  The companion
note proves that the two-collinear-cap boundary reduces to six explicit
families on one transverse line.  Every family satisfies the full
29-row limit system and all six active nonedge inequalities; these are
limit witnesses, not embeddings or exclusions.
"""

import argparse
from functools import lru_cache
from itertools import combinations
import json
from pathlib import Path

import sympy as s

import solver_remaining_c1_collinear as trits
import solver_remaining_c1_collinear_rank as rank
import solver_remaining_c1_geometry as geometry
import solver_remaining_limit as reducer
from solver_chambers import write_cnf
from solver_sat import FastSAT

ALPHA, BETA, R = s.symbols('alpha beta r')
HALF = s.Rational(1, 2)
UPPER = {'A': (4, (2, 3)), 'B': (2, (3, 4)), 'C': (4, (2,))}
LOWER = {'A': (0, (6, 7)), 'B': (6, (0, 7)), 'C': (6, (0,))}


@lru_cache(maxsize=1)
def height_relations():
    """All determinant expansions using only vertices other than 5.

    alpha*[ijkl] is a signed sum of [01ab], with coefficients among
    1, alpha, 1-alpha and their negatives.  Positive coefficient
    magnitudes may be forgotten when imposing the necessary trit sum.
    """
    twice_heights = (0, ALPHA, 1, 1, 1, BETA, 0, 0)

    def anchor(i, j):
        if i in (0, 1) or j in (0, 1):
            return {}
        return {tuple(sorted((0, 1, i, j))): 1 if i < j else -1}

    def area(a, b, c):
        result = {}
        for sign, i, j in ((1, b, c), (-1, a, c), (1, a, b)):
            for quad, value in anchor(i, j).items():
                result[quad] = result.get(quad, 0)+sign*value
        return result

    result = []
    for quad in trits.QUADS:
        if 5 in quad:
            continue
        row = {quad: ALPHA}
        for index, vertex in enumerate(quad):
            for minor, coefficient in area(*(quad[:index]+quad[index+1:])).items():
                row[minor] = row.get(minor, 0)-(-1)**(index+3)*twice_heights[vertex]*coefficient
        row = {minor: s.expand(coefficient) for minor, coefficient in row.items()
               if s.expand(coefficient) != 0}
        if row:
            result.append(row)
    assert len(result) == 25
    return result


def coefficient_sign(coefficient):
    for sign in (1, -1):
        if any(s.expand(coefficient-sign*positive) == 0 for positive in (1, ALPHA, 1-ALPHA)):
            return sign
    raise AssertionError(coefficient)


class ActualModel(trits.ActualBracketModel):
    """The same generic/actual source, with two collinear endpoint caps."""
    def __init__(self, upper=None, lower=None):
        self.n, base, *_ = trits.shared.base_formula()
        self.clauses = [list(row) for row in base]
        self.trits = {}
        for high in ({2, 3, 4}, {1, 2, 3, 4, 5}):
            for support in combinations(range(8), 5):
                if set(support) <= high or not set(support) & high:
                    continue
                row = [(1 if vertex in high else -1)*(-1)**i
                       *trits.shared.common.lit(support[:i]+support[i+1:])
                       for i, vertex in enumerate(support)]
                self.clauses.extend((row, [-literal for literal in row]))
        for index, quad in enumerate(trits.QUADS):
            positive, negative = self.new_trit()
            self.trits[quad] = positive, negative
            self.clauses.extend(([-positive, index+1], [-negative, -index-1]))
        for support in combinations(range(8), 5):
            self.sumzero([self.bits(support[:i]+support[i+1:], (-1)**i)
                          for i in range(5)])
        for triangle in ((2, 3, 4), (0, 6, 7)):
            for vertex in range(8):
                if vertex not in triangle:
                    self.clauses.extend([[-bit] for bit in self.bits(triangle+(vertex,))])
        for choice, shapes in ((upper, UPPER), (lower, LOWER)):
            if choice is not None:
                middle, parents = shapes[choice]
                for quad in trits.QUADS:
                    if middle in quad:
                        self.sumzero([self.bits(tuple(parent if vertex == middle else vertex
                                                       for vertex in quad)) for parent in parents]
                                     +[self.bits(quad, -1)])
        self.add_weak_gp()
        for relation in rank.HEIGHT_SIGNS:
            self.sumzero([self.bits(quad, sign) for quad, sign in relation])
        for relation in height_relations():
            self.sumzero([self.bits(quad, coefficient_sign(coefficient))
                          for quad, coefficient in relation.items()])


def verify_height_relations():
    points = [s.zeros(2, 1), s.zeros(2, 1)]
    points.extend(s.Matrix(s.symbols(f'x{i} y{i}')) for i in range(2, 8))
    heights = (0, ALPHA/2, HALF, HALF, HALF, BETA/2, 0, 0)
    xyz = [point.col_join(s.Matrix([height])) for point, height in zip(points, heights)]

    def determinant(quad):
        first, *rest = quad
        return s.Matrix.hstack(*(xyz[i]-xyz[first] for i in rest)).det()

    for relation in height_relations():
        assert s.expand(sum(coefficient*determinant(quad)
                            for quad, coefficient in relation.items())) == 0
        for coefficient in relation.values():
            coefficient_sign(coefficient)
    return len(height_relations())


def verify_symmetry_cover():
    def signature(shape):
        middle, parents = shape
        return ('equal', tuple(sorted((middle, parents[0])))) if len(parents) == 1 \
            else ('between', middle, tuple(sorted(parents)))

    permutations = (tuple(range(8)), tuple((6-i) % 8 for i in range(8)),
                    tuple((i+4) % 8 for i in range(8)), tuple((2-i) % 8 for i in range(8)))
    records = []
    for upper in UPPER:
        for lower in LOWER:
            if upper == lower == 'C':
                continue
            for permutation in permutations:
                inverse = {value: i for i, value in enumerate(permutation)}

                def mapped(shape):
                    middle, parents = shape
                    return inverse[middle], tuple(inverse[parent] for parent in parents)

                images = [(set(inverse[i] for i in (2, 3, 4)), mapped(UPPER[upper])),
                          (set(inverse[i] for i in (0, 6, 7)), mapped(LOWER[lower]))]
                new_upper = next(shape for cap, shape in images if cap == {2, 3, 4})
                new_lower = next(shape for cap, shape in images if cap == {0, 6, 7})
                if signature(new_upper) != signature(UPPER['B']):
                    continue
                target = next(key for key, shape in LOWER.items()
                              if signature(shape) == signature(new_lower))
                records.append({'upper': upper, 'lower': lower,
                                'permutation': permutation, 'target': ['B', target]})
                break
            else:
                raise AssertionError((upper, lower))
    anchors = {tuple(sorted(permutation[i] for i in (0, 1, 2, 3)))
               for permutation in permutations}
    assert anchors == {(0, 1, 2, 3), (0, 1, 2, 7), (3, 4, 5, 6), (4, 5, 6, 7)}
    return records


def verify_scalar_identities():
    p, q, r, kdef, a = s.symbols('p q r kdef a')
    h, k = HALF-r, HALF-kdef
    rho = a*(q+r)+(1-a)*(HALF-p)
    sigma = HALF+(1-a)*p-a*q
    gap = h*k-q*k-p*h
    expansion = (HALF*(HALF-p-q-r-kdef)+r*kdef+p*r+q*kdef)
    assert s.expand(gap-expansion) == 0
    factor = 2*a*r*(HALF-r-q)+(1-a)*(HALF-p-q-r+2*p*r)
    assert s.expand(2*h*rho-q-factor) == 0
    n2 = sigma**2-2*(1-a)*p
    norm_gap = (a*p+(1-a)*q)*(1-2*(p+q))+(a*p-(1-a)*q)**2
    assert s.expand(n2-(HALF-p-q)**2-norm_gap) == 0
    opposition = p/k-(2*sigma-1+q/h)
    assert s.factor(opposition.subs(q, 0)-p*(1/k-2*(1-a))) == 0
    # On the two possible positive-q zero-area faces.
    assert s.factor(opposition.subs({p: 0, r: HALF-q, kdef: 0}, simultaneous=True)
                    +(1-2*a*q)) == 0
    assert s.factor(opposition.subs({r: 0, p: HALF-q, kdef: 0}, simultaneous=True)
                    -(a-2*q)) == 0
    return {'projection_gap': True, 'anchor_area_factor': True,
            'circle_norm_lower_bound': True, 'opposite_direction_faces': True}


def verify_nonedge_expansion():
    t, a2, a3, a4, a7 = s.symbols('t a2 a3 a4 a7')
    H, w = reducer.H, reducer.W
    q05, q14, _, q25, q47, _ = reducer.QS
    intrinsic = (0, ALPHA/2, HALF+t*a2, HALF+t*a3, HALF+t*a4,
                 -BETA/2, t*(a3+w), t*a7)
    spatial = (0, ALPHA/2, HALF+t*a2, HALF+t*a3, HALF+t*(2*a3-a4),
               BETA/2+2*t*a3, t*a3, t*a7)
    rates = {q05: 2*BETA*a3, q14: 2*(1-ALPHA)*(a3-a4),
             q25: 2*(1-BETA)*(a2-a3), q47: 2*(a3-a7)}
    auxiliaries = (H[4]+q14/(1-ALPHA), H[4]+q05/BETA,
                   -H[6]+H[2]+w, -H[6]+H[2]-w+q25/(1-BETA),
                   -H[7]+H[3], -H[7]+H[3]+q47)
    shifts = ((0, 4, 0), (0, 4, -1), (2, 6, 0), (2, 6, 1), (3, 7, 0), (3, 7, 1))
    for (i, j, shift), expected in zip(shifts, auxiliaries):
        expression = ((spatial[j]-spatial[i]+t*(H[j]-H[i]))**2
                      -(intrinsic[j]-intrinsic[i]+shift)**2)
        assert s.expand(expression.subs(t, 0)) == 0
        assert s.cancel(s.diff(expression, t).subs(t, 0)-expected.subs(rates)) == 0
    return auxiliaries


def verify_families():
    hsymbols = s.symbols('h0:8')
    matrix = reducer.original_system([ALPHA/2, HALF, HALF, HALF, -BETA/2, 0])
    pivot = (0, 1, 2, 3, 8, 9, 10, 12, 13, 16, 17, 18, 20, 22)
    square = matrix[list(pivot), :]
    determinant = s.factor(square.det())
    assert determinant == 2*ALPHA**3*(BETA-1)**2
    inverse = square.inv()
    nonedge_auxiliaries = verify_nonedge_expansion()
    families = []
    expected = {
        (2, 6): [2*R/(ALPHA-1), (2*R-1)/BETA, 0, 0, 0, 0],
        (2, 7): [2*R/(ALPHA-1), 0, (2*R-1)/ALPHA, 0, 2*R*(2*R-1), 0],
        (3, 6): [0, (2*R-1)/BETA, 0, 2*R/(BETA-1), 0, 2*R*(2*R-1)],
        (3, 7): [0, 0, (2*R-1)/ALPHA, 2*R/(BETA-1), 0, 0],
        'left': [0, 0, 0, 0, -1, 0],
        'right': [0, 0, 0, 0, 0, -1],
    }
    for key, residuals in expected.items():
        deficit = [s.Integer(0)]*8
        P = [s.Integer(0)]*8
        if isinstance(key, tuple):
            deficit[key[0]], deficit[key[1]] = R, HALF-R
            P[3] = HALF/ALPHA-HALF+deficit[2]
            P[2], P[4] = HALF/ALPHA, HALF/ALPHA+deficit[2]-deficit[3]
            P[7], P[6] = deficit[7]-HALF, deficit[7]-deficit[6]
            P[5] = (BETA/(2*ALPHA)-HALF+BETA*(deficit[2]-deficit[3])
                    +(1-BETA)*(deficit[7]-deficit[6]))
        elif key == 'left':
            deficit[0], deficit[1] = (1-ALPHA)/2, ALPHA/2
            P = [s.Integer(value)/2 for value in (0, 0, 0, 1, 0, 1, 0, 1)]
        else:
            deficit[4], deficit[5] = BETA/2, (1-BETA)/2
            P = [0, 0, HALF/ALPHA, HALF/ALPHA-HALF, HALF/ALPHA, BETA/(2*ALPHA), 0, -HALF]
        weights = [HALF-value for value in deficit]
        assert s.expand(sum(weights)-s.Rational(7, 2)) == 0
        X = geometry.horizontal_displacements(weights)
        rhs = s.Matrix([s.expand((P[j]-P[i])**2-X[i, j]**2)
                        for i, j in reducer.EDGES]+[0]*5)
        auxiliary_values = (-inverse*rhs[list(pivot), :]).applyfunc(s.factor)
        assert all(s.factor(value) == 0 for value in matrix*auxiliary_values+rhs)
        substitution = dict(zip(reducer.AUXILIARIES, auxiliary_values))
        horizontal = (sum(deficit[:4]), sum(deficit[:4])-HALF,
                      sum(deficit[2:6])-HALF, sum(deficit[2:6]),
                      sum(deficit[3:7])-HALF, sum(deficit[3:7]))
        pairs = ((0, 4), (0, 4), (2, 6), (2, 6), (3, 7), (3, 7))
        actual = [s.factor((P[j]-P[i])**2-dx**2+expression.subs(substitution))
                  for (i, j), dx, expression in zip(pairs, horizontal, nonedge_auxiliaries)]
        assert all(s.cancel(left-right) == 0 for left, right in zip(actual, residuals))
        families.append({'id': list(key) if isinstance(key, tuple) else key,
                         'deficits': list(map(str, deficit)), 'P': list(map(str, P)),
                         'auxiliaries': list(map(str, auxiliary_values)),
                         'nonedge_residuals': list(map(str, actual))})
    return {'pivot_rows': pivot, 'pivot_determinant': str(determinant),
            'families': families, 'actual_embeddings_claimed': False}


def build(directory):
    directory.mkdir(parents=True, exist_ok=True)
    rank_checks = rank.symbolic_checks()
    checks = {'height_relations': verify_height_relations(),
              'symmetry_cover': verify_symmetry_cover(),
              'scalar_identities': verify_scalar_identities(),
              'marked_symmetries': rank_checks['marked_symmetries'],
              'metric_families': verify_families()}
    obligations = []

    def emit(name, model, additions, description):
        clauses = model.clauses+additions
        with FastSAT(model.n, clauses) as solver:
            assert solver.check() == -1, name
        filename = name+'.cnf'
        write_cnf(directory/filename, model.n, clauses)
        obligations.append({'file': filename, 'meaning': description,
                            'variables': model.n, 'clauses': len(clauses)})

    for lower in LOWER:
        model = ActualModel('B', lower)
        emit('c1_flat_nonparallel_B'+lower, model, [list(model.bits((2, 3, 6, 7)))],
             'nonparallel cap lines, canonical upper order B and lower order '+lower)
    model = ActualModel()
    additions = [[-bit] for quad in rank.RANK_QUADS for bit in model.bits(quad)]
    additions += [[model.bits(quad)[0]] for quad in ((0, 1, 2, 3), (0, 1, 2, 7))]
    emit('c1_flat_parallel_strict_anchor', model, additions,
         'parallel cap lines with actual 0123>0 and actual 0127>0')
    model = ActualModel('C', 'C')
    additions = [[model.bits((0, 1, 2, 3))[0]],
                 list(model.bits((3, 4, 5, 6)))+list(model.bits((4, 5, 6, 7)))]
    emit('c1_flat_double_coincidence_middle', model, additions,
         'double cap coincidence and actual 0123>0 force actual 3456=4567=0')
    packet = {'assumptions': ['ray1', '0<alpha,beta<1', 'both endpoint caps collinear'],
              'checks': checks, 'unsat_obligations': obligations,
              'classification': 'six explicit common-transverse-line families',
              'whole_boundary_excluded': False}
    (directory/'c1_flat_limits.json').write_text(json.dumps(packet, indent=2)+'\n')
    return packet


if __name__ == '__main__':
    if not __debug__:
        raise RuntimeError('run with assertions enabled')
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('output', type=Path)
    packet = build(parser.parse_args().output)
    print(json.dumps({'unsat_obligations': len(packet['unsat_obligations']),
                      'metric_families': len(packet['checks']['metric_families']['families']),
                      'whole_boundary_excluded': False}), flush=True)
