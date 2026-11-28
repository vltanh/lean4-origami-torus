#!/usr/bin/env python3
"""Exclude the positive-core orientation of the C0 double coincidence.

The relative diagonal estimate is exact before taking a limit.  A
single virtual-direction CNF requires independent RUP replay.
"""

import argparse
from itertools import combinations, product
import json
from pathlib import Path

import sympy as s

import exhaustive_c0_collinear as boundary
import exhaustive_c0_flat_common as common
import exhaustive_remaining_axis as axis
import solver_remaining_c1_geometry as geometry
from solver_chambers import write_cnf
from solver_sat import FastSAT

HALF = s.Rational(1, 2)


def metric_checks():
    t, ell, b, h0, length, a, g = s.symbols('t ell b h0 L a g')
    norm, other_norm, dot, z4, horizontal, vertical = s.symbols('R2 S2 dot z4 X14 V14')
    e01 = ell**2-b**2-t*h0**2
    e13 = t*norm+t*t*a*a-t*length*length-t*t*g*g
    e03 = t*norm+(ell+t*a)**2-t*(length-h0)**2-(b+t*g)**2
    polar = ell*a-b*g+h0*length
    assert s.expand(e03-e01-e13-2*t*polar) == 0
    e14 = t*other_norm+(z4-ell)**2-t*horizontal**2-vertical**2
    e34 = (t*(norm+other_norm-2*dot)+(z4-ell-t*a)**2
           -t*(horizontal-length)**2-(vertical-t*g)**2)
    second = dot+a*(z4-ell)-length*horizontal-g*vertical
    assert s.expand(e14+e13-e34-2*t*second) == 0
    norm_identity = ell**2*norm-(b*length+t*h0*g)**2
    witness = ell**2*(e13/t)+(length**2+t*g*g)*e01 \
        -t*polar*(ell*a+b*g-h0*length)
    assert s.expand(norm_identity-witness) == 0
    coefficient = b*(z4-ell)/ell-vertical
    rhs = length*(horizontal+h0*(z4-ell)/ell)-dot
    assert s.cancel(coefficient*g-rhs-second+(z4-ell)*polar/ell) == 0

    # Exact source binding: 013 and 134 have zero cocycle period, while
    # 012 has the checked horizontal period -1.  All vertical periods
    # used below are zero.
    shifts, _, _ = axis.case_data(1)
    for tri in ((0, 1, 3), (1, 3, 4), (1, 2, 4)):
        i, j, k = tri
        assert tuple(shifts[i, j][a]+shifts[j, k][a]-shifts[i, k][a]
                     for a in (0, 1)) == (0, 0)
    assert tuple(shifts[0, 1][a]+shifts[1, 2][a]-shifts[0, 2][a]
                 for a in (0, 1)) == (-1, 0)
    h = s.symbols('h0:8')
    X = geometry.horizontal_displacements(h)
    assert s.expand(X[1, 3]-(1-h[1]-h[2])) == 0
    assert s.expand(X[0, 3]-X[0, 1]-X[1, 3]) == 0
    assert s.expand(X[1, 4]-X[1, 3]-X[3, 4]) == 0
    assert s.expand(X[1, 4]-X[1, 2]-X[2, 4]) == 0
    k12 = s.expand((X[0, 2]**2-X[0, 1]**2-X[1, 2]**2)/2)
    assert s.expand(k12.subs(h[1], HALF)+h[0]/2) == 0

    # The source after dividing edge13 by L and taking its unit
    # direction w=2P2.  No transverse cap area is divided by t.
    lu, h3, eP4, A, G, a2, g2 = s.symbols('lu h3 eP4 A G a2 g2')
    r1 = A-G+2*h0
    r2 = -eP4-lu*A/2+h3-lu*G/2
    r3 = a2-g2+h0
    r4 = -eP4/2-lu*a2/2-h3/2-lu*g2/2
    assert s.expand(lu*(A-2*a2)-2*h3+r2-2*r4-lu*(r1-2*r3)/2) == 0

    # The determinant identity used in the actual finite sequence.
    z1, z7, aa, a3 = s.symbols('z1 z7 aa a3')
    p2, p3, p7 = [s.Matrix(s.symbols(f'p{i}x p{i}y')) for i in (2, 3, 7)]
    cross = lambda p, q: s.det(s.Matrix.hstack(p, q))
    determinant = s.det(s.Matrix.hstack(
        p2.col_join(s.Matrix([t*aa])), p3.col_join(s.Matrix([t*a3])),
        p7.col_join(s.Matrix([z7-z1]))))
    assert s.expand(determinant-(z7-z1)*cross(p2, p3)
                    -t*(aa*cross(p3, p7)-a3*cross(p2, p7))) == 0
    return {'finite_polarization_identities': 2, 'finite_relative_norm_identity': True,
            'cocycle_bindings': 4, 'divided_tilt': 'h3/(1-2u)>0',
            'finite_determinant_identity': True}


class VirtualUpper(common.FlatModel):
    """Actual macro signs and the independently normalized diagonal13."""

    def __init__(self, core_positive=True, independent_pair=(2, 7)):
        super().__init__('d', 'd', boundary.height_relations())
        if core_positive:
            self.clauses.append([self.bits((0, 1, 2, 7))[0]])
        nodes = (2, 4, 5, 7, 8)  # 8 is the unit limit P3/L.
        self.virtual = {(i, 8): self.new_trit() for i in nodes[:-1]}

        def cross(i, j, sign=1):
            if i == j:
                return None
            if i > j:
                return cross(j, i, -sign)
            pair = self.virtual[i, j] if j == 8 else self.bits((0, 1, i, j))
            return pair if sign > 0 else pair[::-1]

        self.cross = cross
        # The caller's two projected vectors are independent, and the
        # virtual vector is nonzero. The default is the proved core case.
        assert len(set(independent_pair)) == 2 and set(independent_pair) <= set(nodes[:-1])
        self.clauses.append([bit for node in independent_pair for bit in cross(node, 8)])
        products = {}

        def multiply(left, right):
            key = tuple(sorted((left, right)))
            if key not in products:
                result = self.new_trit()
                products[key] = result
                for x, y, z in product((-1, 0, 1), repeat=3):
                    if x*y != z:
                        self.clauses.append(self.deny(left, x)+self.deny(right, y)
                                            +self.deny(result, z))
            return products[key]

        for i, j, k, l in combinations(nodes, 4):
            self.sumzero((multiply(cross(i, j), cross(k, l)),
                          multiply(cross(i, k, -1), cross(j, l)),
                          multiply(cross(i, l), cross(j, k))))

        # Exact first coefficient of every determinant containing13.
        u, v, alpha = s.symbols('u v alpha')
        heights = (0, HALF, HALF, HALF, u, v, 0, 0)
        vectors = {0: None, 1: None, 2: (2, 1), 3: (8, alpha),
                   4: (4, 1), 5: (5, 1), 6: None, 7: (7, 1)}
        crosses = {pair: s.Symbol('C'+''.join(map(str, pair)))
                   for pair in combinations(nodes, 2)}

        def ci(i, j):
            if vectors[i] is None or vectors[j] is None:
                return s.Integer(0)
            a, p = vectors[i]
            b, q = vectors[j]
            if a == b:
                return s.Integer(0)
            return p*q*(1 if a < b else -1)*crosses[tuple(sorted((a, b)))]

        def origin(i, j, k):
            return heights[i]*ci(j, k)-heights[j]*ci(i, k)+heights[k]*ci(i, j)

        count = 0
        self.normalized = {}
        for quad in common.QUADS:
            if not {1, 3} <= set(quad):
                continue
            i, j, k, l = quad
            polynomial = s.expand(origin(j, k, l)-origin(i, k, l)
                                  +origin(i, j, l)-origin(i, j, k))
            expression = s.expand(polynomial/alpha)
            assert not expression.has(alpha)
            normalized = self.new_trit()
            self.normalized[quad] = normalized
            forms = [normalized[::-1]]
            for pair, variable in crosses.items():
                coefficient = expression.coeff(variable)
                assert s.Poly(coefficient, u, v).total_degree() <= 1
                corners = [coefficient.subs({u: a, v: b})
                           for a, b in product((0, HALF), repeat=2)]
                if all(value == 0 for value in corners):
                    continue
                sign = 1 if all(value >= 0 for value in corners) else -1
                assert all(sign*value >= 0 for value in corners)
                forms.append(cross(*pair, sign))
            self.sumzero(forms)
            literal = boundary.shared.common.lit(quad)
            self.clauses.extend(([-normalized[0], literal], [-normalized[1], -literal]))
            count += 1
        assert count == 15
        self.normalized_brackets = count


def build(directory):
    directory.mkdir(parents=True, exist_ok=True)
    checks = metric_checks()
    model = VirtualUpper()
    # Negate: P2 x w=0, P7 x w<0, and generic chi1237=+.
    violation = list(model.cross(2, 8))+[-model.cross(7, 8)[1],
                                        -boundary.shared.common.lit((1, 2, 3, 7))]
    clauses = model.clauses+[violation]
    with FastSAT(model.n, clauses) as solver:
        assert solver.check() == -1
    filename = 'c0_double_coincidence_positive_core_virtual.cnf'
    write_cnf(directory/filename, model.n, clauses)
    packet = {'checks': checks, 'normalized_brackets': model.normalized_brackets,
              'unsat_obligations': [{'file': filename, 'variables': model.n,
                                    'clauses': len(clauses)}],
              'excluded': 'interior ray1 C0, P1=P3 and P0=P6, actual C27>0',
              'remaining': 'nonparallel bd/da, or dd with actual C27<0',
              'relative_rate_assumptions': [], 'whole_flat_C0_exclusion_claimed': False}
    (directory/'double_coincidence.json').write_text(json.dumps(packet, indent=2)+'\n')
    return packet


if __name__ == '__main__':
    if not __debug__:
        raise RuntimeError('run with assertions enabled')
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('output', type=Path)
    result = build(parser.parse_args().output)
    print(json.dumps({'unsat_obligations': len(result['unsat_obligations']),
                      'excluded': result['excluded']}), flush=True)
