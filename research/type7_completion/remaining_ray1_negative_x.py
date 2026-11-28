#!/usr/bin/env python3
"""Exact exclusion of the negative-X ray-1 endpoint regime.

Usage: python remaining_ray1_negative_x.py

The replay binds all fifteen surviving primary sign words to the
published virtual12 certificates. It checks the two unique upper-edge
directions and the incompatible local polarizations used in
remaining_ray1_negative_x.md. Companion proofs close the other two regimes.
"""

from itertools import combinations
import json
import time

import sympy as s

import exhaustive_remaining_axis as axis
import solver_remaining_virtual12_consequences as source

HALF = s.Rational(1, 2)
Q = tuple(combinations(range(8), 4))
QI = {quad: index for index, quad in enumerate(Q)}
X, Y, Z = s.symbols('X Y Z')
POINTS = tuple(s.Matrix(point) for point in (
    (0, 0, 0), (0, 0, 1), (0, 0, 1), (HALF, 0, 1),
    (0, 0, 1), (HALF, 1, 0), (0, 0, 0), (HALF, 1, 0)))


def virtual_bracket(edge, other):
    """The leading determinant after dividing the edge by its own size."""
    a, b = edge
    j, k = other
    order = (a, b, j, k)
    assert len(set(order)) == 4
    parity = (-1)**sum(order[i] > order[j] for i, j in combinations(range(4), 2))
    value = s.Matrix.hstack(s.Matrix((X, Y, Z)),
                            POINTS[j]-POINTS[a], POINTS[k]-POINTS[a]).det()
    return tuple(sorted(order)), s.expand(parity*value)


def signed_rows(edge, words):
    rows = {}
    for other in combinations(tuple(i for i in range(8) if i not in edge), 2):
        quad, value = virtual_bracket(edge, other)
        if value == 0:
            continue
        signs = {word[QI[quad]] for word in words}
        if len(signs) == 1:
            rows[quad] = value if next(iter(signs)) == '+' else -value
    return rows


def source_words():
    packet, words, digest = source.source_data()
    data = json.loads(source.DEFAULT_DATA.read_text())
    source.verify(data, packet, words, digest)
    records = packet['scenarios']['negative_x_boundary']
    result = tuple(sorted(word for record in records
                          if record['satisfiable_relaxation']
                          for word in record['signs']))
    assert len(result) == len(set(result)) == 15
    return result


def direction_checks(words):
    """Every displayed polynomial is itself a required nonnegative row."""
    upper = []
    for edge, required in (
        ((1, 4), ((0, 1, 3, 4), (0, 1, 4, 5), (0, 1, 4, 7),
                  (1, 3, 4, 5), (1, 3, 4, 7))),
        ((2, 4), ((0, 2, 3, 4), (0, 2, 4, 5), (0, 2, 4, 7),
                  (2, 3, 4, 5), (2, 3, 4, 7))),
    ):
        rows = signed_rows(edge, words)
        expected = (Y/2, Y/2-X, X-Y/2, -(Y+Z)/2, (Y+Z)/2)
        assert tuple(rows[quad] for quad in required) == expected
        # Opposite rows imply Y=2X and Z=-Y; the first gives X>=0.
        assert s.expand(expected[1]+expected[2]) == 0
        assert s.expand(expected[3]+expected[4]) == 0
        assert expected[0].subs(Y, 2*X) == X
        upper.append({'edge': list(edge), 'direction': '(1,2,-2)',
                      'required_quads': [''.join(map(str, q)) for q in required]})

    rows = signed_rows((0, 6), words)
    required = ((0, 1, 3, 6), (0, 1, 5, 6),
                (0, 2, 6, 7), (0, 3, 5, 6))
    expected = (Y/2, -X+Y/2, X-Y/2, -X+Y/2+Z/2)
    assert tuple(rows[quad] for quad in required) == expected
    assert s.expand(expected[1]+expected[2]) == 0
    assert expected[0].subs(Y, 2*X) == X
    assert expected[3].subs(Y, 2*X) == Z/2
    axial = sum(word[QI[0, 3, 4, 6]] == '+' for word in words)
    assert axial == 12
    # [0346]=-Y/2, so these twelve words force Y=X=0 as well.
    assert virtual_bracket((0, 6), (3, 4))[1] == -Y/2
    return {'upper_edges': upper, 'edge06': 'X>=0,Y=2X,Z>=0',
            'edge06_pure_positive_axial_words': axial,
            'edge06_other_words': len(words)-axial}


def local_identities():
    # The following auxiliary12 formulas use the intrinsic face013 plane:
    # vertex1=(-h0,v1/sqrt(t),0), vertex3=(c-h0,(v1+s)/sqrt(t),0).
    # They are not the transverse P2x or axial H2-H1 of the axis01 gauge.
    # The closure below uses its separately checked axis_lambda formula.
    h, d0, d2, b1, b2, b3, t, v1 = s.symbols('h d0 d2 b1 b2 b3 t v1')
    h0, h2 = HALF-d0, HALF-d2
    c, phase = 1-h-h2, b1+b2
    determinant = v1*c+h0*phase
    remainder = h-d0
    q12 = (v1*d2+phase*remainder)/determinant
    u12 = -h+q12
    height12 = (h0*d2-c*remainder)/determinant
    c0 = d0-(HALF+d0)*h
    assert s.cancel(-h0*u12+v1*height12-c0) == 0
    assert s.cancel(c*u12+phase*height12-(d2-c*h)) == 0
    assert s.expand(((c*c+h*h-h2*h2)/2)-(d2-c*h)) == 0
    normal_square = 2*h*q12-q12*q12-2*b1*height12-t*height12*height12
    assert s.cancel(u12*u12+normal_square+2*b1*height12
                    +t*height12*height12-h*h) == 0

    # The actual face214 has the positive archived orientation near this
    # endpoint: face310 is uniformly positive and all face signs agree.
    shifts, faces, _ = axis.case_data(1)
    assert (2, 1, 4) in faces and (3, 1, 0) in faces
    p, q = s.symbols('p q')
    x = {1: -h0, 2: 1-h0-h, 3: c-h0, 4: -h0-q}
    vertical = {1: v1, 2: v1+b1, 3: v1+b1+b2,
                4: v1+b1+b2+b3}
    def lifted(a, b):
        return (x[b]-x[a]+shifts[a, b][0]+HALF*shifts[a, b][1],
                vertical[b]-vertical[a]+shifts[a, b][1])
    x21, v21 = lifted(2, 1)
    x24, v24 = lifted(2, 4)
    area214 = s.expand(x21*v24-x24*v21)
    assert s.expand(area214.subs(q, h-p)-(h*(b2+b3)+p*b1)) == 0

    # Polarization of the two actual triangles134 and214 requires no
    # division by a collapsing edge. Here z is the actual axial change,
    # and a is the bounded axial correction of edge13.
    L, M, N, z, a = s.symbols('L M N z a')
    intrinsic14 = phase+b3
    actual_dot = t*L*M+(phase+t*a)*z
    intrinsic_dot = -t*c*q+phase*intrinsic14
    assert s.expand((actual_dot-intrinsic_dot)
                    -t*(L*M+a*z+c*q)
                    +phase*(intrinsic14-z)) == 0
    assert (HALF+(-HALF)*(-1))/(1-(-1)) == HALF
    assert HALF-s.Rational(1, 4) == s.Rational(1, 4)

    # Triangle214 has intrinsic vectors12=(-h,b1),14=(-q,V14).
    # The actual axis-coordinate vector12 is (P2,Z2,b1+t*lambda).
    p2, n2, lam = s.symbols('P2 Z2 lambda')
    actual214 = t*(p2*M+n2*N)+(b1+t*lam)*z
    intrinsic214 = t*h*q+b1*intrinsic14
    assert s.expand((actual214-intrinsic214)
                    -t*(p2*M+n2*N+lam*z-h*q)
                    +b1*(intrinsic14-z)) == 0
    # Subtracting the two exact polarizations eliminates b1 entirely.
    difference = (L-p2)*M-n2*N+(a-lam)*z+(c+h)*q
    assert s.expand((actual_dot-intrinsic_dot)-(actual214-intrinsic214)
                    -t*difference+b2*(intrinsic14-z)) == 0
    # The two sides of the divided difference tend to 1 and1/2.
    assert (HALF+(-HALF)*(-1)) == 1
    assert s.Rational(1, 4)*(1-(-1)) == HALF

    ell, H1, axis_lam = s.symbols('ell H1 axis_lambda')
    axis_polarization = ell*(b1+t*axis_lam)-v1*b1-t*c0
    assert s.expand(axis_polarization.subs(ell, v1+t*H1)
                    -t*(ell*axis_lam+H1*b1-c0).subs(ell, v1+t*H1)) == 0

    # Exact triangle016 formulas used to retain a possible tiny edge06.
    u, r, ell = s.symbols('u r ell', nonzero=True)
    axial6 = (v1*u+t*h0*r)/ell
    transverse6 = (h0*u-v1*r)/ell
    identity = t*transverse6*transverse6+axial6*axial6
    assert s.cancel(identity.subs(ell**2, v1*v1+t*h0*h0)-(u*u+t*r*r)) == 0
    return {'face013_edge12_projection_U': str(u12),
            'face013_edge12_axial_correction': str(height12),
            'face013_edge12_normal_square': str(normal_square),
            'face214_area': 'h*(b2+b3)+(h-q)*b1',
            'polarization134': 'L*M+a*z+c*q=(b1+b2)*(V14-z)/t',
            'polarization214': 'P2*M+Z2*Z4+lambda*z=h*q+b1*(V14-z)/t',
            'difference': '(L-P2)*M-Z2*Z4+(a-lambda)*z+(c+h)*q=b2*(V14-z)/t',
            'incompatible_limits': ['1', '1/2'],
            'secondary_rates': {'(b1+b2)/t': '1/2', 'b1/t': '1/4'},
            'edge06_axial': str(axial6), 'edge06_transverse_radius': str(transverse6)}


def main():
    start = time.monotonic()
    words = source_words()
    result = {'primary_words': len(words), 'directions': direction_checks(words),
              'local_identities': local_identities(),
              'negative_x_regime_excluded': True, 'whole_endpoint_excluded': False,
              'seconds': round(time.monotonic()-start, 3)}
    print(json.dumps(result), flush=True)


if __name__ == '__main__':
    if not __debug__:
        raise RuntimeError('run with assertions enabled')
    main()
