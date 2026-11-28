#!/usr/bin/env python3
"""Uniform bounded axis coordinates for Type-7 markings 1 and 2.

Usage: python exhaustive_remaining_axis.py [OUTPUT] [--mark 1] [--y 32]
       python exhaustive_remaining_axis.py OUTPUT --all-heights --y 32

The exact checks run before optional query generation.  The generated
38-real necessary systems keep every edge equation, six bounded product
variables, and the full generic-sign/actual-circuit embedding constraints.
There is no mask assumption and no marking is declared excluded.
With --all-heights, t=1/y^2 is a 39th variable with 0<t<=1/Y^2,
where --y supplies Y>=32. This keeps the entire finite-height tail,
not its t=0 relaxation. Metric equations then have total degree three.
"""

import argparse
from fractions import Fraction as F
from itertools import combinations
import json
from pathlib import Path
import re

import sympy as s

import remaining_full_metric as full

m = full.linked.m
ROOT = full.ROOT
PRODUCT_EDGES = ((0, 5), (1, 4), (2, 4), (2, 5), (4, 7), (5, 7))
COMMON = (2, 3, 6, 7)


def case_data(mark):
    assert mark in (1, 2)
    case = next(row for row in json.loads((ROOT/'linking_checkpoint/cases.json').read_text())
                if row['file'] == f't7_ray_{mark}.smt2')
    shifts, _, _ = full.linked.data(case)
    faces = [tuple(map(int, face)) for face in json.loads(
        (ROOT/'linking_checkpoint/lutz_faces.json').read_text())['7'].split()]
    edges = sorted({tuple(sorted(edge)) for face in faces for edge in combinations(face, 2)})
    return shifts, faces, edges


def rotation_gauges(mark):
    """For p(i)=i+r, K[p(i),p(j)]-K[i,j]=g[j]-g[i], exactly."""
    shifts, faces, edges = case_data(mark)
    cyclic_faces = {face[k:]+face[:k] for face in faces for k in range(3)}
    result = []
    for rotation in range(8):
        permutation = tuple((i+rotation) % 8 for i in range(8))
        assert {tuple(sorted((permutation[i], permutation[j]))) for i, j in edges} == set(edges)
        assert all(tuple(permutation[i] for i in face) in cyclic_faces for face in faces)
        gauge = {0: (0, 0)}
        for _ in range(8):
            for i, j in edges+[(j, i) for i, j in edges]:
                if i in gauge and j not in gauge:
                    gauge[j] = tuple(gauge[i][k]+shifts[permutation[i], permutation[j]][k]
                                     -shifts[i, j][k] for k in (0, 1))
        assert len(gauge) == 8
        for i, j in edges:
            assert tuple(shifts[permutation[i], permutation[j]][k]-shifts[i, j][k]
                         for k in (0, 1)) == tuple(gauge[j][k]-gauge[i][k] for k in (0, 1))
        result.append({'rotation': rotation, 'gauge': [gauge[i] for i in range(8)]})
    return result


def baselines(v):
    """Intrinsic v6 has been replaced by v3-1/2; spatial levels fold 4,5."""
    assert len(v) == 8
    intrinsic = list(v)
    intrinsic[6] = v[3]-s.Rational(1, 2)
    spatial = list(intrinsic)
    spatial[4] = 2*v[3]-v[4]
    spatial[5] = 2*v[3]-v[5]-1
    return intrinsic, spatial


def product_polynomials(v):
    return {
        (0, 5): (2*v[3]-1)*(2*v[3]-2*v[5]-1),
        (1, 4): -4*(v[1]-v[3])*(v[3]-v[4]),
        (2, 4): -4*(v[2]-v[3])*(v[3]-v[4]),
        (2, 5): -4*(v[2]-v[3])*(v[3]-v[5]-1),
        (4, 7): (2*v[3]-2*v[4]+1)*(2*v[3]-2*v[7]-1),
        (5, 7): (2*v[3]-2*v[5]-1)*(2*v[3]-2*v[7]-1),
    }


def verify():
    """Exact cocycle, propagation, cancellation and rational-bound checks."""
    t, w = s.symbols('t w')
    x = [s.Integer(0)]+list(s.symbols('x1:8'))
    v = [s.Integer(0)]+list(s.symbols('v1:8'))
    h = [s.Integer(0)]+list(s.symbols('H1:8'))
    intrinsic, spatial = baselines(v)
    offset = [s.Integer(0)]*8
    offset[6] = w
    products = product_polynomials(v)
    assert tuple(products) == PRODUCT_EDGES
    rotation_records = {}
    for mark in (1, 2):
        shifts, faces, edges = case_data(mark)
        assert len(edges) == 24
        assert all(shifts[0, i] == (0, 0) for i in (1, 2, 3, 5, 6, 7))
        assert all(shifts[1, i][1] == 0 for i in COMMON)
        assert shifts[3, 4] == shifts[1, 4] == (0, 0)
        assert shifts[3, 6][1] == 1
        for vertices in ((0, 1, 3), (3, 4, 6), (3, 5, 6)):
            assert any(set(face) == set(vertices) for face in faces)
            a, b, c = vertices
            assert tuple(shifts[a, b][k]+shifts[b, c][k] for k in (0, 1)) == shifts[a, c]
        period = tuple(sum(shifts[i, (i+1) % 8][k] for i in range(8)) for k in (0, 1))
        assert period == (-5+mark, 1)
        for i in range(8):
            triangle = (i, (i+1) % 8, (i+2) % 8)
            cycle_edges = tuple(zip(triangle, triangle[1:]+triangle[:1]))
            assert tuple(sum(shifts[edge][k] for edge in cycle_edges) for k in (0, 1)) == (-1, 0)
        rotation_records[str(mark)] = rotation_gauges(mark)
        nonzero = []
        for i, j in edges:
            X = x[j]-x[i]+shifts[i, j][0]+s.Rational(shifts[i, j][1], 2)
            V = intrinsic[j]-intrinsic[i]+shifts[i, j][1]
            dz, dh, dw = spatial[j]-spatial[i], h[j]-h[i], offset[j]-offset[i]
            product = s.expand(dz*dz-V*V)
            if product != 0:
                nonzero.append((i, j))
            assert s.expand(product-products.get((i, j), 0)) == 0
            # dP is the exact squared transverse difference.  Substituting
            # t*q=product makes the compact equation exactly the original.
            dP = s.Symbol('dP')
            compact_times_t = t*(dP-X*X+2*dz*dh-2*V*dw+t*(dh*dh-dw*dw))+product
            original = t*(dP-X*X)+(dz+t*dh)**2-(V+t*dw)**2
            assert s.expand(compact_times_t-original) == 0
        assert tuple(nonzero) == PRODUCT_EDGES

    # Individual small-step rates for mask04.  The second identity uses
    # the actual v6, so its w term has a minus sign.
    b2 = v[3]-v[2]
    b6 = v[7]-(v[3]-s.Rational(1, 2)+t*w)
    assert s.expand(products[2, 5]-4*b2*(v[3]-v[5]-1)) == 0
    assert s.expand(products[4, 7]-(2*v[3]-2*v[4]+1)*(-2*b6-2*t*w)) == 0

    # Polarization at axis01 and its exact transverse-norm formula.
    a, c, b, vi, A = s.symbols('a c b vi A')
    ell2 = b*b+t*a*a
    transverse = c*c+a*a*vi*vi/ell2-b*vi*A/ell2-t*A*A/(4*ell2)
    assert s.cancel(t*ell2*transverse-(ell2*(t*c*c+vi*vi)-(b*vi+t*A/2)**2)) == 0
    d, dr, dP, X = s.symbols('d dr dP X')
    assert s.expand(t*(dP-X*X)+(d+t*dr)**2-(d+1)**2
                    -(t*(dP-X*X+2*d*dr+t*dr*dr)-(2*d+1))) == 0

    # Face propagation of the reflected axial coordinate.
    V, Vk, Xk, R = s.symbols('V Vk Xk R')
    Dz = -V+t*R
    ell36sq = V*V+t*X*X
    lhs = (t*Xk*X+Vk*V)*Dz+Vk*ell36sq
    rhs = t*(Vk*V*R+Xk*X*Dz+Vk*X*X)
    assert s.expand(lhs-rhs) == 0

    # All numeric bounds below are rational; no numerical tolerance enters.
    S = F(257, 512)  # |Vij|<S for y>=8.
    assert 8*S+2 < 7
    common_transverse_sq = F(1, 4)+16*S*S+4*S
    assert common_transverse_sq < 9
    w_bound = (36+F(1, 4)+2*(2*S)*14+F(196, 64))/2
    assert w_bound < 34
    assert F(1, 2)-F(34, 1024) > F(7, 16)
    assert F(1, 2)-F(48, 1024) > F(7, 16)
    face_height = F(1, 2)+F(1, 2)*S/F(7, 16)
    assert face_height < F(9, 8)
    assert S*S+F(1, 4096) < F(17, 32)**2
    full_transverse = 3+F(17, 32)*F(96, 7)+F(9, 8)
    assert full_transverse == F(639, 56) and full_transverse < 12
    numerator = S*F(273, 512)*82+F(1, 4)*F(35, 64)+S*F(1, 4)
    reflected_axial = numerator/F(49, 256)+F(108, 7)+7
    assert reflected_axial == F(3473657, 25088) and reflected_axial < 144
    product_bound = 24**2+F(1, 4)+2*(4*S)*288+F(288**2, 1024)
    assert product_bound == F(7255, 4) and product_bound < 2048
    return {'markings': [1, 2], 'minimum_y': 32, 'rotation_gauges': rotation_records,
            'edge_identities': 48, 'common_transverse_norm_bound': 3,
            'common_axial_correction_bound': 7, 'vertical_phase_correction_bound': 34,
            'transverse_norm_bound': 12, 'reflected_axial_correction_bound': 144,
            'product_bound': 2048,
            'product_edges': [''.join(map(str, edge)) for edge in PRODUCT_EDGES],
            'reflected_axial_rational_bound': str(reflected_axial)}


def _smt(expression):
    """Translate the small exact polynomial expressions used in this chart."""
    expression = s.sympify(expression)
    if expression.is_Rational:
        return m.rat(F(int(expression.p), int(expression.q)))
    if expression.is_Symbol:
        return str(expression)
    if expression.is_Add:
        return m.add(*map(_smt, expression.args))
    if expression.is_Mul:
        return m.mul(*map(_smt, expression.args))
    if expression.is_Pow and expression.exp.is_Integer and expression.exp >= 0:
        return m.mul(*[_smt(expression.base)]*int(expression.exp))
    raise ValueError(expression)


def generate(mark, y=10**6, *, all_heights=False):
    """One full marking, at fixed y or for every height >= the given y.

    In all_heights mode an UNSAT proof excludes the entire height tail.
    SAT still requires independent reconstruction; UNKNOWN is no result.
    No positive lower bound is imposed on t or on a collapsing edge.
    """
    assert mark in (1, 2) and isinstance(y, int) and not isinstance(y, bool) and y >= 32
    assert isinstance(all_heights, bool)
    t = s.Symbol('t') if all_heights else s.Rational(1, y*y)
    shifts, faces, edges = case_data(mark)
    x = [s.Integer(0)]+list(s.symbols('x1:8'))
    v = [s.Integer(0)]+list(s.symbols('v1:8'))
    intrinsic, z = baselines(v)
    H = [s.Integer(0)]+list(s.symbols('H1:8'))
    w = s.Symbol('w')
    offsets = [s.Integer(0)]*8
    offsets[6] = w
    actual_v = [intrinsic[i]+t*offsets[i] for i in range(8)]
    axial = [z[i]+t*H[i] for i in range(8)]
    P = [(s.Integer(0), s.Integer(0)) for _ in range(8)]
    P[3] = (s.Symbol('p3u'), s.Integer(0))
    for i in (2, 4, 5, 6, 7):
        P[i] = tuple(s.symbols(f'p{i}u p{i}v'))
    q = {edge: s.Symbol('q'+''.join(map(str, edge))) for edge in PRODUCT_EDGES}
    declared = x[1:]+[v[i] for i in (1, 2, 3, 4, 5, 7)]+[w]+H[1:]
    declared += [value for point in P for value in point if value != 0]+list(q.values())
    assert len(declared) == len(set(declared)) == 38
    if all_heights:
        declared.append(t)
    lines = ['(set-logic QF_NRA)']+[f'(declare-fun {name} () Real)' for name in declared]

    def require(condition):
        lines.append(m.op('assert', condition))

    def bound(expression, size):
        text, limit = _smt(expression), _smt(size)
        require(m.all_([m.op('<', text, limit), m.op('>', text, m.neg(limit))]))

    def definition(name, expression):
        lines.append(f'(define-fun {name} () Real {_smt(expression)})')

    def transverse_distance(i, j):
        return sum((P[j][axis]-P[i][axis])**2 for axis in (0, 1))

    def scaled_distance(i, j):
        return t*transverse_distance(i, j)+(axial[j]-axial[i])**2

    if all_heights:
        require(m.op('>', 't', '0'))
        require(m.op('<=', 't', m.rat(F(1, y*y))))

    # Bounds proven uniformly, with no lower bound on a collapsing edge.
    require(m.op('>=', 'v1', m.rat(F(1, 8))))
    require(m.op('>', 'p3u', '0'))
    require(m.op('<', 'p2v', '0'))  # orientation [0123]>0
    for i in range(1, 8):
        bound(x[i], 1 if i == 4 else F(1, 2))
        bound(z[i], F(257, 256))
    for i in (1, 2, 3, 4, 5, 7):
        bound(v[i], F(257, 256) if i == 4 else F(257, 512))
    bound(w, 34)
    require(m.op('>=', 'H1', '0'))
    require(m.op('<=', 'H1', '1'))
    for i in (2, 3, 7):
        bound(H[i], 7)
    bound(H[6]-w, 7)
    for i in (4, 5):
        bound(H[i], 144)
    for i in range(2, 8):
        require(m.op('<', _smt(sum(value**2 for value in P[i])), '144'))
    for edge, variable in q.items():
        bound(variable, 2048)
        require(m.op('=', _smt(t*variable), _smt(product_polynomials(v)[edge])))

    X, V = {}, {}
    for i, j in edges:
        X[i, j] = x[j]-x[i]+shifts[i, j][0]+s.Rational(shifts[i, j][1], 2)
        V[i, j] = actual_v[j]-actual_v[i]+shifts[i, j][1]
        X[j, i], V[j, i] = -X[i, j], -V[i, j]
        definition(f'X{i}{j}', X[i, j])
        definition(f'V{i}{j}', V[i, j])
        definition(f'D{i}{j}', t*X[i, j]**2+V[i, j]**2)
        require(m.op('>', f'D{i}{j}', '0'))
        bound(X[i, j], F(1, 2))
        for sign in (-1, 1):
            bound(V[i, j]+sign*t*X[i, j]/2, s.Rational(1, 2)+t/8)
        V0 = intrinsic[j]-intrinsic[i]+shifts[i, j][1]
        dz, dh, dw = z[j]-z[i], H[j]-H[i], offsets[j]-offsets[i]
        metric = transverse_distance(i, j)-X[i, j]**2+q.get((i, j), 0)
        metric += 2*dz*dh-2*V0*dw+t*(dh*dh-dw*dw)
        assert s.Poly(metric, *declared).total_degree() <= (3 if all_heights else 2)
        require(m.op('=', _smt(metric), '0'))
    for i in range(8):
        require(m.op('<', _smt(X[i, (i+1) % 8]), '0'))
    for i, j in combinations(range(8), 2):
        if (i, j) in edges:
            continue
        distance = scaled_distance(i, j)
        definition(f'z{i}{j}', distance)
        require(m.op('>', f'z{i}{j}', '0'))
        for a in range(-4, 5):
            for b in range(-3, 4):
                translated = t*(x[j]-x[i]+a+s.Rational(b, 2))**2
                translated += (actual_v[j]-actual_v[i]+b)**2
                require(m.op('<=', f'z{i}{j}', _smt(translated)))
    areas = []
    for index, (a, b, c) in enumerate(faces):
        name = f'area{index}'
        definition(name, X[a, b]*V[a, c]-X[a, c]*V[a, b])
        areas.append(name)
    require(m.any_([m.all_([m.op('>', a, '0') for a in areas]
                           +[m.op('=', m.add(*areas), '2')]),
                    m.all_([m.op('<', a, '0') for a in areas]
                           +[m.op('=', m.add(*areas), '(- 2)')])]))

    # Reuse only the coordinate-independent Boolean/circuit schema.  Its
    # source mask and metric prefix are discarded entirely.
    source, metadata = full.generate(mark, '03', max(y, 10**6))
    suffix = source[source.index('(declare-fun b1 () Bool)'):]
    points = [(P[i][0], P[i][1], axial[i]) for i in range(8)]

    def minor(vertices, axes):
        first, *rest = vertices
        return m.det([[_smt(points[i][axis]-points[first][axis]) for axis in axes] for i in rest])

    for quad in combinations(range(8), 4):
        if not set(combinations(quad, 2)) <= set(edges):
            continue
        name = 'm'+''.join(map(str, quad))
        lines.append(f'(define-fun {name} () Real {minor(quad, (0, 1, 2))})')
        require(m.op('distinct', name, '0'))
    counts = {1: 0, 2: 0, 3: 0}
    for line in suffix.splitlines():
        match = re.fullmatch(r'\(define-fun (a([0-7]+)c([012]+)) \(\) Real .*\)', line)
        if match:
            name, vertices, axes = match.groups()
            vertices, axes = tuple(map(int, vertices)), tuple(map(int, axes))
            line = f'(define-fun {name} () Real {minor(vertices, axes)})'
            counts[len(axes)] += 1
        assert not re.search(r'\bG[1-7][1-7]\b', line)
        lines.append(line)
    assert counts == {1: 84, 2: 168, 3: 70}
    text = '\n'.join(lines)+'\n'
    assert len(re.findall(r'^\(declare-fun \S+ \(\) Real\)', text, re.M)) == len(declared)
    assert text.count('(check-sat)') == 1
    metadata = dict(metadata, y=y, real_variables=len(declared), mask=None,
                    axis='01 with v1>=1/8', metric_equations=24,
                    product_equations=6, metric_degree_bound=3 if all_heights else 2,
                    actual_minor_degree_bound=4 if all_heights else 3, direct_minor_counts=counts,
                    transverse_bound=12, axial_correction_bound=144, product_bound=2048,
                    necessary_system_only=True)
    if all_heights:
        metadata.update(y=None, minimum_y=y, t_interval=f'0 < t <= 1/{y*y}',
                        height_scope='entire tail', limit_at_zero=False,
                        product_degree_bound=2, nonedge_degree_bound=4)
    return text, metadata


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('output', type=Path, nargs='?')
    parser.add_argument('--mark', type=int, choices=(1, 2))
    parser.add_argument('--y', type=int, default=10**6)
    parser.add_argument('--all-heights', action='store_true',
                        help='keep t>0 symbolic; --y is the minimum height, not a sample')
    args = parser.parse_args()
    if args.y < 32:
        parser.error('the bounded axis chart requires y>=32')
    record = verify()
    print(json.dumps({key: value for key, value in record.items() if key != 'rotation_gauges'}), flush=True)
    if args.output is not None:
        args.output.mkdir(parents=True, exist_ok=True)
        (args.output/'axis_verification.json').write_text(json.dumps(record, indent=2)+'\n')
        for mark in (args.mark,) if args.mark else (1, 2):
            text, metadata = generate(mark, args.y, all_heights=args.all_heights)
            name = f'ray{mark}_axis'+('_all_heights' if args.all_heights else '')
            (args.output/f'{name}.smt2').write_text(text)
            (args.output/f'{name}.json').write_text(json.dumps(metadata, indent=2)+'\n')
            print(json.dumps(dict(metadata, bytes=len(text))), flush=True)


if __name__ == '__main__':
    if not __debug__:
        raise RuntimeError('run with assertions enabled')
    main()
