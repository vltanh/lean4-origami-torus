#!/usr/bin/env python3
"""Exact cap identities, boundary kernels, and F1 cocycle substitutions.

This verifies necessary identities; it is not an infeasibility certificate.
"""
from pathlib import Path
from collections import Counter
from itertools import combinations, permutations, product
import sys

import sympy as sp

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent / "type5_focus" / "fixed_elongated"))
import generate as fixed


def zero(expr):
    assert sp.expand(expr) == 0, sp.factor(expr)


h1, h2, b1, b2 = sp.symbols("h1 h2 b1 b2")
h3 = 1 - h1 - h2
s = h1 + h2 - sp.Rational(1, 2)
c = h1 * h2 - s
T = sp.Matrix([[h1**2, -c], [-c, h2**2]])
b = sp.Matrix([b1, b2])
B = T + b * b.T
D = (1 - 2*h1) * (1 - 2*h2) * (1 - 2*h3) / 4

zero(T.det() - D)
zero(B[0, 0] - (h1**2 + b1**2))
zero(B[1, 1] - (h2**2 + b2**2))
zero(B[0, 0] + B[1, 1] - 2*B[0, 1]
     - (h3**2 + (b2-b1)**2))
zero(B.det() - D - (b.T * T.adjugate() * b)[0])
zero(h2**2 * (B.det() - D) - (h2**2*b1 + c*b2)**2 - D*b2**2)
zero(h1**2 * (B.det() - D) - (h1**2*b2 + c*b1)**2 - D*b1**2)
print("PASS: cap Gram decomposition, product determinant, two division-free SOS identities")

plus = sp.Matrix([h2, h1])
minus = sp.Matrix([h2, -h1])
phase_plus = h2*b1+h1*b2
phase_minus = h2*b1-h1*b2
zero((plus.T*B*plus)[0] - phase_plus**2 - h1*h2*(1-2*h3))
zero((minus.T*B*minus)[0] - phase_minus**2 - h1*h2*(1-2*h1)*(1-2*h2))
zero((plus.T*B*minus)[0] - phase_plus*phase_minus)
print("PASS: orthogonal horizontal normal form for the two cap vector combinations")

w = sp.symbols("w")
zero((w*B).det() - w**2*(D+(b.T*T.adjugate()*b)[0]))
print("PASS: scaled determinant identity for an arbitrary nonzero lattice period")

# These are polynomial identities on whole faces, including face intersections.
zero((B.det() - (h2*b1-h1*b2)**2).subs(h1, sp.Rational(1, 2)))
zero((B.det() - (h2*b1-h1*b2)**2).subs(h2, sp.Rational(1, 2)))
zero((B.det() - (h2*b1+h1*b2)**2).subs(h2, sp.Rational(1, 2)-h1))
print("PASS: all three cap-collapse boundary kernels, including their intersections")

# Angular identity after multiplication by the positive factor 2*|u|*|v|.
hx, hy, vx, vy = sp.symbols("hx hy vx vy")
u = sp.Matrix([hx, vx])
v = sp.Matrix([hy, vy])
w = sp.Matrix([1-hx-hy, -vx-vy])
zero(w.dot(w) - u.dot(u) - v.dot(v) - 2*u.dot(v)
     - (2*w[0]-1))
print("PASS: exact cosine difference for cap exterior and intrinsic turns")

F1 = {"00020220", "00020221", "00020222", "00120220", "00120221"}
cells = {"".join(map(str, a)): (a, q) for a, q in fixed.rep}
assert F1 <= cells.keys()
for label in F1:
    a, _ = cells[label]
    assert all(a[i] == 0 for i in (0, 1, 4))
    assert all(a[i] == 2 for i in (3, 5, 6))

x = sp.symbols("x0:8")
v = sp.symbols("v0:8")
y = sp.symbols("y")


def displacement(i, j):
    m, n = fixed.K[i, j]
    return (x[j]-x[i]+sp.Rational(m)+sp.Rational(n, 2),
            v[j]-v[i]+n*y)


for cycle in ((1, 0, 4), (5, 6, 3)):
    edges = list(zip(cycle, cycle[1:] + cycle[:1]))
    assert sum(fixed.K[e][0] for e in edges) == 1
    assert sum(fixed.K[e][1] for e in edges) == 0
    zero(sum(displacement(*e)[0] for e in edges)-1)
    zero(sum(displacement(*e)[1] for e in edges))

gauge = {x[1]: 0, v[1]: 0}
substitutions = [
    ((1, 0, 4), (x[0], -x[4], 1+x[4]-x[0], v[0], v[4])),
    ((5, 6, 3), (x[6]-x[5]+sp.Rational(1, 2),
                  x[5]-x[3]+sp.Rational(1, 2), x[3]-x[6],
                  v[6]-v[5]+y, v[3]-v[5]+y)),
]
for (base, first, second), (a, d, e, p, q) in substitutions:
    first_edge = tuple(z.subs(gauge) for z in displacement(base, first))
    second_edge = tuple(z.subs(gauge) for z in displacement(base, second))
    opposite = tuple(z.subs(gauge) for z in displacement(first, second))
    zero(first_edge[0]-a)
    zero(first_edge[1]-p)
    zero(second_edge[0]+d)
    zero(second_edge[1]-q)
    zero(opposite[0]-e)
    zero(opposite[1]-(q-p))

print("PASS: archived sharp cocycle substitutions for 014 and 356 in all five F1 cells")

# Exact topology of the two cap cuts. Spatial embeddedness is proved in the note.
face_sets = {frozenset(f) for f in fixed.faces}
caps = {frozenset((0, 1, 4)), frozenset((3, 5, 6))}
short = {frozenset(map(int, f)) for f in '031 053 045 136 164 465'.split()}
long = {frozenset(map(int, f)) for f in '012 024 152 147 175 263 237 274 256 357'.split()}
assert short.isdisjoint(long) and short | long == face_sets
assert caps.isdisjoint(face_sets)
cap_edges = {frozenset(e) for f in caps for e in combinations(f, 2)}
for annulus in (short, long):
    counts = Counter(frozenset(e) for f in annulus for e in combinations(f, 2))
    assert set(counts.values()) <= {1, 2}
    assert {e for e, count in counts.items() if count == 1} == cap_edges
    vertices = set().union(*annulus)
    assert len(vertices) - len(counts) + len(annulus) == 0
    unseen = set(annulus)
    todo = [unseen.pop()]
    while todo:
        f = todo.pop()
        neighbors = {g for g in unseen if len(f & g) == 2}
        unseen -= neighbors
        todo.extend(neighbors)
    assert not unseen
opposite = ((0, 6), (1, 5), (3, 4))
assert short | caps == {frozenset(f) for f in product(*opposite)}
tetrahedra = [frozenset(map(int, t)) for t in '0124 1247 1257 2357 2356'.split()]
counts = Counter(frozenset(f) for t in tetrahedra for f in combinations(t, 3))
assert set(counts.values()) <= {1, 2}
assert {f for f, count in counts.items() if count == 1} == long | caps
assert {f for f, count in counts.items() if count == 2} == {
    frozenset(map(int, f)) for f in '124 127 257 235'.split()}
for t in tetrahedra:
    assert all(tuple(sorted(e)) in fixed.E for e in combinations(t, 2))
assert frozenset((1, 2, 5)) in face_sets
assert {frozenset(map(int, f)) for f in '256 236 012 024'.split()} <= face_sets
assert all((2, i) in fixed.K for i in fixed.V if i != 2)
for cap, others in ((frozenset((0, 1, 4)), (2, 5)),
                    (frozenset((3, 5, 6)), (1, 2))):
    for other in others:
        assert all(tuple(sorted(e)) in fixed.E for e in combinations(cap | {other}, 2))
print("PASS: two annuli, embedded-sphere combinatorics, five-K4 chain, and anchor-face incidences")

# If both cap piercings occurred, these two convex combinations would coincide.
s, t, U, V = sp.symbols('s t U V')
alpha = s*(1-t)/(1-s*t)
beta = (1-t)/(1-s*t)
assert sp.factor(alpha*U+(1-alpha)*t*V - beta*s*U-(1-beta)*V) == 0
assert sp.factor(1-alpha-(1-s)/(1-s*t)) == 0
assert sp.factor(1-beta-t*(1-s)/(1-s*t)) == 0
print("PASS: exact intersection identity excluding simultaneous cap piercings")

assert sp.Rational(2000)**2 + sp.Rational(1, 4) < 2001**2
assert sp.Rational(119, 250)-sp.Rational(2, 1000) == sp.Rational(237, 500)
assert sp.Rational(237, 500)*10**6-2001 > 2000
assert {label for label in F1 if cells[label][0][2] == 0} == {
    '00020220', '00020221', '00020222'}
print("PASS: cap-entry phase margins and the three first-cap endpoint cells")
def check_leaf_geometry(root):
    import ast
    from itertools import combinations
    import json
    from pathlib import Path
    import re

    import sympy as sp

    root = Path(root)

    def zero(expr):
        assert sp.cancel(expr) == 0, sp.factor(expr)

    def matrix_zero(matrix):
        for entry in matrix:
            zero(entry)

    def read(relative):
        return (root / relative).read_text()

    def lean_list(text, pattern):
        match = re.search(pattern, text, flags=re.S)
        assert match, pattern
        return ast.literal_eval(match[1])

    # The unweighted cycle and the (permuted) Horn matrix.
    C = sp.zeros(5)
    cycle = {tuple(sorted((i, (i + 1) % 5))) for i in range(5)}
    for i, j in cycle:
        C[i, j] = C[j, i] = 1
    H = sp.Matrix([
        [1, 1, -1, -1, 1],
        [1, 1, 1, -1, -1],
        [-1, 1, 1, 1, -1],
        [-1, -1, 1, 1, 1],
        [1, -1, -1, 1, 1],
    ])
    one = sp.ones(5, 1)
    matrix_zero(C * H - 2 * sp.eye(5))
    matrix_zero(H * one - one)
    x = sp.symbols("x")
    zero(C.charpoly(x).as_expr() - (x - 2) * (x**2 + x - 1)**2)
    negative = {e for e in combinations(range(5), 2) if H[e] == -1}
    assert negative == set(combinations(range(5), 2)) - cycle
    assert all(sum(i in e for e in negative) == 2 for i in range(5))
    assert not any(all(e in negative for e in combinations(t, 2))
                   for t in combinations(range(5), 3))
    z = sp.Matrix(sp.symbols("z0:5"))
    m = sp.symbols("m")
    zero((z.T * H * z)[0] - sum(z)**2
         + 4 * sum(z[i] * z[j] for i, j in negative))
    q = z + m * one
    zero((q.T * H * q)[0] - (z.T * H * z)[0]
         - 2 * m * sum(z) - 5 * m**2)

    a, b, c, d, e = sp.symbols("a b c d e", positive=True)
    S = sp.Matrix([[0, a, 0, 0, e],
                   [a, 0, b, 0, 0],
                   [0, b, 0, c, 0],
                   [0, 0, c, 0, d],
                   [e, 0, 0, d, 0]])
    determinant = 2 * a * b * c * d * e
    zero(S.det() - determinant)
    delta0 = sp.sqrt(a * c * e / (b * d))
    delta = [delta0, a / delta0, b * delta0 / a,
             c * a / (b * delta0), d * b * delta0 / (c * a)]
    D = sp.diag(*delta)
    matrix_zero(D * C * D - S)
    inverse = S.inv()
    matrix_zero(inverse - D.inv() * H * D.inv() / 2)
    inverse_sum = (one.T * inverse * one)[0]
    positive_vector = D.inv() * one
    zero(inverse_sum - (positive_vector.T * H * positive_vector)[0] / 2)
    print("PASS: weighted C5 inverse sum, Horn identities, and inertia polynomial")

    # The singular path: exact kernel and a nonzero four-by-four minor.
    S0 = S.subs(b, 0)
    lam = sp.Matrix([0, -e * c, -a * d, 0, a * c])
    matrix_zero(S0 * lam)
    zero(S0.extract(range(4), range(4)).det() - a**2 * c**2)
    zero(sum(lam) - a * c * (1 - e / a - d / c))
    P = C.copy()
    P[1, 2] = P[2, 1] = 0
    zero(P.charpoly(x).as_expr() - x * (x**2 - 1) * (x**2 - 3))
    print("PASS: singular C5 kernel, rank-four minor, and path inertia polynomial")

    # Arbitrary-core completion.  G is the signed Gram matrix of the K_i;
    # arbitrary diagonal entries encode a change of affine origin.
    u = S.adjugate() * one
    total = sum(u)
    matrix_zero(S * u - determinant * one)
    E = sp.zeros(5, 4)
    for i in range(4):
        E[i, i] = 1
        E[4, i] = -1
    matrix_zero(E.T * S * u)
    zero((u.T * S * u)[0] - determinant * total)
    zero(E.row_join(u).det() - total)
    norms = sp.Matrix(sp.symbols("norm0:5"))
    G = S + (norms * one.T + one * norms.T) / 2
    for i in range(5):
        # The barycentric center has coefficients u/total and radius
        # -det(S)/total = -1/(1^T S^-1 1).
        zero(G[i, i] * total**2 - 2 * total * (G * u)[i]
             + (u.T * G * u)[0] + determinant * total)
    matrix_zero(E.T * G * E - E.T * S * E)
    t = sp.symbols("t")
    normal_coefficients = inverse * one
    for i in range(5):
        zero(S[i, i] - 2 * t * (S * normal_coefficients)[i]
             + t**2 * (normal_coefficients.T * S * normal_coefficients)[0]
             - (inverse_sum * t**2 - 2 * t))
    c0, kappa = sp.symbols("c0 kappa", positive=True)
    zero(c0 * t**2 - 2 * t - c0 * t * (t - 2 / c0))
    zero(c0 * (2 / c0)**2 - 4 / c0)
    zero((-1 / c0 + kappa * t**2).subs(t, 1 / sp.sqrt(c0 * kappa)))
    zero((-1 / c0 + kappa * t**2).subs(t, -1 / sp.sqrt(c0 * kappa)))
    zero(4 * kappa / (c0 * kappa) - 4 / c0)
    zero(inverse_sum.subs({a: 1, b: t, c: 1, d: 1, e: 1})
         - (4 * t + 1) / (2 * t))
    print("PASS: arbitrary-core signed circumcenter and both reflection quadratics")

    faces = lean_list(read("OrigamiTorus/Type5/Reconstruction.lean"),
                      r"def faces : List Triangle :=\s*(\[.*?\])")
    archived_faces = [tuple(map(int, f)) for f in json.loads(
        read("research/type5_focus/lutz_faces.json"))["5"].split()]
    assert faces == archived_faces
    face_sets = {frozenset(f) for f in faces}
    edges = {tuple(sorted(pair)) for f in faces for pair in combinations(f, 2)}
    assert len(faces) == 16 and len(edges) == 24
    assert set(combinations(range(8), 2)) - edges == {(0, 6), (0, 7), (3, 4), (6, 7)}
    orders = {0: (2, 3, 4, 1, 5), 6: (5, 3, 4, 2, 1), 7: (1, 3, 4, 5, 2)}
    hinges = {0: 5, 6: 1, 7: 2}
    for leaf, order in orders.items():
        link_edges = {tuple(sorted(v for v in f if v != leaf))
                      for f in faces if leaf in f}
        nonlink_edges = set(combinations(sorted(order), 2)) - link_edges
        assert nonlink_edges == {tuple(sorted((order[i], order[(i + 1) % 5])))
                                 for i in range(5)}
        assert (order[1], order[2]) == (3, 4)
        assert order[4] == hinges[leaf]
        assert nonlink_edges - edges == {(3, 4)}
        for left, right in nonlink_edges & edges:
            middle = [v for v in order
                      if tuple(sorted((left, v))) in link_edges
                      and tuple(sorted((right, v))) in link_edges]
            assert len(middle) == 1
            clique = (leaf, left, middle[0], right)
            assert len(set(clique)) == 4
            assert all(tuple(sorted(pair)) in edges for pair in combinations(clique, 2))
        for root_vertex in (3, 4):
            assert frozenset((leaf, hinges[leaf], root_vertex)) in face_sets
    print("PASS: all three actual leaf links, strict K4 chords, and distinguished hinges")

    cocycle_text = read("OrigamiTorus/Winding/WindingCocycle.lean")
    coefficients = dict(lean_list(cocycle_text,
        r"def coefficients.*?\| \.type5 =>\s*(\[.*?\])"))
    assert re.search(r"def basisCycles.*?\| \.type4 \| \.type5 => "
                     r"\(\(0,1,4\),\(0,1,5\)\)", cocycle_text, flags=re.S)

    def directed(cochain):
        result = {edge: tuple(cochain.get(edge, (0, 0))) for edge in edges}
        result.update({(j, i): tuple(-v for v in shift)
                       for (i, j), shift in list(result.items())})
        result.update({(i, i): (0, 0) for i in range(8)})
        return result

    def cycle_shift(cochain, cycle_vertices):
        ee = list(zip(cycle_vertices, cycle_vertices[1:] + cycle_vertices[:1]))
        return tuple(sum(cochain[edge][j] for edge in ee) for j in range(2))

    def root_shifts(cochain):
        return tuple(tuple(cochain[leaf, 4][j] - cochain[leaf, 3][j]
                           for j in range(2)) for leaf in (0, 6, 7))

    def differences(shifts):
        return sp.Matrix([[shifts[i][j] - shifts[1][j] for j in range(2)]
                          for i in (0, 2)])

    dual = directed(coefficients)
    assert all(cycle_shift(dual, f) == (0, 0) for f in faces)
    assert cycle_shift(dual, (0, 1, 4)) == (1, 0)
    assert cycle_shift(dual, (0, 1, 5)) == (0, 1)
    canonical_shifts = root_shifts(dual)
    assert canonical_shifts == ((0, 0), (1, 0), (1, -1))
    assert differences(canonical_shifts) == -sp.eye(2)
    M = sp.Matrix(2, 2, sp.symbols("M00 M01 M10 M11"))
    zero((differences(canonical_shifts) * M).det() - M.det())

    orbit_text = read("OrigamiTorus/Winding/WindingOrbits.lean")
    representatives = {region: lean_list(orbit_text,
        rf"def representatives.*?\| \.type5, \.{region} =>\s*(\[.*?\])")
        for region in ("interior", "ray", "hexagonal")}
    assert {k: len(v) for k, v in representatives.items()} == {
        "interior": 2, "ray": 1, "hexagonal": 1}
    cases = [case for case in json.loads(read("research/type5_focus/cases.json"))
             if case["type"] == 5]
    assert len(cases) == 3
    assert [tuple(map(tuple, case["marking"])) for case in cases if not case["sharp"]] \
        == representatives["interior"]
    assert [tuple(map(tuple, case["marking"])) for case in cases if case["sharp"]] \
        == representatives["ray"]
    observed = []
    for case in cases:
        marking = sp.Matrix(case["marking"])
        assert marking.det() in (-1, 1)
        assert case["basis"] == [[0, 1, 4], [0, 1, 5]]
        archived = {tuple(row["edge"]): tuple(row["shift"]) for row in case["edge_shifts"]}
        assert set(archived) == edges
        for edge in edges:
            assert tuple(sp.Matrix([dual[edge]]) * marking) == archived[edge]
        K = directed(archived)
        shifts = root_shifts(K)
        assert len(set(shifts)) == 3
        assert differences(shifts).det() == marking.det()
        observed.append(shifts)
        if case["sharp"]:
            gauge = {i: K[1, i] for i in range(8)}
            gauged = {edge: tuple(value[j] + gauge[edge[0]][j] - gauge[edge[1]][j]
                                  for j in range(2)) for edge, value in K.items()}
            assert root_shifts(gauged) == ((1, 0), (0, 0), (1, -1))
    assert observed == [((0, 0), (-1, -1), (0, -1)),
                        ((0, 0), (-1, 0), (0, -1)),
                        ((0, 0), (-1, 0), (0, -1))]
    for region, reps in representatives.items():
        for marking in reps:
            MM = sp.Matrix(marking)
            transformed = tuple(tuple(sp.Matrix([v]) * MM) for v in canonical_shifts)
            assert len(set(transformed)) == 3
            assert differences(transformed).det() == MM.det() in (-1, 1)
    print("PASS: actual dual cocycle, every archived/hexagonal marking, and arbitrary-marking determinant")


def check_exposed_cap_bookkeeping():
    """Check the finite tables in the hand proof, not a sign-model search."""
    vertices = {0, 1, 3, 4, 5, 6}
    equator = {1, 3, 4, 5}
    octahedron = short | caps
    fs = lambda text: frozenset(map(int, text))
    table = {
        1: ('035 045 356 456', '034', [('345', 0), ('346', 5)]),
        4: ('013 035 136 356', '015', [('135', 0), ('156', 3)]),
        3: ('014 045 146 456', '156', [('145', 6), ('015', 4)]),
        5: ('013 014 136 146', '346', [('134', 6), ('034', 1)]),
    }
    curtains = [(0, 1, 3, 4), (0, 4, 5, 1),
                (3, 6, 1, 5), (5, 6, 4, 3)]
    for vertex, (initial, direct, steps) in table.items():
        excluded = {fs(f) for f in initial.split()}
        assert excluded == {f for f in octahedron if vertex not in f}
        direct = fs(direct)
        assert any(vertex in (a, b) and
                   direct == frozenset(({a, b} - {vertex}) | {p, q})
                   for a, b, p, q in curtains)
        excluded.add(direct)
        for target, apex in steps:
            target = fs(target)
            assert vertex not in target and apex not in target
            assert {frozenset(edge) | {apex}
                    for edge in combinations(target, 2)} <= excluded
            excluded.add(target)
        possible = {frozenset(t) for t in combinations(vertices - {vertex}, 3)} - excluded
        assert possible == {frozenset((0, 6, r)) for r in equator - {vertex}}
        for r, s in permutations(equator - {vertex}, 2):
            assert frozenset((0, r, s)) in excluded
            assert frozenset((6, r, s)) in excluded
    print('PASS: all exposed-cap triangle exclusions and pole-triangle fan transfers')

    def side_conditions(a, b):
        return ((a[3]-a[1])*(a[4]-a[1]) > 0
                and (a[5]-a[4])*(a[1]-a[4]) > 0
                and (b[1]-b[3])*(b[5]-b[3]) > 0
                and (b[4]-b[5])*(b[3]-b[5]) > 0)
    forced = {1: (5, 4), 4: (3, 1), 3: (4, 5), 5: (1, 3)}
    cases = Counter()
    for left, right in product(permutations(sorted(equator)), repeat=2):
        a = {v: k for k, v in enumerate(left)}
        b = {v: k for k, v in enumerate(right)}
        if not side_conditions(a, b) or left[0] != right[0]:
            continue
        interior = left[0]
        partner, target = forced[interior]
        assert a[partner] < a[target] and b[partner] < b[target]
        assert partner != interior and a[interior] < a[partner]
        cases[interior] += 1
    assert set(cases) == equator
    print('PASS: every angular-order implication in the four interior-vertex cases')

    def orientation(order, triple):
        positions = [order.index(v) for v in triple]
        inversions = sum(positions[i] > positions[j]
                         for i, j in combinations(range(3), 2))
        return (-1)**inversions
    def crosses(order, edge, other):
        a, b = (order.index(v) for v in edge)
        inside = lambda v: 0 < (order.index(v)-a) % 6 < (b-a) % 6
        return inside(other[0]) != inside(other[1])
    orders = set()
    for tail in permutations(sorted(vertices - {0})):
        order = (0,) + tail
        if order > (0,) + tuple(reversed(tail)):
            continue
        in_cap = [v in {0, 1, 4} for v in order]
        if sum(in_cap[i] != in_cap[(i+1) % 6] for i in range(6)) != 2:
            continue
        if not all(orientation(order, (a, b, p)) == orientation(order, (a, b, q))
                   for a, b, p, q in curtains):
            continue
        orders.add(order)
        assert all(crosses(order, (1, 4), edge) for edge in ((0, 3), (0, 5)))
        assert all(crosses(order, (3, 5), edge) for edge in ((6, 1), (6, 4)))
    assert orders == {(0, 1, 3, 6, 5, 4), (0, 1, 5, 6, 3, 4)}
    print('PASS: the two convex hexagon orders and both strict height-reversal endpoints')


check_leaf_geometry(HERE.parents[1])
check_exposed_cap_bookkeeping()
print("All checks passed. No localized cell is excluded by these identities or the geometric reduction.")
