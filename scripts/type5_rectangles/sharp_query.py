"""Emit the sharp-ray existence question in the first-order theory of real fields.

Use a rational squared period height for a fixed torus, or "all" for the
universality statement. Requires the optional Python package z3-solver.
"""

import argparse
from fractions import Fraction
from itertools import combinations

from .chart import Complex, add, cross, scale, subtract, volume
from .reduced import CYCLES


def homogeneous_bracket(columns, q):
    a, b, c, d = (columns[i] for i in q)
    return (a[0]*volume(b[1:], c[1:], d[1:]) - b[0]*volume(a[1:], c[1:], d[1:])
            + c[0]*volume(a[1:], b[1:], d[1:]) - d[0]*volume(a[1:], b[1:], c[1:]))


def generic_separation(complex_, z, columns):
    """Separate every disjoint edge and face using positive homogeneous denominators."""
    tests = []
    brackets = {}
    # A disjoint edge and face contain at most two leaves; the five
    # determinants involving all three leaves never enter separation.
    needed = {q for e, face in complex_.disjoint for q in combinations(sorted((*e, *face)), 4)}
    for q in sorted(needed):
        value = homogeneous_bracket(columns, q)
        tests.append(value != 0)
        brackets[q] = value > 0
    for e, face in complex_.disjoint:
        labels = tuple(sorted((*e, *face)))
        circuit = []
        for i, v in enumerate(labels):
            sign = brackets[labels[:i]+labels[i+1:]]
            circuit.append(sign if (i % 2 == 0) == (v in e) else z.Not(sign))
        tests.extend([z.Or(circuit), z.Or([z.Not(sign) for sign in circuit])])
    return tests, brackets


def constraints(complex_, z, x, y_squared):
    """Return twelve real variables and the constraints on their values."""
    p = {1: (0, 0)}
    for i in (2, 3, 4, 5):
        p[i] = tuple(z.Reals(f"x{i} y{i}"))
    product = z.Real("g")
    leaf_x = {j: z.Real(f"t{j}") for j in CYCLES}
    variables = [v for i in (2, 3, 4, 5) for v in p[i]] + [product, *leaf_x.values()]

    # Physical (a, y*b) is stored as (a, b). D is the determinant of the
    # two anchor inner-product rows in these coordinates.
    def dot(u, v):
        return u[0]*v[0] + y_squared*u[1]*v[1]

    def squared(u):
        return dot(u, u)

    def period(i, j):
        m, n = complex_.shift[i, j]
        return m+n*x, n

    def edge(i, j):
        return add(subtract(p[j], p[i]), period(i, j))

    anchor2, anchor5 = p[2], p[5]
    det = y_squared*cross(anchor2, anchor5)
    det_sq = det*det
    tests = [det < 0]  # Positive orientation of the face 152.

    def rhs(i, j, v):
        s = subtract(p[i], period(i, j))
        return dot(s, v) + (squared(p[i])-squared(s))/2

    def project(j, v):
        # Numerator of the horizontal projection, with common denominator D.
        h, k = rhs(2, j, v), rhs(5, j, v)
        return y_squared*(anchor5[1]*h-anchor2[1]*k), anchor2[0]*k-anchor5[0]*h

    horizontal = {i: scale(det, p[i]) for i in (1, 2, 5)}
    horizontal.update({i: project(i, p[i]) for i in (3, 4)})
    height_sq = {i: det_sq*squared(p[i])-squared(horizontal[i]) for i in (3, 4)}
    h3, h4 = height_sq[3], height_sq[4]
    tests.extend([h3 > 0, h4 > 0, product*product == h3*h4])

    # Spatial horizontal coordinates are scaled by D, and the physical
    # vertical coordinate is scaled by D² times the signed root-3 height.
    height = {1: 0, 2: 0, 5: 0, 3: h3, 4: product}
    columns = {i: (1, *horizontal[i], height[i]) for i in p}
    for j, cycle in CYCLES.items():
        lifted = {i: subtract(p[i], period(i, j)) for i in p}
        for i, k in zip(cycle, cycle[1:]+cycle[:1], strict=True):
            intrinsic_sq = squared(subtract(lifted[i], lifted[k]))
            if (i, k) == (3, 4):
                spatial_sq = squared(subtract(horizontal[i], horizontal[k])) + h3+h4-2*product
                tests.append(det_sq*intrinsic_sq > spatial_sq)
            else:
                tests.append(intrinsic_sq > squared(edge(i, k)))
        boundary = [(f[(f.index(j)+1) % 3], f[(f.index(j)+2) % 3]) for f in complex_.faces if j in f]
        tests.append(sum(cross(lifted[i], lifted[k]) for i, k in boundary) > 0)

        def linear_height(i, v):
            return det_sq*rhs(i, j, v) - dot(horizontal[i], project(j, v))

        def axis(v):
            return h3*linear_height(4, v) - product*linear_height(3, v)

        origin, ex, ey = (0, 0), (1, 0), (0, 1)
        c = axis(origin)
        a, b = axis(ex)-c, axis(ey)-c
        tests.append(b != 0)
        # v/b is the intrinsic leaf position. The last null equation is
        # quadratic in t, without any division by a variable.
        t = leaf_x[j]
        v = (b*t, -a*t-c)

        def evaluate_homogeneous(fn):
            intercept = fn(origin)
            return b*intercept+(fn(ex)-intercept)*v[0]+(fn(ey)-intercept)*v[1]

        nx, ny = (evaluate_homogeneous(lambda u: project(j, u)[k]) for k in range(2))
        nz = evaluate_homogeneous(lambda u: linear_height(3, u))
        tests.append(h3*(squared((nx, ny))-det_sq*squared(v)) + nz*nz == 0)
        columns[j] = (b*b, b*nx, b*ny, b*nz)

    # At the hexagon face 125 supports the whole embedding. The last
    # homogeneous coordinate of root 3 is positive in this normalization.
    tests.append(z.Implies(4*y_squared == 3,
                           z.And(product > 0, *(columns[j][-1] > 0 for j in CYCLES))))

    separate, brackets = generic_separation(complex_, z, columns)
    tests.extend(separate)
    # A hexagonal symmetry brings one supporting winding triangle to 123
    # or 126. In general position all five side tests are strict.
    def supports(k):
        signs = []
        for j in range(8):
            if j in (1, 2, k):
                continue
            labels = (1, 2, k, j)
            sign = brackets[tuple(sorted(labels))]
            signs.append(z.Not(sign) if sum(a > b for a, b in combinations(labels, 2)) % 2 else sign)
        return z.Or(z.And(signs), z.And([z.Not(sign) for sign in signs]))

    tests.append(z.Implies(4*y_squared == 3, z.Or(supports(3), supports(6))))
    return variables, tests


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("height_squared", help='rational y² >= 3/4, or "all"')
    arg = parser.parse_args().height_squared
    try:
        import z3
    except ImportError:
        parser.exit(1, "This exporter requires the Python package z3-solver.\n")
    if arg == "all":
        y_squared = z3.Real("Y")
    else:
        try:
            y_squared = Fraction(arg)
        except (ValueError, ZeroDivisionError):
            parser.error("expected a rational squared height or all")
        if y_squared < Fraction(3, 4):
            parser.error("the reduced sharp ray starts at y² = 3/4")
        y_squared = z3.RealVal(y_squared)
    variables, tests = constraints(Complex(), z3, z3.RealVal("1/2"), y_squared)
    solver = z3.Solver()
    if arg == "all":
        feasible = z3.Exists(variables, z3.And(tests))
        solver.add(z3.ForAll([y_squared], z3.Implies(y_squared >= z3.RealVal("3/4"), feasible)))
    else:
        solver.add(z3.And(tests))
    print(solver.to_smt2(), end="")


if __name__ == "__main__":
    main()
