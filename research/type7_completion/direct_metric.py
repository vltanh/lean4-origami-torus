#!/usr/bin/env python3
"""Full ray-3 query in a cap-adapted direct-coordinate chart, y >= 8.

Usage: python direct_metric.py OUTPUT [Y [TIMEOUT_MS]]

The 27 real unknowns are 14 intrinsic coordinates, 11 transverse
coordinates, and two rescaled cap heights.  The other four heights are
eliminated exactly by subtracting the two anchor-distance equations.
Metric equations have degree
at most four.  The full generic-completion/linking/circuit formula is
reused verbatim from linked_metric.py, replacing only its affine minors
by minors in the direct chart.  Vanishing minors remain permitted when
the original formula permits them.

Let t=1/y^2, c0=X02^2+2*Y0_02*gamma2+t*gamma2^2, d=1+4*t*c0>0,
and L=sqrt(d/(4*t)).  The physical points are
  r_i=(P_i, L*c_i+rho_i/(2*L)), c_i=I[i in {2,3,6,7}].
The incidence coordinates are (P_i,d*c_i+2*t*rho_i), obtained by a
positive axial scaling.  The chart sets r0=0 and r2=(0,0,L), fixes the
remaining rotation by P1=(px1,0), px1>0, and uses reflection to put
py3<0.  K4 nondegeneracy guarantees this chart covers every permitted
placement; no cap area or edge length is assumed bounded away from zero.

This is an exact alternative encoding, not a marking exclusion.  Its
necessity inherits the geometric premises of the existing full query
and cap-order theorem.  Generated queries belong in scratch.
"""

import json
import re
import sys
from fractions import Fraction as F
from itertools import combinations
from pathlib import Path

import projected_metric as p

m = p.m
ROOT = p.ROOT
V = tuple(range(8))
OTHER = (1, 3, 4, 5, 6, 7)
ELIMINATED_HEIGHTS = (1, 3, 5, 7)


def load_data():
    case = next(c for c in json.loads(
        (ROOT / "linking_checkpoint/cases.json").read_text())
        if c["file"] == "t7_ray_3.smt2")
    faces = [tuple(map(int, f)) for f in json.loads(
        (ROOT / "linking_checkpoint/lutz_faces.json").read_text())["7"].split()]
    shifts = {tuple(e["edge"]): tuple(e["shift"]) for e in case["edge_shifts"]}
    shifts.update({(j, i): (-a, -b) for (i, j), (a, b) in list(shifts.items())})
    edges = sorted({tuple(sorted(e)) for f in faces for e in combinations(f, 2)})
    xb, yb = [F(0)] * 8, [F(0)] * 8
    for ring in ((0, 2, 4, 6), (1, 3, 5, 7)):
        for i, j in zip(ring, ring[1:]):
            a, b = shifts[i, j]
            xb[j], yb[j] = xb[i] - a - F(b, 2), yb[i] - F(1, 2) - b
    kx = {(i, j): xb[j] - xb[i] + a + F(b, 2)
          for (i, j), (a, b) in shifts.items()}
    ky = {(i, j): yb[j] - yb[i] + b for (i, j), (_, b) in shifts.items()}
    for i, j in edges:
        ell = int(j in p.CAP_B) - int(i in p.CAP_B)
        assert ky[i, j] ** 2 == F(ell * ell, 4)
    assert ky[0, 2] == -F(1, 2)
    return faces, shifts, edges, xb, yb, kx, ky


def generate(y=10 ** 6):
    if not isinstance(y, int) or isinstance(y, bool) or y < 8:
        raise ValueError("the direct cap chart requires integer y >= 8")
    t, w = F(1, y * y), y * y
    faces, shifts, edges, xb, yb, kx, ky = load_data()
    lines = ["(set-logic QF_NRA)"]
    nreals = 0

    def declare(name):
        nonlocal nreals
        nreals += 1
        lines.append(f"(declare-fun {name} () Real)")
        return name

    def define(name, expr):
        lines.append(f"(define-fun {name} () Real {expr})")
        return name

    def require(expr):
        lines.append(m.op("assert", expr))

    def bounded(expr, bound, strict=True):
        return m.all_([m.op("<" if strict else "<=", expr, bound),
                       m.op(">" if strict else ">=", expr, m.neg(bound))])

    xx = ["0"] + [declare(f"x{i}") for i in V[1:]]
    gamma = ["0"] + [declare(f"gamma{i}") for i in V[1:]]
    transverse = {0: ("0", "0"), 2: ("0", "0")}
    for i in OTHER:
        transverse[i] = (declare(f"px{i}"), "0" if i == 1 else declare(f"py{i}"))
    rho = {0: "0", 2: "0"} | {i: declare(f"rho{i}") for i in (4, 6)}
    assert nreals == 27
    X, Y = {}, {}
    for i, j in edges:
        X[i, j] = define(f"X{i}{j}", m.add(m.sub(xx[j], xx[i]), m.rat(kx[i, j])))
        Y[i, j] = define(f"V{i}{j}", m.add(m.rat(ky[i, j]),
                                         m.mul(m.rat(t), m.sub(gamma[j], gamma[i]))))
        X[j, i], Y[j, i] = m.neg(X[i, j]), m.neg(Y[i, j])
    c0 = define("c0", m.add(m.mul(X[0, 2], X[0, 2]),
                            m.mul(m.rat(2 * ky[0, 2]), gamma[2]),
                            m.mul(m.rat(t), gamma[2], gamma[2])))
    den = define("den", m.add("1", m.mul(m.rat(4 * t), c0)))
    for i in ELIMINATED_HEIGHTS:
        # |ri-r0|^2-|ri-r2|^2=(2*c_i-1)*L^2+rho_i.
        # Both distances are prescribed edges.  Their common y^2/4
        # contributions cancel, leaving this quadratic polynomial.
        rho[i] = define(f"rho{i}", m.sub(m.add(
            m.sub(m.mul(X[0, i], X[0, i]), m.mul(X[2, i], X[2, i])),
            m.mul(m.rat(2 * ky[0, i]), gamma[i]),
            m.neg(m.mul(m.rat(2 * ky[2, i]), m.sub(gamma[i], gamma[2]))),
            m.mul(m.rat(t), m.sub(m.mul("2", gamma[i], gamma[2]),
                                  m.mul(gamma[2], gamma[2])))),
            m.mul(str(2 * int(i in p.CAP_B) - 1), c0)))
    require(m.op(">", den, "0"))
    require(m.op(">", transverse[1][0], "0"))
    require(m.op("<", transverse[3][1], "0"))
    # Uniform finite cap bounds, sharpened by relative_cap_bounds.md:
    # no nondegeneracy assumption about a limiting cap is used.
    require(bounded(c0, m.rat(F(41, 20))))
    for i in OTHER:
        require(m.op("<", m.add(*(m.mul(a, a) for a in transverse[i])),
                     m.rat(F(33, 64) ** 2)))
        require(bounded(rho[i], m.mul(m.rat(F(11, 4)), den)))

    def diffs(i, j):
        return [m.sub(transverse[j][k], transverse[i][k]) for k in (0, 1)]

    lines.extend(p.relative_edge_constraints(y))
    for i, j in p.ring_edges(p.CAP_A) + p.ring_edges(p.CAP_B):
        x = X[i, j]
        hsq = m.mul(x, x)
        dr = m.sub(rho[j], rho[i])
        require(m.op(">", m.add(*(m.mul(a, a) for a in diffs(i, j))),
                     m.mul(m.rat(F(9, 16)), hsq)))
        require(m.op("<", m.mul(dr, dr), m.mul("25", den, hsq)))

    for i, j in edges:
        x, v = X[i, j], Y[i, j]
        require(m.op(">", m.add(m.mul(m.rat(t), x, x), m.mul(v, v)), "0"))
        require(bounded(x, "(/ 1 2)"))
        for sign in (x, m.neg(x)):
            require(bounded(m.add(v, m.mul(m.rat(t / 2), sign)),
                            m.rat(F(1, 2) + t / 8)))
        ell = int(j in p.CAP_B) - int(i in p.CAP_B)
        if ell == 0:
            require(bounded(v, m.rat(7 * t / 4)))
        else:
            limit = m.rat(F(1, 2) - 7 * t / 4)
            require(m.any_([m.op(">=", v, limit), m.op("<=", v, m.neg(limit))]))
        if (i, j) in ((0, 2), (1, 2), (2, 5), (0, 3), (0, 7)):
            # Edge 02 defines L; the four other equations are equivalent
            # to the retained short anchor edges after eliminating rho.
            continue
        dg, dr = m.sub(gamma[j], gamma[i]), m.sub(rho[j], rho[i])
        finite_difference = m.sub(
            m.add(*(m.mul(a, a) for a in diffs(i, j)),
                  m.mul(str(ell), dr), m.mul(str(ell * ell), c0)),
            m.add(m.mul(x, x), m.mul(m.rat(2 * ky[i, j]), dg),
                  m.mul(m.rat(t), dg, dg)),
        )
        residual = define(f"metric{i}{j}", m.add(m.mul(den, finite_difference),
                                                m.mul(m.rat(t), dr, dr)))
        require(m.op("=", residual, "0"))
    areas = [define(f"area{k}", m.sub(m.mul(X[a, b], Y[a, c]),
                                      m.mul(X[a, c], Y[a, b])))
             for k, (a, b, c) in enumerate(faces)]
    require(m.any_([
        m.all_([m.op(">", a, "0") for a in areas] + [m.op("=", m.add(*areas), "2")]),
        m.all_([m.op("<", a, "0") for a in areas] + [m.op("=", m.add(*areas), "(- 2)")]),
    ]))
    for i, j in combinations(V, 2):
        if (i, j) in edges:
            continue
        assert (i in p.CAP_B) == (j in p.CAP_B)
        dr = m.sub(rho[j], rho[i])
        numerator = define(f"nonedge{i}{j}", m.add(
            m.mul(den, m.add(*(m.mul(a, a) for a in diffs(i, j)))),
            m.mul(m.rat(t), dr, dr)))
        require(m.op(">", numerator, "0"))
        for a in range(-4, 5):
            for b in range(-3, 4):
                u = m.add(m.sub(xx[j], xx[i]), m.rat(xb[j] - xb[i] + a + F(b, 2)))
                v = m.add(m.rat(yb[j] - yb[i] + b),
                          m.mul(m.rat(t), m.sub(gamma[j], gamma[i])))
                require(m.op("<=", numerator,
                             m.mul(den, m.add(m.mul(u, u), m.mul(str(w), v, v)))))

    def minor(points, axes):
        # Dividing an all-one-cap minor containing the axial coordinate
        # by positive 2*t preserves every sign and zero test.  It avoids
        # coefficients of order 10^-12 without assuming it is nonzero.
        same_cap = len({i in p.CAP_B for i in points}) == 1
        coords = {
            i: (*transverse[i], rho[i] if same_cap else
                m.add(m.mul(str(int(i in p.CAP_B)), den), m.mul(m.rat(2 * t), rho[i])))
            for i in points
        }
        origin, *rest = points
        return m.det([[m.sub(coords[i][k], coords[origin][k]) for k in axes] for i in rest])

    for q in combinations(V, 4):
        if all(e in edges for e in combinations(q, 2)):
            value = define("m" + "".join(map(str, q)), minor(q, (0, 1, 2)))
            require(m.op("distinct", value, "0"))
    full, metadata = p.linked.generate(y)
    suffix = full[full.index("(declare-fun b1 () Bool)"):].splitlines()
    assert suffix[-1] == "(check-sat)"
    nminors = 0
    for line in suffix[:-1]:
        match = re.fullmatch(r"\(define-fun (a([0-7]+)c([012]+)) \(\) Real .*\)", line)
        if match:
            name, points, axes = match.groups()
            define(name, minor(tuple(map(int, points)), tuple(map(int, axes))))
            nminors += 1
        else:
            assert not re.search(r"\bG[1-7][1-7]\b", line)
            lines.append(line)
    assert nminors > 0
    small = []
    for name, (i, j), (k, l) in p.determinant_pairs():
        a, b = diffs(i, j), diffs(k, l)
        value = define("projected_area_" + name,
                       m.sub(m.mul(a[0], b[1]), m.mul(a[1], b[0])))
        small.append(bounded(value, m.rat(400 * t), strict=False))
    require(m.any_(small))
    relative_small = []
    for name, a, b in p.relative_comparisons():
        bound = m.mul(m.rat(36 * t), X[a], X[b])
        relative_small.append(bounded("projected_area_" + name, bound, strict=False))
    require(m.any_(relative_small))
    lines.append("(check-sat)")
    metadata |= {
        "real_variables": nreals,
        "metric_equations": 19,
        "metric_degree_bound": 4,
        "eliminated_cap_heights": list(ELIMINATED_HEIGHTS),
        "incidence_minor_definitions": nminors,
        "projected_determinants": len(small),
        "physical_area_bound": str(400 * t),
        "chart": "direct transverse coordinates and rescaled cap heights",
        "zero_projected_determinants_retained": True,
        "relative_cap_edges": 8,
        "relative_slope_bound": "(1/2+1/y^2)*h_e",
        "relative_area_bound": "36*h_e*h_f/y^2",
    }
    return "\n".join(lines) + "\n", metadata


if __name__ == "__main__":
    if not 2 <= len(sys.argv) <= 4:
        raise SystemExit(__doc__)
    y = int(sys.argv[2]) if len(sys.argv) > 2 else 10 ** 6
    text, metadata = generate(y)
    Path(sys.argv[1]).write_text(text)
    print(json.dumps(metadata), flush=True)
    print("bytes", len(text), flush=True)
    if len(sys.argv) > 3:
        print("solver", m.solve(text, int(sys.argv[3])), flush=True)
