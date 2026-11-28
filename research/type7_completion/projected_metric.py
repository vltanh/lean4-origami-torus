#!/usr/bin/env python3
"""Add the degeneracy-complete projected-area union to the full ray-3 system.

Usage: python projected_metric.py OUTPUT [Y [TIMEOUT_MS]]

For y >= 8, the conditional cap-order theorem gives at least one of 24
physical transverse determinants of magnitude <= 400/y^2.  All lengths
in the underlying Gram system are scaled by 1/y^2.  If Q is the 3-by-3
Gram determinant of (r2-r0, a, b) in that system, the exact equivalent
polynomial inequality is y^8 Q <= 160000 D02.  D02 is strictly positive.

The relative cap theorem additionally imposes negative short-edge
horizontal displacements, |y^2*V_e|<(1/2+1/y^2)*(-X_e), and the stronger union
y^8 Q <= 1296 D02 X_e^2 X_f^2.  Here e,f are consecutive cap edges or
one edge from each cap.  Its physical bound is 36*h_e*h_f/y^2, where
h_e=-X_e>0; it controls directions even when cap edges shrink.

These are necessary unions, including their zero-determinant boundaries.  They
does not exclude ray 3 and does not discharge the geometric premises of
the cap-order theorem.  An optional solver result is research evidence,
not an independently checked proof.  Write generated queries to scratch.
"""

import importlib.util
import json
import sys
from itertools import combinations
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location(
    "type7_linked_metric", ROOT / "type7_closure" / "linked_metric.py"
)
linked = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(linked)
m = linked.m

CAP_A = (0, 1, 4, 5)
CAP_B = (2, 3, 6, 7)
AXIS = (0, 2)


def ring_edges(cap):
    return tuple(zip(cap, cap[1:] + cap[:1]))


def determinant_pairs():
    """The eight cap triangles and sixteen pairs of cyclic ring edges."""
    rows = []
    for cap in (CAP_A, CAP_B):
        for a, b, c in combinations(cap, 3):
            rows.append((f"cap_{a}{b}{c}", (a, b), (a, c)))
    for a in ring_edges(CAP_A):
        for b in ring_edges(CAP_B):
            rows.append((f"cross_{a[0]}{a[1]}_{b[0]}{b[1]}", a, b))
    assert len(rows) == 24
    assert len({row[0] for row in rows}) == 24
    return tuple(rows)


def relative_comparisons():
    """The same 24 areas, using consecutive edges for the cap triangles."""
    rows = []
    for cap in (CAP_A, CAP_B):
        for triple in combinations(cap, 3):
            i = next(i for i in range(4)
                     if {cap[(i + j) % 4] for j in range(3)} == set(triple))
            a, b, c = (cap[(i + j) % 4] for j in range(3))
            rows.append(("cap_" + "".join(map(str, triple)), (a, b), (b, c)))
    rows += list(determinant_pairs()[8:])
    assert [r[0] for r in rows] == [r[0] for r in determinant_pairs()]
    return tuple(rows)


def directed_symbol(prefix, edge):
    i, j = edge
    value = f"{prefix}{min(i, j)}{max(i, j)}"
    return value if i < j else m.neg(value)


def relative_edge_constraints(y):
    """Eight negative horizontal steps with a uniform relative slope."""
    lines = []
    for edge in ring_edges(CAP_A) + ring_edges(CAP_B):
        x = directed_symbol("X", edge)
        gamma = m.mul(str(y * y), directed_symbol("V", edge))
        bound = m.mul(m.rat(-m.F(1, 2) - m.F(1, y * y)), x)
        lines += [m.op("assert", m.op("<", x, "0")),
                  m.op("assert", m.op("<", gamma, bound)),
                  m.op("assert", m.op(">", gamma, m.neg(bound)))]
    return lines


def relative_projected_union(y):
    tests = []
    for name, a, b in relative_comparisons():
        x, z = directed_symbol("X", a), directed_symbol("X", b)
        tests.append(m.op("<=", m.mul(str(y ** 8), "projected_gram_" + name),
                          m.mul("1296", "D02", x, x, z, z)))
    return m.op("assert", m.any_(tests))


def vertex_inner(i, j):
    # The origin is vertex 0; all remaining Gij are defined by the base
    # generator, including the diagonal entries and nonedge distances.
    return "0" if i == 0 or j == 0 else f"G{min(i, j)}{max(i, j)}"


def edge_inner(a, b):
    i, j = a
    k, l = b
    return m.sub(
        m.add(vertex_inner(j, l), vertex_inner(i, k)),
        m.add(vertex_inner(j, k), vertex_inner(i, l)),
    )


def projected_constraints(y):
    """Return declarations/assertions and metadata, without a solver call."""
    if not isinstance(y, int) or isinstance(y, bool) or y < 8:
        raise ValueError("the finite cap-order bound requires integer y >= 8")
    lines = []
    tests = []
    for name, a, b in determinant_pairs():
        vectors = (AXIS, a, b)
        gram = [[edge_inner(u, v) for v in vectors] for u in vectors]
        symbol = "projected_gram_" + name
        lines.append(f"(define-fun {symbol} () Real {m.det(gram)})")
        # PSD follows from the positive anchor Gram matrix and the exact
        # completion equations.  Recording it makes the squared-area
        # interpretation explicit without excluding zero-area cases.
        lines.append(m.op("assert", m.op(">=", symbol, "0")))
        tests.append(m.op("<=", m.mul(str(y ** 8), symbol),
                          m.mul("160000", "D02")))
    lines.append(m.op("assert", m.any_(tests)))
    return lines, {
        "projected_determinants": len(tests),
        "projected_triangle_terms": 8,
        "projected_cross_terms": 16,
        "projected_axis": list(AXIS),
        "physical_area_bound": str(m.F(400, y * y)),
        "scaled_gram_coefficient": str(y ** 8),
        "zero_projected_determinants_retained": True,
    }


def generate(y=10 ** 6):
    extra, metadata = projected_constraints(y)
    text, base_metadata = linked.generate(y)
    assert text.endswith("(check-sat)\n")
    text = text.removesuffix("(check-sat)\n")
    text += "\n".join(extra + relative_edge_constraints(y)
                      + [relative_projected_union(y)]) + "\n(check-sat)\n"
    metadata |= {"relative_cap_edges": 8,
                 "relative_slope_bound": "(1/2+1/y^2)*h_e",
                 "relative_area_bound": "36*h_e*h_f/y^2"}
    return text, base_metadata | metadata


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
