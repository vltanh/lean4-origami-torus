#!/usr/bin/env python3
"""Add the degeneracy-complete projected-area union to the full ray-3 system.

Usage: python projected_metric.py OUTPUT [Y [TIMEOUT_MS]]

For y >= 8, the conditional cap-order theorem gives at least one of 24
physical transverse determinants of magnitude <= 400/y^2.  All lengths
in the underlying Gram system are scaled by 1/y^2.  If Q is the 3-by-3
Gram determinant of (r2-r0, a, b) in that system, the exact equivalent
polynomial inequality is y^8 Q <= 160000 D02.  D02 is strictly positive.

This is a necessary union, including its zero-determinant boundary.  It
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
    text += "\n".join(extra) + "\n(check-sat)\n"
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
