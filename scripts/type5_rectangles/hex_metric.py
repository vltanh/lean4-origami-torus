"""Export the intrinsic-coordinate feasibility tests for the hexagonal torus."""

import argparse
from itertools import combinations
import json
from pathlib import Path

from .chart import Complex, add, cross, scale, subtract, volume
from .sharp_query import homogeneous_bracket

ROOTS = (3, 4)
LEAVES = (0, 6, 7)
ANCHORS = (1, 2, 5)


def intrinsic_data(complex_, p):
    def edge(i, j):
        return add(subtract(p[j], p[i]), complex_.shift[i, j])

    squared = {(i, i): 0 for i in range(8)}
    for i, j in complex_.edges:
        x, y = edge(i, j)
        squared[i, j] = squared[j, i] = x*x+x*y+y*y

    faces = [cross(edge(i, j), edge(i, k)) for i, j, k in complex_.faces]
    return squared, faces


def spatial_data(squared):
    """Compute six Gram determinants and homogeneous spatial representatives."""
    # Twice the Gram entries of spatial vectors based at vertex 1.
    gram = {(i, j): squared[1, i]+squared[1, j]-d for (i, j), d in squared.items()}
    a, b, c = gram[2, 2], gram[2, 5], gram[5, 5]
    det = a*c-b*b
    horizontal = {i: (gram[2, i], gram[5, i]) for i in range(8)}

    def vertical(i, j):
        x, y = horizontal[i]
        u, v = horizontal[j]
        return det*gram[i, j] - x*(c*u-b*v) - y*(a*v-b*u)

    nonanchors = ROOTS + LEAVES
    diag = {i: vertical(i, i) for i in nonanchors}
    pair = {(i, j): vertical(i, j) for i in ROOTS for j in LEAVES}
    equations = []
    for i, j in pair:
        # Expand the fourth-order Gram determinant along the last row. This
        # avoids the common factor det in diag[i]*diag[j] - pair[i,j]^2.
        rows = [(gram[k, 2], gram[k, 5], gram[k, i]) for k in (2, 5, i, j)]
        col = [gram[k, j] for k in (2, 5, i, j)]
        equations.append(sum((-1)**(3+k)*col[k]*volume(*(rows[:k]+rows[k+1:])) for k in range(4)))

    height = {1: 0, 2: 0, 5: 0, 3: diag[3], **{j: pair[3, j] for j in LEAVES}}
    columns = {i: (1, *horizontal[i], h) for i, h in height.items()}
    columns[4] = (pair[3, 0], *scale(pair[3, 0], horizontal[4]), diag[3]*pair[4, 0])
    return [det, *diag.values(), *pair.values()], equations, columns


def mixed_volumes(complex_, squared):
    """Products of each clique volume with the volume of an anchor tetrahedron."""
    products = {}
    for q in combinations(range(8), 4):
        if not all(e in complex_.edges for e in combinations(q, 2)):
            continue
        t = (*ANCHORS, next(i for i in q if i not in ANCHORS))
        rows = [tuple(squared[i, t[0]] + squared[q[0], j] - squared[i, j] - squared[q[0], t[0]]
                      for j in t[1:]) for i in q[1:]]
        products[q] = volume(*rows)
    assert len(products) == 23
    return products


def constraints(complex_, p, z, classes):
    squared, faces = intrinsic_data(complex_, p)
    positive, equations, columns = spatial_data(squared)
    tests = [v > 0 for v in positive+faces] + [v == 0 for v in equations]
    for i, j in sorted(complex_.edges):
        x, y = add(subtract(p[j], p[i]), complex_.shift[i, j])
        for projection in (2*x+y, x+2*y, y-x):
            tests.extend([projection > -1, projection < 1])

    mixed = mixed_volumes(complex_, squared)
    # At 1256 the two volumes coincide, so their product is positive.
    # Its bit fixes the absolute sign convention in each canonical word.
    reference = list(mixed).index((1, 2, 5, 6))
    quartets = list(combinations(range(8), 4))
    data = json.loads(Path(__file__).with_name("hex_angle_certificates.json").read_text())
    additional = {code: data["separation"][format(code, "x")] for code in classes}
    brackets = {i: homogeneous_bracket(columns, quartets[i-1])
                for i in {abs(k) for row in additional.values() for k in row}}
    alternatives = []
    for code in classes:
        signs = [(v > 0 if ((code >> k) & 1) == ((code >> reference) & 1) else v < 0)
                 for k, v in enumerate(mixed.values())]
        # With horizontal Gram coordinates, the oriented 1256 determinant
        # is positive. The stored extra signs use the first clique as reference.
        for k in additional[code]:
            positive = (k > 0) == bool(code & (1 << reference))
            v = brackets[abs(k)]
            signs.append(v > 0 if positive else v < 0)
        alternatives.append(z.And(signs))
    tests.append(z.Or(alternatives))
    return tests


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    codes = json.loads(Path(__file__).with_name("hex_angle_certificates.json").read_text())["clique_classes"]
    parser.add_argument("clique_class", choices=["all", *codes], default="all", nargs="?")
    choice = parser.parse_args().clique_class
    try:
        import z3
    except ImportError:
        parser.exit(1, "This exporter requires the Python package z3-solver.\n")
    p = {i: tuple(z3.Reals(f"x{i} y{i}")) if i != 1 else (0, 0) for i in range(8)}
    classes = [int(code, 16) for code in (codes if choice == "all" else [choice])]
    solver = z3.Solver()
    solver.add(z3.And(constraints(Complex(), p, z3, classes)))
    print(solver.to_smt2(), end="")


if __name__ == "__main__":
    main()
