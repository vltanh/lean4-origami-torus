#!/usr/bin/env python3
"""Exact metric exclusions from relative raw-bracket comparisons, y >= 8.

The five-sign obstruction checked here closes phase chambers 129 and 130
and also covers the already excluded chamber 131.  Its proof uses one
relative comparison and one affine cocycle identity; no LP result is
trusted.  All magnitudes refer to RAW affine brackets in one common
coordinate frame, before the query's individual positive rescalings.
"""

from fractions import Fraction as F
from itertools import combinations

QUADS = tuple(combinations(range(8), 4))
INDEX = {q: i for i, q in enumerate(QUADS)}
PATTERN = (((0, 1, 2, 3), 1), ((0, 1, 2, 7), -1),
           ((0, 1, 3, 7), 1), ((0, 2, 3, 7), 1), ((1, 2, 3, 7), -1))
COMPARISON_SYMMETRY = (3, 2, 1, 0, 7, 6, 5, 4)
TARGET_MODELS = {
    129: '+-++-+--++-++-+++++--++++++----+--+-++-++-----+--+--+--++-----+--+--++',
    130: '+-++-+--++-++-+++++--++++++----+--+-++-++-+---+--+--+--++-----+--+--++',
    131: '+-++-+--++-++-+++++--+++++++---+--+-++-++-----+--+--+--++-----+--+--++',
}


def sign(model, points):
    parity = (-1)**sum(points[i] > points[j] for i, j in combinations(range(4), 2))
    return parity * model[INDEX[tuple(sorted(points))]]


def phase_permutations(symmetries):
    return tuple(tuple(entry['permutation']) for entry in symmetries if entry['phase_preserving'])


def relative_comparisons(model, symmetries):
    """All phase images of the proved bound L <= 8*t*R.

    A row's left pair consists of opposite weak signs on a same-cap
    triangle against the ends of one short edge in the other cap.  The
    right pair is the corresponding pair of raw two-cap brackets.
    This routine imposes no genericity on the actual minors.
    """
    result = {}
    for permutation in phase_permutations(symmetries):
        for i, j in combinations((1, 4, 5), 2):
            first = tuple(permutation[k] for k in (0, i, j, 2))
            second = tuple(permutation[k] for k in (0, i, j, 3))
            if sign(model, first) == sign(model, second):
                continue
            left = tuple(sorted((tuple(sorted(first)), tuple(sorted(second)))))
            right = tuple(sorted(tuple(sorted(permutation[k] for k in (0, 2, 3, v)))
                                 for v in (i, j)))
            result.setdefault((left, right), {
                'left': left, 'right': right, 'permutation': permutation,
                'cap_pair': (i, j), 'coefficient': '8/y^2',
            })
    return tuple(result[key] for key in sorted(result))


def verify(model, symmetries):
    """Return a minimal five-sign certificate, or None if not covered."""
    assert len(model) == 70 and all(value in (-1, 1) for value in model)
    group = phase_permutations(symmetries)
    assert len(group) == 16 and COMPARISON_SYMMETRY in group
    for permutation in group:
        image = lambda q: tuple(permutation[i] for i in q)
        orientation = sign(model, image((0, 1, 2, 3)))
        if not all(orientation * sign(model, image(q)) == value for q, value in PATTERN):
            continue
        # In these labels the necessary raw-bracket comparison is
        # B0237+B1237 <= (1/2)*(B0123+B0137), since 8/y^2<=1/8<1/2.
        # The exact five-point cocycle is
        # -B1237-B0237+B0137+B0127+B0123=0.
        # Adding gives (B0123+B0137)/2+B0127<=0, impossible because
        # B0123 is a nonzero K4 bracket and every B is nonnegative.
        normalized = tuple(orientation * sign(model, image(q)) for q in QUADS)
        rows = relative_comparisons(normalized, symmetries)
        left = ((0, 2, 3, 7), (1, 2, 3, 7))
        right = ((0, 1, 2, 3), (0, 1, 3, 7))
        assert any(row['left'] == left and row['right'] == right for row in rows)
        coefficients = {q: F(0) for q in QUADS}
        for q in left:
            coefficients[q] += 1
        for q in right:
            coefficients[q] -= F(1, 2)
        support = (0, 1, 2, 3, 7)
        for i in range(5):
            q = support[:i] + support[i + 1:]
            coefficients[q] += (-1)**i * normalized[INDEX[q]]
        assert {q: v for q, v in coefficients.items() if v} == {
            (0, 1, 2, 3): F(1, 2), (0, 1, 2, 7): F(1), (0, 1, 3, 7): F(1, 2),
        }
        return {'permutation': permutation, 'orientation': orientation,
                'valid_for': 'y>=8', 'raw_left': left, 'raw_right': right,
                'coefficient': '1/2', 'cocycle': support,
                'strict_clique': (0, 1, 2, 3)}
    return None


def symbolic_checks():
    """Check the raw determinant identities and all uniform constants."""
    import sympy as s

    t, x2, x3, g2, g3 = s.symbols('t x2 x3 g2 g3')
    ui, zi, wi, uj, zj, wj = s.symbols('ui zi wi uj zj wj')
    origin = s.zeros(3, 1)
    point2 = s.Matrix([x2, 0, 1 - 2*t*g2])
    point3 = s.Matrix([x3, 0, 1 - 2*t*g3])
    pointi = s.Matrix([ui, zi, -2*t*wi])
    pointj = s.Matrix([uj, zj, -2*t*wj])
    determinant = lambda a, b, c: s.Matrix.hstack(a, b, c).det()
    h, dg = x2 - x3, g3 - g2
    actual = determinant(pointi, pointj, point3) - determinant(pointi, pointj, point2)
    expected = -2*t*(h*(wi*zj - zi*wj) + dg*(ui*zj - zi*uj))
    assert s.expand(actual - expected) == 0
    anchor = x2*(1 - 2*t*g3) - x3*(1 - 2*t*g2)
    assert s.expand(anchor - ((1 - 2*t*g2)*h - 2*t*x2*dg)) == 0
    assert s.expand(determinant(point2, point3, pointi) + anchor*zi) == 0
    assert s.expand(determinant(point2, point3, pointj) + anchor*zj) == 0
    # Generic five-point affine cocycle.  Translation sets its first
    # point to zero without changing any bracket.
    points = [origin] + [s.Matrix(s.symbols(f'v{i}x v{i}y v{i}z')) for i in range(1, 5)]
    total = 0
    for i in range(5):
        kept = points[:i] + points[i + 1:]
        a, *rest = kept
        total += (-1)**i * determinant(*(p - a for p in rest))
    assert s.expand(total) == 0
    bound = F(1, 64)
    beta = F(1, 2) + bound
    assert 1 - 3*bound/4 - bound*beta > F(31, 32)
    assert F(32, 31) * (7 + F(33, 32)*beta) < 8
    assert 8*bound <= F(1, 8) < F(1, 2)


def main():
    import solver_chambers as compiler

    symbolic_checks()
    symmetries = compiler.marked_symmetries()
    for chamber, key in TARGET_MODELS.items():
        model = tuple(1 if value == '+' else -1 for value in key)
        certificate = verify(model, symmetries)
        assert certificate is not None
        print(f'PASS chamber {chamber}: one relative comparison plus one affine cocycle; y>=8')
    print('Two additional complete weak metric chambers excluded; chamber 131 overlaps the final-polynomial proof.')


if __name__ == '__main__':
    if not __debug__:
        raise RuntimeError('run with assertions enabled')
    main()
