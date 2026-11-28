"""Exclude exact Type 5 embeddings near the planar base at every sharp modulus."""

from functools import cache
from itertools import combinations
import json
from pathlib import Path

from flint import fmpq_poly, fmpz_mat, fmpz_poly
import sympy as sp

from scripts.type5_planar_masks import EDGES, FACES, common_clauses, literal
from .chart import cross
from .separation import refute
from .sharp_opening import L, QUARTETS, SPATIAL, planar_base, strict_sign


def height_forms():
    """Integer polynomials in L-3, positively proportional to the volume rows."""
    _, r, _ = planar_base()
    rows = []
    for q in QUARTETS:
        row = [sp.S.Zero]*5
        for k, i in enumerate(q):
            if i in SPATIAL:
                a, b, c = [j for j in q if j != i]
                row[SPATIAL.index(i)] = sp.factor((-1)**(k+1)*cross(r[b]-r[a], r[c]-r[a]))
        den = sp.lcm([sp.denom(v) for v in row])
        den *= strict_sign(den, 3, sp.oo)
        polys = [sp.Poly(sp.cancel(v*den), L) for v in row]
        gcd = sp.gcd_list([p.as_expr() for p in polys]) or sp.S.One
        gcd *= strict_sign(gcd, 3, sp.oo)
        translated = [p.exquo(sp.Poly(gcd, L)).shift(3) for p in polys]
        scalar = sp.ilcm(*(c.q for p in translated for c in p.all_coeffs()))
        rows.append([fmpz_poly([int(c*scalar) for c in reversed(p.all_coeffs())]) for p in translated])
    return rows


def coefficient_sign(p):
    """A strict sign on [0,infinity) from the monomial coefficients."""
    if p and p[0] > 0 and min(p.coeffs()) >= 0:
        return 1
    if p and p[0] < 0 and max(p.coeffs()) <= 0:
        return -1
    return 0


def check_conflicts(rows, conflicts):
    degrees = [max(p.degree() for p in row) for row in rows]
    assert len(rows) == 70 and max(degrees) <= 2
    bound = 5*max(degrees)
    samples = [[[p(j) for p in row] for row in rows] for j in range(bound+1)]
    newton = [fmpq_poly([1])]
    for j in range(1, bound+1):
        newton.append(newton[-1]*fmpq_poly([1-j, 1])/j)

    @cache
    def minor(indices):
        # The degree is at most the sum of the five row degrees. Interpolate
        # from that many plus one integer determinants by finite differences.
        degree = max(0, sum(degrees[i] for i in indices))
        values = [fmpz_mat([samples[j][i] for i in indices]).det() for j in range(degree+1)]
        result = fmpq_poly()
        for basis in newton[:degree+1]:
            result += basis*values[0]
            values = [b-a for a, b in zip(values, values[1:])]
        return result

    def reparametrize(p, left, right):
        if right is None:
            return p(fmpq_poly([left, 1]))
        u, v = fmpq_poly([left, right]), fmpq_poly([1, 1])
        return sum((c*u**i*v**(p.degree()-i) for i, c in enumerate(p.coeffs())), fmpq_poly())

    def opposite_signs(polys):
        return {-1, 1} <= {coefficient_sign(p) for p in polys}

    for conflict in conflicts:
        ids = sorted(abs(k)-1 for k in conflict)
        assert len(ids) == len(set(ids)) and 0 <= ids[0] <= ids[-1] < len(rows)
        orient = {abs(k)-1: 1 if k > 0 else -1 for k in conflict}
        assert any(coefficient_sign(minor(five)) for five in combinations(ids, 5))
        for four in combinations(ids, 4):
            # Each determinant is a scalar product with the same normal to
            # the four rows. Only the relative signs of these products matter.
            dots = []
            for i in ids:
                if i not in four:
                    p = minor(tuple(sorted((*four, i))))
                    if p:
                        dots.append(orient[i]*(-1)**sum(j > i for j in four)*p)
            if not dots or opposite_signs(dots):
                continue
            # A vanishing common factor makes all determinants zero at that
            # parameter. Full rank then implies the chosen four are dependent.
            gcd = dots[0]
            for p in dots[1:]:
                gcd = gcd.gcd(p)
            reduced = [p//gcd for p in dots]
            if not opposite_signs(reduced):
                for left, right in ((0, 1), (1, 4), (4, 12), (12, None)):
                    assert opposite_signs([reparametrize(p, left, right) for p in reduced])
            # Every independent four has rows on both sides of its hyperplane,
            # so its normal in either direction is outside the weak height cone.


def verify(complex_):
    forms = height_forms()
    assert all(literal(q) == i for i, q in enumerate(QUARTETS, 1))
    assert set(EDGES) == complex_.edges and set(FACES) == set(complex_.faces)
    clauses = [row for row in common_clauses() if len(row) > 1 and max(map(abs, row)) <= 70]
    clauses.append([literal((0, 1, 2, 5))])
    conflicts = json.loads(Path(__file__).with_name("height_conflicts.json").read_text())
    check_conflicts(forms, conflicts)
    clauses.extend([[-k for k in row] for row in conflicts])

    full = [-66, -43, -15, -9, 40]
    partial = [-11, 3, 49, 57]
    required = full + partial + [literal((0, 1, 5, 7))]
    refute(clauses + [[-k for k in required]], 70)

    def signed_matrix(literals, omit_seven=False):
        rows = []
        for k in literals:
            polys = forms[abs(k)-1]
            if omit_seven:
                assert 7 not in QUARTETS[abs(k)-1] and not polys[-1]
                polys = polys[:-1]
            row = [sum(int(c)*(L-3)**i for i, c in enumerate(p.coeffs())) for p in polys]
            rows.append(row if k > 0 else [-v for v in row])
        return sp.Matrix(rows)

    # Every nonzero h with A h >= 0 has h7 > 0, since A is invertible and
    # the last coordinate functional is a strictly positive sum of its rows.
    a = signed_matrix(full)
    assert strict_sign(a.det(), 3, sp.oo) != 0
    dual = a.T.inv()[:, -1]
    assert all(strict_sign(v, 3, sp.oo) > 0 for v in dual)

    # On vertices 0 through 6, B u >= 0 implies B u = 0 because its rows
    # have a positive dependence. Its kernel is a line with u0=0 and u4!=0.
    b = signed_matrix(partial, omit_seven=True)
    relation, = b.T.nullspace()
    assert all(strict_sign(v, 3, sp.oo) == 1 for v in relation)
    direction, = b.nullspace()
    assert direction[0] == 0 and strict_sign(direction[2], 3, sp.oo) != 0
    # Certify rank three after every specialization using one fixed minor.
    assert strict_sign(b.extract((0, 1, 3), (0, 1, 3)).det(), 3, sp.oo) != 0
    for v in (*direction, *relation):
        assert strict_sign(sp.denom(sp.cancel(v)), 3, sp.oo) != 0
    print("Certified both limiting height cones throughout the sharp ray.", flush=True)
