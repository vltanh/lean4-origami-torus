# Exact cap identities for the whole F1 block

**Scope.** These are necessary identities and inequalities for every realization
in any of the five F1 cells. They do not exclude a cell. They identify the
possible cap degenerations explicitly, without a lower bound on cap area.
The proof uses the exact edge metric and the strict horizontal nearest-lift
inequality, not a nonzero tetrahedron or an orientation archive.

## 1. A primitive horizontal triangle has three positive short increments

Orient an essential triangle so its horizontal winding is +1. Write its
three lifted horizontal increments as `h1,h3,h2` in cyclic order. Their sum
is 1 and each lies strictly between -1/2 and 1/2. Each is therefore positive:
if one were nonpositive, the sum of the other two would be strictly less
than 1. Thus

    0 < hi < 1/2,       h1+h2+h3 = 1.

Set `ui=1-2*hi`. The three short-edge margins satisfy

    ui > 0,            u1+u2+u3 = 1.

In particular at least one `hi` is at least 1/3. A reconstruction may align
its first coordinate with a longest cap edge using three charts, and that
edge has squared length at least 1/9. This does not give a positive lower
bound on the cap's altitude.

Gauge the intrinsic coordinates at the common endpoint of the `h1` and
`h2` edges. The other two lifted coordinates are `(h1,b1)` and `(-h2,b2)`;
the opposite edge uses horizontal shift +1. The three squared spatial
edge lengths are exactly

    d01 = h1^2+b1^2,
    d02 = h2^2+b2^2,
    d12 = h3^2+(b2-b1)^2.

## 2. Positive cap Gram decomposition

Let `B` be the two-by-two spatial Gram matrix at the chosen base vertex.
Write `s=h1+h2-1/2=u3/2` and `b=(b1,b2)^T`. Polarization gives

    B = T+b*b^T,
    T = [[ h1^2,       -h1*h2+s ],
         [ -h1*h2+s,   h2^2     ]].

`T` is positive definite. Indeed `h1>0` and

    D := det(T)
       = 2*(1/2-h1)*(1/2-h2)*(h1+h2-1/2)
       = u1*u2*u3/4 > 0.

The exact determinant is

    det(B) = D + h2^2*b1^2 + h1^2*b2^2
                 + 2*(h1*h2-s)*b1*b2
           = D + b^T*adj(T)*b.

As `adj(T)` is positive definite, vertical phase differences cannot reduce
the cap determinant. Hence

    det(B) >= u1*u2*u3/4 > 0,
    16*(spatial triangle area)^2 >= u1*u2*u3.

The first weak inequality can be equality: this happens exactly when
`b1=b2=0`. It must not be replaced by a strict inequality.

For a division-free sum-of-squares certificate, put

    c = h1*h2-s.

Then

    h2^2*(det(B)-D) = (h2^2*b1+c*b2)^2 + D*b2^2,
    h1^2*(det(B)-D) = (h1^2*b2+c*b1)^2 + D*b1^2.

These polynomial identities prove the inequality even for arbitrarily
small positive shortest-edge margins. Their closed versions remain valid
on every boundary stratum.

## 3. The three collapse faces and their kernels

Suppose a convergent sequence of such cap data has spatial cap determinant
tending to zero. In the closed limit `ui>=0`, `sum(ui)=1`. The determinant
identity forces at least one `ui=0`; a cap cannot collapse while all three
horizontal margins stay positive. On each boundary face the determinant
becomes one square:

| Boundary face | Horizontal relation | Exact limiting `det(B)` | Necessary condition for collapse |
|---|---|---|---|
| `u1=0` | `h1=1/2`, `h2+h3=1/2` | `(h2*b1-h1*b2)^2` | `h2*b1=h1*b2` |
| `u2=0` | `h2=1/2`, `h1+h3=1/2` | `(h2*b1-h1*b2)^2` | `h2*b1=h1*b2` |
| `u3=0` | `h3=1/2`, `h1+h2=1/2` | `(h2*b1+h1*b2)^2` | `h2*b1=-h1*b2` |

The formulas also cover intersections of boundary faces, including a
vanishing horizontal edge. No division by `hi`, `ui`, or a cap area is
needed in the table. The conclusion is conditional on convergence of the
displayed vertical phase data; it does not itself supply a uniform bound
on those phases in an elongated sequence.

## 4. Substitution for both F1 caps

Use the sharp marking gauged at vertex 1, physical horizontal coordinates
`xi`, and physical vertical coordinates `vi` (`vi=y*bi` in the fixed
generator's normalized notation). The same two essential triangles occur
in every F1 cell, even when vertices 2 or 7 also enter a cap.

| Cap and orientation | Base | `h1` | `h2` | `h3` | `b1` | `b2` |
|---|---:|---|---|---|---|---|
| `1 -> 0 -> 4 -> 1` | 1 | `x0` | `-x4` | `1+x4-x0` | `v0` | `v4` |
| `5 -> 6 -> 3 -> 5` | 5 | `x6-x5+1/2` | `x5-x3+1/2` | `x3-x6` | `v6-v5+y` | `v3-v5+y` |

The first cap uses spatial Gram vectors `(r0-r1,r4-r1)`; the second uses
`(r6-r5,r3-r5)`. The formulas hold for the whole marked realization,
independently of the particular localized cell. The verifier checks the
listed horizontal and vertical winding directly from the archived cocycle,
checks all five F1 memberships, and verifies the polynomial identities.

If squared distances are normalized by `y^2`, the corresponding Gram
determinant is divided by `y^4`. The necessary bound is then

    det(B_normalized) >= u1*u2*u3/(4*y^4).

## 5. A related exact angular inequality

At a corner of the cap, let `u,v` be the two consecutive intrinsic edge
vectors, and let `w` be the opposite edge. Let `theta_ext` be the exterior
turning angle of the spatial cap triangle, in `[0,pi]`. Let `theta_int` be
the unsigned angle between `u` and `v`. Since the intrinsic edge vectors
sum to `(1,0)` while the spatial edge vectors sum to zero,

    cos(theta_ext)-cos(theta_int)
       = (2*h_opposite-1)/(2*|u|*|v|) < 0.

Thus `theta_ext>theta_int`. Equivalently, if either side of the intrinsic
annulus is capped by its spatial triangle, the total angle at each cap
vertex is strictly less than `2*pi`: the annulus angle is `pi` plus or
minus the signed intrinsic turn, whereas the cap angle is
`pi-theta_ext`. This is an angular inequality only. It does not establish
convexity or embeddedness of the capped polyhedron.

## Reproduction

    python research/type5_completion/f1_geometry_verify.py

The new bounds isolate exactly where the cap-plane estimates lose
uniformity: the three explicit horizontal margin faces. A whole-cell
exclusion still needs to combine these bounds with the cross-cap metric
equations and the embedding conditions.

## Extension to every essential triangle

The same argument applies to any three-edge cycle with nonzero lattice
period `ell`, at any modulus. Put `w=|ell|^2>0`. For each lifted intrinsic
edge vector `e`, uniqueness of its shortest lift against `e+ell` and
`e-ell` gives

    -1/2 < (e dot ell)/w < 1/2.

The three quantities sum to 1, so they again are the positive `hi` above.
After gauging at one vertex, write the other two intrinsic vectors as

    p1 = h1*ell+c1*J(ell),
    p2 = -h2*ell+c2*J(ell),

where `J` is a quarter-turn and `ci=det(ell,pi)/w`. The opposite edge uses
the period `ell`. Exact polarization now gives

    B = w*(T+c*c^T),
    det(B) >= w^2*u1*u2*u3/4 > 0.

This is a quantitative noncollinearity theorem for every essential
triangle. It uses no convexity, strict support, or K4 premise. The two
displayed SOS identities apply after replacing `B` by `B/w` and `b` by
`c`; all denominators are known positive and may be cleared. The bound is
an additional useful consequence of the exact edge metric and the
shortest-lift inequalities, not an independent assumption.
