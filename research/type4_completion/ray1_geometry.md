# Ray 1: a perimeter obstruction and forced-contact lemma for the bare annuli

**Status: a conditional geometric reduction, not a fixed-target exclusion.**
This note treats the three ray-1 cap pairs for which one of the two annuli
has six faces and no interior vertices. It proves a convex-hull/perimeter
lemma for their transverse polygon model. In an exact model with two
disjoint nested fibers, it rules out a nonconvex bare fiber unless a
specified missing cross-cap chord is exposed. In a weakly nested limit,
the same proof can force contact instead of a contradiction.

The finite target remains open. In particular, an embedded sequence can
have projected limiting curves which touch or coincide. No uniform
separation, cap-area bound, or finite-height replacement for the limiting
perimeter identity is asserted here.

## 1. The three annulus decompositions

Use the Type 4 faces

    012 031 024 053 045 152 134 146 165 264 257 276 374 356 367 475.

Cut the face-dual graph along the edges of the two cap triangles. For
`ray1_1`, `ray1_3`, and `ray1_5`, the two components have six and ten
faces. The six-face component contains no vertices outside the caps.
Call it the **bare annulus**. The other three ray-1 rows have two
eight-face annuli, each containing one additional vertex, and are not
covered by the calculation below.

The cap orders in this table follow the same horizontal orientation;
both have period `(-1,0)` in the first marking.

| Case | Ordered caps A / B | Six bare faces | Interior vertices of the other annulus |
|---|---|---|---|
| `ray1_1` | `014 / 375` | `031 053 045 134 374 475` | `2,6` |
| `ray1_3` | `014 / 256` | `012 024 152 146 165 264` | `3,7` |
| `ray1_5` | `034 / 162` | `012 031 024 134 146 264` | `5,7` |

These statements are finite checks of the actual face graph, including
which annulus contains each additional vertex. They do not assume an
orientation chamber or a positive lower bound on a determinant.

## 2. The exact transverse polygon model

Let `A_i` and `B_j` be two nondegenerate planar triangles, each of
perimeter one, with the vertex orders above. For `0<t<1`, put

    C_ij(t) = (1-t) A_i + t B_j.

The regular slice of the bare annulus has the following cyclic vertex
list. The final point is joined to the first.

| Case | Bare polygon P(t) | Directed edge word |
|---|---|---|
| `ray1_1` | `C03,C13,C43,C47,C45,C05` | `A01,A14,B37,B75,A40,B53` |
| `ray1_3` | `C02,C12,C15,C16,C46,C42` | `A01,B25,B56,A14,B62,A40` |
| `ray1_5` | `C01,C31,C41,C46,C42,C02` | `A03,A34,B16,B62,A40,B21` |

For example, in `ray1_3`, the edge from `C12` to `C15` is exactly
`t(B5-B2)`, and the edge from `C16` to `C46` is
`(1-t)(A4-A1)`. Each A edge and each B edge occurs once. Consequently
the polygonal-walk length is exactly

    length(P(t)) = (1-t) perimeter(A) + t perimeter(B) = 1.       (1)

This identity does **not** assert that P is convex or even simple.
Convexity cannot be inferred just by merging the edge words of two
triangles. Simplicity and any nesting hypotheses used below are separate
geometric assumptions.

Write

    M(t) = (1-t) conv(A) + t conv(B),                            (2)

where the plus sign denotes the Minkowski sum of convex sets. Equivalently,
M is the convex hull of all nine points `C_ij`. It is a nondegenerate
convex polygon and

    perimeter(M(t)) = 1.                                      (3)

To see (3) without making any assumption on P, use the perimeter formula
`perimeter(K) = integral_0^pi width_K(theta) d theta` for a convex polygon.
Widths add under Minkowski sums and scale linearly under positive
homotheties. The formula itself follows by projecting the polygonal
boundary: its total variation in a direction is twice its width, and
the integral of the absolute projection of an edge of length L is `2L`.

## 3. Which Minkowski points are supplied by actual edges?

Every actual edge joining the two cap triangles supplies its point
`C_ij(t)` to the corresponding annulus in this exact model. Six such
points belong to P. The remaining actual cross-cap edges belong to the
other annulus, whose fiber will be denoted Q.

| Case | Additional cross-cap points on Q | Missing cross-cap pairs | Number m of additional points |
|---|---|---|---:|
| `ray1_1` | `C15` | `07,17` | 1 |
| `ray1_3` | `C05,C45` | `06` | 2 |
| `ray1_5` | `C36` | `06,32` | 1 |

The last missing pair `32` is the unordered graph nonedge `23`; it is
written with its A vertex first. Let E(t) be the set of all the actual
cross-cap points in this table together with the six vertices of P.
Thus E has respectively seven, eight, and seven labeled points.

The useful hull condition is

    conv(E(t)) = M(t).                                        (4)

It is enough to verify that every missing point lies in `conv(E(t))`.
Section 5 gives an equivalent condition in terms of the cap triangles'
normal cones, independent of t.

## 4. Perimeter saturation forces an outer convex boundary

### General lemma

Let P and Q be closed polygonal curves of length one. Suppose:

1. P is the bare polygon in section 2, and Q contains the additional
   actual cross-cap points in section 3;
2. one of the curves, C, has a convex hull containing both curves;
3. the hull condition (4) holds.

Then

    conv(C) = M(t),       trace(C) = boundary(M(t)).            (5)

Condition 2 is automatic when P and Q are simple nested planar curves
and C is the outer one. It also makes sense for a weakly nested limit
with contact. No positive gap between the curves is needed for (5).

**Proof.** The convex hull K of C contains every point of E, hence M.
For any closed polygonal curve, the perimeter of its convex hull is at
most its length. Therefore

    1 = perimeter(M) <= perimeter(K) <= length(C) = 1.

All inequalities are equalities. Inclusion is strictly monotone for
perimeters of nondegenerate compact convex polygons: a proper inclusion
strictly increases a support function, and hence the width, on an open
set of directions. Thus `K=M`.

Equality between a polygonal walk's length and its hull perimeter means
that it traverses the convex boundary, allowing collinear subdivisions
and zero-length pauses. Indeed, visiting hull vertices out of their
cyclic order strictly lengthens the tour; in cyclic order, any detour
off a hull edge strictly lengthens the corresponding connecting path.
This proves the trace assertion in (5). QED.

### Consequences for a bare annulus

If P is the outer curve, it must be the convex boundary of M. In
particular, a genuinely nonconvex bare polygon cannot be outer under
(4), even if the inner curve is allowed to touch it.

If Q is the outer curve, it equals the boundary of M. Every extreme
vertex of M is one of the actual cross-cap points, by (4). At most m of
these points are additional Q points. Since M has at least three
extreme vertices, at least `3-m` distinct extreme vertices belong to P.
Consequently

    trace(P) meets trace(Q) at at least 3-m extreme vertices of M.  (6)

More precisely, the bound is `k-m` if M has k extreme vertices. Thus
the guaranteed minimum is two contacts in `ray1_1` and `ray1_5`, and one
in `ray1_3`.

For **disjoint simple nested curves**, (6) is impossible. In that exact
model, (4) therefore forces the bare curve to be the outer convex
boundary of M. This leaves a possible nonconvex inner curve Q; convexity
of the outer curve alone is not a perimeter contradiction.

There is a further restriction in this disjoint model: **none of the
additional Q points may be an exposed vertex of M**. Such a point
would lie both on Q and on the outer boundary P, again giving contact.
Thus an exposed additional Q point, together with (4), rules out both
possible nesting orders. In a weak limit it forces contact instead.

For a **weakly nested limit**, (6) is a forced-contact conclusion. It
does not exclude an embedded sequence whose separation tends to zero.
Under (4), a nonconvex limiting bare curve can only be inner, with the
contacts just described. Excluding that contact degeneration requires
an additional metric argument.

## 5. The exceptional exposed chords

For a vertex a of a convex triangle A, define its open normal cone by

    N_A(a) = { n : n dot a > n dot a' for each other vertex a' }.

For positive weights, `C_ij(t)` is an exposed vertex of M exactly when

    N_A(A_i) intersects N_B(B_j).                              (7)

If a direction belongs to both cones, it uniquely maximizes the sum
at that pair. Conversely, a direction exposing a vertex of the sum
must expose a unique vertex in each summand. This also shows that an
exposed grid point has a unique pair of cap vertices representing it.

It follows that (4) holds exactly when none of the missing cross-cap
pairs in section 3 satisfies (7). This criterion depends on the edge
directions of the two caps, not on t or their relative translations.
All boundary cases are retained: if two normal-cone closures only meet
on a ray but their open cones do not intersect, the corresponding sum
point is not an omitted exposed vertex, so it causes no exception to
(4).

For `ray1_3`, the entire exception is therefore

    N_A(A0) intersects N_B(B6):                                (8)

the absent edge `06` would supply an exposed corner of the Minkowski
polygon. Without (8), the perimeter argument forces either an outer
convex bare fiber or the inner-bare contact degeneration of section 4.
For `ray1_1`, the possible exceptions are `07` and `17`; for `ray1_5`,
they are `06` and `23`.

In the strictly disjoint `ray1_3` model with no exposed missing pair,
the additional points `C05,C45` cannot be exposed either. Consequently

    N_B(B5) is contained in N_A(A1).                           (9)

Indeed, an open direction uniquely supporting B5 can support neither
A0 nor A4. It must uniquely support A1. A direction tied between two
A vertices cannot lie in the open B5 cone either: a small perturbation
would then expose one of the forbidden pairs. This gives the familiar
planar-angle consequence

    interior_angle_B(5) >= interior_angle_A(1).                (10)

The open normal cone at a triangle vertex has angle `pi` minus its
interior angle. Neither (9) nor (10) is asserted for the contact or
exposed-missing-pair alternatives. A metric argument giving the strict
opposite angle comparison on this whole remaining model would therefore
be decisive there; no such comparison is assumed or proved here.

This identifies specific geometry still needing analysis. It does not
assume that a nonedge chord is a surface edge or that its interpolation
point lies on Q.

## 6. Scope of the passage from elongated tori

The [bounded-cap analysis](../type4_focus/elongated_hand.md) proves that
an **isolated** cap cycle in an elongated sequence has intrinsic
physical vertical width tending to zero, spatial axial width tending
to zero, and perimeter tending to one. Here “isolated” means that its
final bounded cluster consists of the chosen cycle's vertices. For the
model in this note, this conclusion is required for **both** cap
triangles, and their transverse limits must remain nondegenerate.
The two extra vertices can instead join a bounded cap cluster; that
possibility is not removed by the six-plus-ten face decomposition.

At a regular height between two isolated caps, interpolation along each
cross-cap edge gives the limiting points `C_ij(t)`. The bare face word
then gives (1). To use the second curve Q, one must also justify its
regular-slice convergence, its limiting length one, and the appropriate
weak nesting. These are geometric hypotheses of the application, not
consequences of the finite combinatorial checker below.

At finite y, actual horizontal fibers are intrinsic geodesics. An
ambient plane section need not be exactly such a fiber, and its
perimeter need not be exactly one. Projection can also change length.
Conversely, limits of embedded fibers can touch or coincide. Therefore
the exact-model disjointness contradiction cannot be applied directly
to the full finite domains in the roadmap.

A finite exclusion would need a quantitative version of the perimeter
comparison together with control of the forced contacts, or a different
argument ruling out the exposed missing-chord regimes and the possible
outer-convex bare annulus. No such bridge is proved here.

## 7. Exact finite check

    python3 research/type4_completion/ray1_geometry.py

The checker verifies the annulus decompositions, face-by-face slice
cycles, both cap periods, the three occurrences of each cap's edges,
and all additional and missing cross-cap pairs. It uses finite sets and
integer cocycles only. The perimeter and normal-cone arguments are the
hand proofs above; the checker does not claim a real-feasibility
decision or a Lean theorem.
