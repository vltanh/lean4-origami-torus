# Ray 3 is impossible at all sufficiently large heights

## Research theorem

There is a real number `Y3 >= 8` such that no embedded flat Type 7 torus
of modulus `1/2 + i*y`, with `y >= Y3`, has the third sharp-ray marking

\[
\bigl([012],[025]\bigr)=\bigl((-1,1),(0,-1)\bigr).
\]

Equivalently, there is **no unbounded sequence of actual ray-3
realizations**. Both localized phases are included, since the checked
marked symmetry identifies them. The proof uses the
[audited geometric necessities](geometric_audit.md), the exact finite
orientation covers, and the uniform analytic arguments listed below.
It retains zero nonclique brackets and arbitrary relative collapse rates.

This is a research proof, not a Lean theorem. It does not provide a
numerical value of `Y3`; in particular it does not assert `Y3 <= 10^6`.
The fixed-target ledger remains **0 of 15 ray-1/2/3 systems closed at
`1/2 + 10^6 i`**, with 78 of the 132 ray-3 metric chambers excluded by
separate finite-height certificates.

## 1. Compactness reduces an unbounded sequence to a common line

Suppose an unbounded sequence exists, and pass to a subsequence with
`y -> infinity`. Write `t=1/y²`. The exact phase localization and
[relative bounds](relative_cap_bounds.md) give bounded transverse
coordinates for the short caps `A=0145`, `B=2367`. Their positive
horizontal weights satisfy

\[
h_e=-X_e>0,\qquad \sum_{e\in A}h_e=\sum_{e\in B}h_e=1,
\qquad h_e<\tfrac12.
\]

After a convergent subsequence, every physical short-edge length tends
to its weight. The following complete exclusions force both physical
cap limits onto one common transverse line:

| Physical limiting caps | Proof |
|---|---|
| Both noncollinear | [Exact stress-cone obstruction](cap_limit.md), with the [complete shape cover](exhaustive_cap_shapes.md) and zero-base boundaries |
| Collinear on different lines | [Nonparallel corner](exhaustive_nonparallel_corner.md) and [complete weak-order/cluster cover](exhaustive_collinear_caps.md) |
| Exactly one noncollinear | [Complete one-collinear-cap proof](remaining_one_collinear.md) and its separately normalized short-edge directions |

These arguments use actual edge directions before taking limits. They
do not assume that a collapsing edge is comparable to `t` or to another
collapsing edge.

## 2. A nontrivial bounded normal blow-up always exists

Use a verified phase symmetry to put a longest short edge at `01`;
its weight is at least `1/4`. Choose longitudinal axis `02`, and rotate
the transverse plane so that `P1-P0` is positive horizontal. The common
line is then `Y=0`, with transverse anchors `P0=P2=0`.

Set `delta=max_i |Y_i|`. For every actual realization `delta>0`:
otherwise all eight vertices would lie in one spatial plane, contrary
to the nonzero K4 bracket `0123`. Also `delta -> 0`. Thus the stretched
points `(X_i,Y_i/delta)` have a convergent subsequence, with at least
one nonzero limiting normal coordinate.

In this blow-up the physical metric becomes the seminorm `|Delta X|`.
The relative axial increment divided by a stretched short-edge norm is
still `O(t)`, so every necessary point/direction sign remains valid.
The two caps have at least two positive physical weights each. Hence a
collinear stretched cap is not vertical, and the common shear used in
the mixed and two-line proofs is legitimate.

There are exactly three cases: both stretched caps collinear, exactly
one collinear, or both noncollinear. The following sections exclude
each completely.

## 3. Every two-line blow-up is excluded

The [complete weak-order calculation](common_line_edge_collapse.md)
checks all 5,476 pairs of nonconstant four-point weak orders. Necessary
orientation signs exclude 4,140. The exact seminorm stress excludes
712 more. The remaining 624 zero-stress pairs are partitioned by their
number of zero physical short weights:

| Zero weights | Orders | Complete exclusions |
|---:|---:|---|
| 1 | 16 | [One-edge moving-height proof](remaining_two_line_blowup.md) |
| 2 | 352 | [288 triple clusters](remaining_two_line_triple.md), [32 paired 14/36 orders](remaining_two_line_blowup.md), [16 split pairs](remaining_split_blowup.md), [16 paired 14/67 orders](exhaustive_two_single_blowup.md) |
| 3 | 176 | [Complete three-zero cover](exhaustive_three_zero_blowup.md) |
| 4 | 80 | [48 triple/triple orders](remaining_fourzero_blowup.md) and [32 triple/split orders](remaining_fourzero_split.md) |

There is no zero-weight-free survivor. All coincidences and all relative
small-edge scales occur in these weak-order and direction covers.

## 4. Every mixed blow-up is excluded

The exact degenerate-norm cover has 1,292 mixed cells. Its disjoint
partition and proofs are:

| Zero weights | Cells | Complete exclusions |
|---:|---:|---|
| 0 | 24 | [Positive-weight metric proof](remaining_flat_blowup.md) |
| 1 | 80 | [48 adjacent collisions](remaining_adjacent_blowup.md) and [32 partner collisions](remaining_partner_blowup.md) |
| 2 | 568 | [24 double-partner cells](remaining_double_partner_blowup.md) and [544 triple-cluster cells](remaining_cluster_blowup.md) |
| 3 | 320 | [304 triple-cluster endpoints](remaining_three_cluster_blowup.md) and [16 adjacent-collision endpoints](remaining_three_adjacent_blowup.md) |
| 4 | 300 | [Complete four-zero cover](exhaustive_four_cluster_blowup.md), including [both vertical V endpoints](exhaustive_four_cluster_v.md) |

The final 300 cells have 35 canonical shapes and three relative A-edge
scales. Of the 105 cases, 73 have direct Boolean contradictions and
twelve more contradict a separately normalized partner edge. The
remaining twenty map to six metric endpoints and their checked mirrors.
Four-defect analytic charts, exact reference families, and factored
actual brackets exclude those endpoints. The exceptional endpoint
retains the branch where a small edge has zero leading horizontal
projection.

All 96 final-package CNFs have independent RUP proofs. A fresh complete
producer reproduced exactly the same clause multisets. The batch,
including its shared coverage proof, took 21.377 seconds in the research
workspace. Four formulas required a second deterministic producer order;
every accepted replacement trace was checked independently from its start.

## 5. Every two-noncollinear-cap blow-up is excluded

The [complete shape cover](exhaustive_cap_shapes.md) leaves trapezoid
alignments or V/V alignments. The [point-sign proof](exhaustive_vv_geometry.md)
excludes the V/V cases and the perpendicular-base stress boundary.
For nonvertical trapezoid bases, the
[closed zero-cone calculation](common_line_trapezoids.md) covers all
32 sign cones and all zero supports among their 116 extreme rays.
Its 652 bilinear products are nonnegative. Exactly 16 supports can
involve a positive base in each cap.

Those supports force two triple-cluster/tip physical caps, with two zero
weights and two weights `1/2` in each. Their four zero-weight patterns
are one checked marked orbit of a triangle pair with normal-height ratio
`0 < lambda < infinity`.

The [triangle-pair proof](remaining_two_triangles_blowup.md) excludes
this entire family. Its finite formula forces two missing-base directions
and the weak sign `[0347]>=0` after relabeling. Let `a,b,c,d` be the four
vanishing positive short weights and `M=max(a,b,c,d)`. An exact planar
reference for every small `t`, together with a determinant-2048 regular
metric chart, proves

\[
b+d-U_5-(U_6-U_3)=o(M).
\]

The individual metric bounds make both summands nonnegative up to
`O(tM)`, so each is `o(M)`. Factoring the required bracket along the
actual short paths `04` and `37` then yields

\[
\lambda(a+b)+c+d\le o(M).
\]

Its left side is at least `min(lambda,1)*M>0`. All axial and normal
errors retain the short-path factor, so the contradiction permits
unrelated rates of `t`, normal width, and all four small weights.
The endpoints `lambda=0` or infinity are mixed limits already excluded
in Section 4.

## 6. From no unbounded sequence to an eventual exclusion

Sections 3–5 exhaust every nontrivial stretched limit supplied by
Section 2. Thus the assumed unbounded sequence cannot exist.
If no threshold `Y3` existed, for every integer `n>=8` one could choose
a ray-3 realization at some height `y_n>=n`. This would be precisely
the unbounded sequence just excluded. Therefore such a finite threshold
exists, proving the theorem.

This logical step needs no numerical compactness estimate. It also
explains the distinction from the separate fixed-height target: the
proof gives a common eventual bound for all ray-3 placements and both
phases, but does not compare that bound with `10^6`.

## Remaining Type 7 gates

Ray 4 has an explicit research exclusion for `y²>=63/16`. Rays 1 and 2
still require complete exclusions. Eventual bounds for those two markings
would suffice: choosing one height above all four bounds would give a
Type 7 counterexample, without needing the particular value `10^6`.
Alternatively, the existing fourteen fixed-mask systems could be closed
at a common height also known to exceed the ray-3 bound.

The geometric necessities, finite certificate interpretation, compactness,
and uniform analytic arguments must still be assembled in Lean before
claiming the requested formal classification. No theorem is replaced by
an unchecked solver result, timeout, or additional axiom.
