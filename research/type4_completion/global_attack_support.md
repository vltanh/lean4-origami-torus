# Direct strict support and strict K4 proof for every flat Type 4 embedding

This is a hand proof valid for **every embedded Type 4 realization with
cone angle `2*pi` at each vertex**, independently of modulus, marking,
cap choice or degeneration scale. It discharges the strict-support and
strict-K4 research premises used by the Type 4 metric reductions. It does
not exclude any of the eight fixed-target domains, and it is not a new
Lean theorem.

Unlike the earlier argument in the orientation checkpoint, this proof
does not delete a vertex, retriangulate a folded star, or appeal to
nonexistence of seven-vertex paper tori. Its finite input is the actual
Type 4 face graph, checked by `global_attack_support.py` using integers
and finite sets alone.

## 1. Spherical equality facts

At an embedded vertex `v`, normalize each incident edge vector to a unit
vector. Consecutive vectors are joined by the shorter great-circle arc
corresponding to the incident triangle. Their cyclic spherical polygon
has length `2*pi`, by intrinsic flatness. Neighbor directions are
nonzero and distinct, because overlapping radial edges would violate
embeddedness.

We use three elementary angular facts, already represented in the
repository's general spherical-perimeter lemmas.

1. Selecting points in cyclic order cannot increase the angular
   perimeter, by the spherical triangle inequality. Equality means that
   each intervening arc is a shortest path between its endpoints. When
   those endpoints are not antipodal, this path lies on their unique
   shorter great-circle arc.
2. Three noncollinear directions with a strictly positive linear
   dependence have angular perimeter `2*pi`. No two are antipodal.
   Four affinely independent directions with a strictly positive linear
   dependence have angular perimeter strictly greater than `2*pi`.
3. If the cyclic polygon contains antipodal directions `a,b`, the two
   intervening paths each have length at least `pi`. Their sum is
   `2*pi`, so each is a minimizing semicircle and lies in a plane
   through the origin. This conclusion allows arbitrary intermediate
   vertices: choose any one intermediate direction `c`, which differs
   from `a,b`; equality on the two subpaths puts them both in
   `span(a,c)`. A path with no intermediate vertex would be an incident
   triangle of angle `pi`, already forbidden by embeddedness.

For (2), the three-direction statement says that their rays surround the
origin in their two-dimensional span. The four-direction statement is
the strict spherical-perimeter inequality for a positive independent
four-point dependence. The existing general lemmas include
`triangle_perimeter_eq_of_positive_relation`,
`quadrilateral_perimeter_gt_of_positive_relation`,
`angularCycleLength_mono`, and `mem_span_of_angularPathLength_eq` in
[SphericalPerimeter.lean](../../OrigamiTorus/Geometry/SphericalPerimeter.lean).

## 2. No Type 4 vertex star is planar

Every closed neighborhood contains a complete graph on five vertices:

| Vertex | Cyclic link | A K5 in the closed neighborhood |
|---|---|---|
| 0 | `12453` | `01245` |
| 1 | `025643` | `01245` |
| 2 | `015764` | `01245` |
| 3 | `014765` | `01345` |
| 4 | `0261375` | `01245` |
| 5 | `0361274` | `01245` |
| 6 | `142735` | `12456` |
| 7 | `25436` | `24567` |

If the star at a vertex were planar, all vertices of the displayed K5
would lie in the same affine plane. Their ten straight edges are actual
surface edges. A straight-line drawing of K5 in a plane must have an
intersection between disjoint edges or a vertex on a nonincident edge,
contradicting embeddedness. This statement retains all degenerate
positions; it does not assume that the five points are in general
position. The general Lean theorem `Type2.clique_not_planar` already has
an arbitrary face-list parameter, despite its namespace.

## 3. Every one of the 23 clique tetrahedra is strict

Suppose four clique vertices were coplanar. No three can be collinear:
the middle point would lie on the actual edge joining the other two.
They also cannot be in convex position, because the two actual diagonal
edges would intersect. Thus one clique vertex `v` lies strictly inside
the triangle of the other three `a,b,c`.

The three vectors from `v` have a strictly positive dependence and none
are antipodal. Their angular triangle has perimeter `2*pi`. They occur
in some cyclic order in the full link, also of perimeter `2*pi`.
Equality in the three intervening spherical triangle inequalities puts
every neighbor direction in the plane of `a,b,c`. Hence the entire
star at `v` is planar, contradicting section 2.

Therefore **all 23 K4s are nondegenerate tetrahedra in every embedded
flat Type 4 realization**. The proof gives strict positivity of the
corresponding Gram determinants, but no uniform positive lower bound.
It remains valid when their determinants tend to zero along a sequence.

This argument precedes strict support and does not use it; consequently
using it in the next section is not circular.

## 4. No link contains an antipodal neighbor pair

If neighbors `a,b` are adjacent, antipodality would place `v` on the
actual edge `ab`, contrary to embeddedness. It remains to check only
nonadjacent neighbor pairs.

For every such pair, one of its two closed link arcs contains three
vertices which, together with `v`, form a K4. The complete table is:

| Center | Antipodal pair | One closed link arc | Contained K4 |
|---|---|---|---|
| 0 | `23` | `2453` | `0245` |
| 1 | `06` | `0256` | `0125` |
| 1 | `23` | `25643` | `1256` |
| 2 | `07` | `0157` | `0125` |
| 2 | `06` | `01576` | `0125` |
| 2 | `17` | `76401` | `2467` |
| 3 | `07` | `0147` | `0134` |
| 3 | `06` | `01476` | `0134` |
| 3 | `17` | `76501` | `3567` |
| 4 | `06` | `613750` | `1346` |
| 4 | `07` | `026137` | `0124` |
| 4 | `23` | `2613` | `1246` |
| 4 | `17` | `750261` | `2457` |
| 5 | `06` | `612740` | `1256` |
| 5 | `07` | `036127` | `0135` |
| 5 | `23` | `3612` | `1356` |
| 5 | `17` | `740361` | `3457` |
| 6 | `17` | `1427` | `1246` |
| 6 | `23` | `35142` | `1356` |
| 7 | `23` | `2543` | `2457` |

Under antipodality, this arc is a minimizing semicircle by section 1,
so all its rays are coplanar. The displayed K4 would be planar,
contradicting section 3. This exhausts all 20 nonedge-pair cases.

## 5. Strict support at all eight vertices

Suppose `r_v` lies in the convex hull of its neighbors. Choose a
support-minimal positive convex combination. In three dimensions it
uses at most four neighbors, and its direction vectors are affinely
independent. A single neighbor is impossible by injectivity. Two give
an antipodal pair, excluded by section 4. Four give a selected spherical
quadrilateral of perimeter greater than `2*pi`, contradicting the full
link length. Three give a selected spherical triangle of perimeter
`2*pi`; section 4 rules out antipodal pairs, so equality forces the
entire star planar as in section 3, contradicting section 2.

Thus `r_v` is outside its neighbors' compact convex hull. Strict
separation supplies a normal `n_v` with

    n_v dot (r_w-r_v) > 0

for every neighbor `w` of `v`. This is the required strict local support.
It makes no claim that each vertex is an extreme point of the full
eight-vertex convex hull.

The convex separation and minimal-dependence steps are already general
in `Type2.strictSupport_iff_not_mem_linkHull` and
`Type2.ordered_pair_or_triple_of_flat_link` in
[Links.lean](../../OrigamiTorus/Type2/Links.lean).

## 6. Scope and formalization boundary

The proof establishes strict support and strict K4 determinants from
embeddedness, the actual Type 4 face list and flat vertex stars. In
particular, all strict clique signs and the local six-pattern K5 Radon
lists used by the active cap analysis have their geometric premise
directly justified; singleton Radon parts would violate strict support.

The finite checker verifies all eight link cycles, the eight K5
certificates, all 23 K4s and every one of their 92 possible
interior-vertex incidences, and all 20 nonedge antipodal-pair cases.

    python3 research/type4_completion/global_attack_support.py

A Lean implementation can reuse the general lemmas named above. The
remaining formal work is the Type 4 link data, a generic
positive-three-direction planar-star lemma with hypotheses only for
the three selected pairs, a minimizing-semicircle planarity lemma, and
the finite tables. The existing `Type2.link_is_planar_of_positive_triple`
asks for absence of **all** antipodal link pairs; it cannot be used
unmodified in section 3 without introducing a circular argument.

No new Lean build is claimed. The current metric and topological
obstruction to an entire `ray2_2` domain remains open.
