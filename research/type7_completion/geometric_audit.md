# Type 7: geometric necessity audit

## Result and scope

This audit supplies the hand-proof bridge from an actual Type 7 realization
to the geometric premises used in the ray-4 certificate. It also checks the
archive/Lean label convention and replays the independent Boolean proof.
It does **not** close any of the fifteen remaining ray-1/2/3 systems, and
it does not supply the missing Lean bridge.

The conclusions, in ordinary mathematical language, are:

1. An embedded, facewise isometric Type 7 torus has strict neighbor
   support, a mixed-side incident face at every vertex, and noncoplanar
   four-cliques. A sufficiently small generic vertex perturbation
   preserves these conditions, embeddedness, and the linking numbers of
   disjoint cycles.
2. Its coherent edge cocycle belongs, after the stated relabelings and
   lattice isometries, to the four sharp-ray marking classes.
3. The cycles `0246` and `1357` have nonzero linking. Consequently the
   **ray-4 marking is excluded when `y^2 >= 63/16`**, including equality.

These statements use the established seven-vertex nonexistence theorem,
the spherical hemisphere lemma, and standard properties of linking
number. They are not new axioms or new Lean theorems. The original
research-level geometric qualifications for ray 4 can be replaced by the
explicit dependencies and arguments below. Formal assembly of the
negated `Type7.Realizes` statement remains open, as do the other markings.

## 1. Starting from the actual realization predicate

Use [`Type7.ChartRealization`](../../OrigamiTorus/Type7/Tiling.lean) with
`flipped=false`, first period `1`, and second period `1/2+i*y`, on the
reduced sharp ray `y>0`, `y^2>=3/4`. Its homeomorphism identifies the abstract sixteen-face complex
with the lattice quotient; its closed embedding gives the spatial
surface; its affine face charts and facewise metric identity give the
intrinsic flat metric. In particular this is a paper torus in the sense
of Schwartz, not just a solution of its edge equations.

The following extraction explains why no extra hypothesis of globally
chosen vertex lifts is needed in a hand proof.

* Choose one supplied face chart containing each vertex and use its
  vertex coordinate as the representative `p_i` in the plane. Every
  occurrence of that vertex in another face chart projects to the same
  quotient point. Its difference from `p_i` is therefore a lattice
  period, uniquely an integer pair because `y>0`.
* On an edge shared by two faces, the two affine edge charts project to
  the same path. Their difference is a continuous map of the connected
  interval into the discrete lattice, so it is constant. Thus their
  edge displacement vectors agree. Subtracting their endpoint period
  labels defines a face-independent integer edge cocycle `K_ij`.
  Reversal negates it and its sum around every face is zero.
* The affine chart of each face is nondegenerate: an affine dependence
  of its three vertices would give two distinct barycentric points
  with the same quotient image, contradicting the homeomorphism.
  Similarly, spatial vertices and disjoint simplices have distinct
  images. The coherent oriented face charts all have one common
  orientation sign, the local orientation sign of the homeomorphism.
  Their oriented double areas sum to plus or minus twice the
  fundamental-cell area.
* The integer cocycle generates the full lattice. One may either use
  the induced isomorphism on first homology, or the explicit translated
  face-cover argument already implemented in
  [`generating_walks_of_quotient`](../../OrigamiTorus/Winding/WindingGeneration.lean).
  The finitely many compact face lifts and all their lattice translates
  cover the plane, locally finitely. Paths between a tile and its two
  primitive translates give closed edge walks with periods `(1,0)` and
  `(0,1)`. Hence the two basis-cycle periods form a unimodular matrix.

Every graph edge is **strictly** shortest among its lattice translates.
Indeed the image of any straight intrinsic competitor has length at
most its intrinsic length, by subdividing it at the finitely many lifted
face boundaries. The prescribed edge already maps to the straight
spatial chord. A shorter competitor contradicts the chord bound. In the
equality case the image of the competitor must be that same chord,
traversed at constant speed. Spatial injectivity makes its quotient path
equal to the prescribed edge path. Their lifts, starting at the same
point, then agree, contradicting a different endpoint period. This is
the argument formalized generally in
[`strict_period_comparison_of_compact_cover`](../../OrigamiTorus/Winding/ShortestWinding.lean).

## 2. Four-marking coverage and the label check

At `x=1/2`, `y^2>=3/4`, the reduced-basis hypothesis
`1<=x^2+y^2` holds. The strict-shortest bounds then put each nonzero triangular period
in

\[
\{(1,0),(-1,0),(0,1),(0,-1),(1,-1),(-1,1)\}.
\]

The existing Lean results `triangle_mem_allowed`,
`marking_mem_candidates_of_shortest_edges`,
`marking_unimodular_of_quotient`, and `exists_orbit_representative`
give the finite cover once supplied with the extracted data above.
The basis cycles are `012` and `025`. Relabelings are automorphisms of
the actual Type 7 face list, and target symmetries are isometries of
every sharp-ray lattice. Thus the marking reduction must be applied
jointly to the vertex, metric, and embedding data.

The following entries were checked directly from
[`cases.json`](../linking_checkpoint/cases.json), against the
[`Lean dual cocycle and tree gauge`](../../OrigamiTorus/Winding/WindingCocycle.lean).

| Marking | Periods of `012`, `025` | Period of each alternating ring | Period of `01234567` |
|---|---|---|---|
| ray 1 | `(-1,0)`, `(-1,1)` | `(0,1)` | `(-4,1)` |
| ray 2 | `(-1,0)`, `(0,1)` | `(1,1)` | `(-3,1)` |
| ray 3 | `(-1,1)`, `(0,-1)` | `(1,-2)` | `(-3,2)` |
| ray 4 | `(-1,1)`, `(0,1)` | `(1,0)` | `(-3,4)` |

The ordered face lists in both orientation and linking archives agree
exactly with `Type7.faces` in
[`Rectangular.lean`](../../OrigamiTorus/Type7/Rectangular.lean), not merely
up to an unspecified permutation. Their edges are exactly the pairs
other than `04`, `15`, `26`, `37`. All face cocycle sums vanish. After
the Lean tree gauge, every archived edge shift is the image of the Lean
dual cocycle under the corresponding displayed matrix.

This discharges the hand-proof extraction and convention issue. There
is still no Lean theorem here extracting the data directly from
`ChartRealization`; the existing finite theorems should not be described
as already proving that complete implication.

## 3. Strict support from eight-vertex minimality

The external inputs are [Schwartz, *Vertex-Minimal Paper Tori*,
arXiv:2507.14998v9](https://arxiv.org/html/2507.14998v9): Theorem 1.1
excludes seven-vertex paper tori, and Lemma 2.1 puts a simple spherical
polygon of length at most `2*pi` in a closed hemisphere. These precise
statements were checked in the source; strict support is the following
additional argument, not the statement of Lemma 2.1 itself.

At a vertex `v`, intersect its embedded star with a sufficiently small
sphere and radially rescale to the unit sphere. The result is a simple
spherical polygon `L`; flatness gives length `2*pi`. It lies in a closed
hemisphere with normal `n`.

Suppose no plane through `v` strictly separates all its neighbors from
`v`. By convex separation, zero is in the convex hull of the neighbor
directions. Because their scalar products with `n` are nonnegative,
any positive term in a convex combination giving zero is on the
equator. Planar Caratheodory reduces it to either two antipodal
directions or three equatorial directions enclosing zero.

For an antipodal pair, the two paths of `L` joining them each have
length at least `pi`. Their sum is `2*pi`, so both are shortest great
semicircles. For an enclosing triple without an antipodal pair, their
three minor-arc distances sum to `2*pi`; the three corresponding paths
in `L` attain those distances, so `L` is the equator. Therefore the
star is either planar or consists of two planar parts joined along a
line through `v`.

In the two-plane case the ends of the two semicircles are actual link
corners, hence directions of two incident edges. Their two neighbors
and `v` are collinear, with `v` between them. Replace these two edges
by the segment joining the neighbors and triangulate each planar half
of the star without `v`. In the planar case, triangulate the entire
boundary polygon without `v`. The boundary polygons are simple because
the original star is embedded. Triangulations can retain collinear
boundary subdivision vertices while making every triangle
nondegenerate.

Every new diagonal lies inside the old star. It cannot already be an
edge outside that star: such an edge would intersect its interior in
the original embedded complex. The replacement is therefore a
simplicial triangulation of the same embedded surface, with the same
intrinsic metric and exactly seven vertices. This contradicts
Theorem 1.1. Consequently every vertex has strict support relative to
its six neighbors.

No conclusion about the global convex hull of all eight vertices is
needed. In particular, the opposite nonneighbor need not lie on the
supported side.

## 4. Mixed-side faces, four-cliques, and perturbation

Central projection from `v` maps its strictly supported spherical link
to a simple planar polygon. If no incident face has neighbors on both
strict sides of its plane, every edge line supports that polygon. It
is consequently convex, allowing collinear subdivisions. The spherical
link then bounds a convex spherical polygon in an open hemisphere.
Its perimeter is strictly below `2*pi`: a generic great circle meets
its boundary at most twice, and an open set of great circles misses
it, so the strict bound follows from Crofton's formula. This
contradicts flatness and proves the mixed-side property.

Any four-clique is spatially noncoplanar. Three collinear clique
vertices give overlapping edges. Four coplanar vertices with no three
collinear either form a convex quadrilateral, whose diagonal edges
cross, or have one vertex inside the triangle of its three neighbors,
contradicting strict support. These cover all coplanar possibilities.

The relevant properties are open in the finite vertex coordinates.
For embeddedness, all pairs of disjoint closed simplices have positive
distance. Preserving these finitely many separations suffices: an
unintended intersection of two simplices sharing labels yields an
intersection of disjoint subfaces by canceling common barycentric
mass. Strict support normals, selected mixed-side face witnesses, and
four-clique determinant signs also persist. A small perturbation can
therefore make all seventy affine brackets nonzero while retaining
every required condition.

The straight interpolation from the original placement to a sufficiently
small perturbation stays within the same open set of embeddings.
Disjoint polygonal cycles consequently remain disjoint during this
homotopy, so their linking numbers do not change. **Flatness need not
persist.** The perturbation is used only for necessary orientation and
linking signs; actual metric equations concern the original placement.

## 5. Necessity and replay of the ray-4 orientation certificate

The source [`satgeom.py`](../orientation_checkpoint/satgeom.py) was
checked against the geometric statements it encodes:

* each Grassmann--Plucker clause forbids three nonzero terms of one
  determinant identity from having one common sign;
* each five-point affine dependence has coefficients summing to zero;
  its forbidden `2+3` partitions would make a disjoint edge and face
  intersect, and its forbidden `1+4` neighbor partitions violate
  strict support;
* each vertex selects an incident face with both strict signs among
  its other neighbors.

Reflection fixes the first bracket positive without loss; it is the
nonzero four-clique `0123`. The auxiliary conjunctions in
[`verify_linking.py`](../linking_checkpoint/verify_linking.py) encode
exactly the signed transverse intersections of a polygon with the
oriented triangle fan spanning another polygon. Genericity prevents
boundary intersections. The partial-sum implications start at zero and
force the true running signed sum; prohibiting every nonzero terminal
state is thus necessary for unlinking. Extra auxiliary states are
irrelevant to this necessary implication.

Assume `0246` and `1357` were unlinked. The generic perturbation just
constructed supplies a model of that formula. Fresh replay of
`verify_full_ring4.py` found the sixteen archived primary sign models
and verified that blocking all of them is UNSAT. To avoid trusting that
solver outcome, `generate_ray4_rup.py` regenerated the blocked formula
and trace, and `check_ray4_rup.cpp`, compiled without `NDEBUG`, checked:

```text
PASS UNSAT: 7786 original clauses, 8018 checked input lines,
4379 RUP additions, 3976 deletions
```

The independent checker accepts a logged input only if already present
or reverse-unit-propagation implied, and requires a derived empty
clause. Its guard extension is equisatisfiable with the original
formula. `verify_final_polynomial.cjs` then checked both six-inequality
Grassmann--Plucker certificates, the exact cancellation of their
products, and coverage of all sixteen models under relabeling and
reflection. Every model is nonrealizable, a contradiction. Therefore
the alternating rings have nonzero linking for every actual flat
Type 7 embedding, independent of the marking or modulus.

The stored formula is a necessary relaxation; no sufficiency claim
about arbitrary Boolean sign models is used.

## 6. Linking, diameter, and the complete ray-4 hand proof

For a primitive lattice period `h`, any two distinct parallel intrinsic
geodesics are disjoint simple curves in its slope. Their images have
length `|h|`. Any two disjoint simple cycles of that primitive slope on
the torus are isotopic as a pair to such fibers, so their common
linking number is `q(h)`.

If `q(h)` is nonzero, every pair of fiber convex hulls intersects:
otherwise a separating plane splits the link. A simple closed curve
of length `|h|` has diameter **strictly** less than `|h|/2`. Equality
would force its two arcs between a diametral pair to be the same
straight segment, contradicting injectivity. The distance from a point
of the curve to any point of its convex hull is at most its diameter,
by convexity of the norm. Thus two points on different fibers have
distance less than `|h|`; points on the same fiber satisfy the stronger
half-length bound. Compactness gives an attained surface diameter, so
`diam(T)<|h|` follows without a separate uniform-fiber estimate.

In ray 4 the alternating rings have the same primitive period `(1,0)`.
Section 5 therefore gives `diam(T)<1`. Each of the eight spatial edges
of `01234567` has length less than one, whereas the period of this
cycle is `(-3,4)`, of physical norm `sqrt(1+16*y^2)`. Facewise isometry
and the intrinsic triangle inequality give

\[
\sqrt{1+16y^2}\leq\operatorname{length}(01234567)<8.
\]

Hence `y^2<63/16`. This contradicts `y^2>=63/16`, and proves the stated
whole-marking exclusion, including actual nongeneric embeddings.
The finite winding computation was separately replayed with
`verify_cycle_thresholds.py`.

## 7. Remaining formal and research obligations

The hand-proof audit above retires the research-level geometric
qualification on the existing ray-4 exclusion. It does **not** turn it
into a kernel-checked theorem. In particular the current Lean library
still needs the direct `ChartRealization` extraction, the Type 7
strict-support/mixed-side bridge, a formal linking/diameter theory, and
the connection from the Boolean/final-polynomial checks to those actual
geometric signs. The successful research scripts are not Lean proof
terms.

At `tau=1/2+10^6*i`, the research ledger therefore remains **ray 4
excluded; rays 1--3 open, comprising fifteen systems**. Closing the
other three markings at this same modulus is still necessary for the
negative classification. This audit supplies no metric contradiction
for them and no claim that the small-projected-determinant region of
ray 3 is empty.
