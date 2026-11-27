# All planar inflation seeds at the hexagonal modulus: a finite screen

Status: **109 necessary orientation classes for regular planar seeds,
121 for arbitrary nondegenerate planar seeds.** No class surviving the
screen is asserted feasible. No new spatial embedding or universality
theorem. The reduction concerns the planar-inflation approach, not
arbitrary three-dimensional Type 4 realizations.

The constructive work in flip_ready_type6.md used a particular
convex-coplanar quad and three marked inverse-flip classes. This
checkpoint removes the flip requirement entirely. It uses the existing
hexagonal marking equivalence and the Lutz Type 4 face list.

## 1. All monochromatic face components

Let h=(1,0), g=(1/2,sqrt(3)/2). Consider a continuous planar map
of the hexagonal torus, affine and isometric on each nondegenerate
triangle of the Type 4 triangulation. It need not be injective.
Choose intrinsic lifts p_i and the ray-2 marking of type4_gap_enum.py,
which represents the sole hexagonal marking orbit. This latter
coverage uses the previously established winding/orbit results
(with weak nearest-lift inequalities for planar realizations; see
the qualification below).

For a face, record the sign of its planar map relative to its
coherent intrinsic orientation. There are 2^15 assignments modulo
an overall spatial reflection. Join faces of equal sign across
shared edges. On each connected component of this dual graph,
the developed triangles have a common Euclidean isometry into
the target plane: two equal-orientation isometries agreeing on
the endpoints of a nondegenerate edge agree everywhere.

Each occurrence of a vertex in this component must have the same
intrinsic lift relative to its chosen starting face. Otherwise the
same isometry would send two points differing by a nonzero lattice
vector to the same planar vertex. This is impossible. Check this
by propagating the integer edge cocycle on all edges in the component.

Moreover **every pair** of vertices in the component has its
coherent lift difference as a shortest lattice representative,
even when the pair is not an edge. The global planar map is
distance nonincreasing, because its facewise isometry preserves
the length of a path broken at face crossings. Its image distance
for that pair equals the length of the coherent lift difference.
The intrinsic distance is at most the latter length. Hence all
three quantities agree.

These two facts are necessary even if there are many shortest-lift
ties, coincident nonadjacent planar vertices, or nonconvex components.
They require no uniform lower bound on any face area.

### Weak marking qualification

The enumeration uses the archived sharp-ray cocycle. In fact
weak shortestness gives the same list of possible triangle periods
at the hexagon as strict shortestness: each edge vector belongs
to the closed hexagonal Voronoi cell. A triangular cycle of three
such vectors has its period in three times that cell; boundary
periods could include longer lattice vectors. Consequently the
claimed exhaustiveness for *all* planar seeds is conditional on
the weak marking coverage. For **regular, inflatable planar seeds**
with a strict spatial lift, this qualification is removed by
the existence of nearby embedded realizations at fixed periods:
their unique shortestness and previously verified marking
classification supply the chosen cocycle. A planar seed at which
no nearby embedding exists is not automatically in that marking.
The screen therefore covers every planar seed relevant to the
regular inflation strategy, and every nondegenerate planar seed
in the archived marking. It is not asserted to classify other
weak markings that cannot be inflated.

## 2. Exact integer nearest-lift propagation

Use doubled inner products
    A_i=2 p_i dot h, B_i=2 p_i dot g, C_i=B_i-A_i.
The translation p4=0 fixes the intrinsic translation gauge.
A shifted difference p_j-p_i+m*h+n*g is shortest, with ties
allowed, exactly when its projections satisfy the three strips
    |A_j-A_i+2m+n| <= 1,
    |B_j-B_i+m+2n| <= 1,
    |C_j-C_i-m+n| <= 1.
These are the six sides of the hexagonal Voronoi cell. Each
radial edge 4i has zero marking shift in this gauge, so all three
coordinates are bounded by 1 in absolute value. Differences are
bounded by 2.

Represent all the upper bounds as three integer matrices U.
Reverse ordered pairs encode lower bounds. Every pair of
vertices in a coherent monochromatic component supplies the
three strip constraints, in addition to the actual edge
constraints. Repeat the following exact operations:
    U^k_ij <- min(U^k_ij,U^k_iq+U^k_qj)
for every intermediate vertex q, followed by the three
consequences of B=A+C:
    U^A_ij <- min(U^A_ij,U^B_ij+U^C_ji)
    U^B_ij <- min(U^B_ij,U^A_ij+U^C_ij)
    U^C_ij <- min(U^C_ij,U^B_ij+U^A_ji).
A negative diagonal or incompatible upper/lower bounds is a
contradiction. Otherwise all bounds are integers in a finite
interval and decrease monotonically, so the propagation
terminates. This is a necessary test, not a claim of completeness
for the coupled three-coordinate linear system.

If the closed bounds force the coherent differences of a face
to have one common zero projection, that triangle is collinear.
If two independent projections of one edge are forced zero,
that edge collapses. Finally if two independent edge vectors
are completely fixed, test their determinant exactly. These
tests reject any such degenerate face.

## 3. Geometry of overlaps between components

Two equal-sign isometries agree if a common actual edge has
identical lift difference in both components. Its endpoints
are distinct because that edge belongs to a nondegenerate
face. Translate the lifts of one component by the corresponding
common lattice vector and merge the components. If the new
lifts disagree at another common vertex, reject. Repeat to
closure and include the additional coherent pair differences.

For two components, choose a shared vertex a and write their
lifted differences to every shared vertex i as u_i and u_i+d_i,
where d_i is a lattice vector. Equality of their planar images
implies R*u_i=u_i+d_i for one orthogonal relative linear map R.

* For equal signs, R is a rotation. If any d_i is nonzero, R-I
  is invertible. Equal d_i and d_j imply coincident images of
  i,j, impossible for an actual edge. If the d_i span a line,
  all shared vertices are collinear.
* For opposite signs, R is a reflection, so all d_i lie in its
  one-dimensional normal space. If all d_i vanish, the shared
  vertices lie in its axis. In either of the collinearity cases,
  a shared vertex set containing the three labels of any actual
  face is impossible, whether or not that face is in one of the
  two components.
* If opposite signs have a nonzero d_i, its direction fixes the
  normal. The two coherent differences are both shortest.
  Therefore |d_i| <= 2/sqrt(3) and, in the hexagonal lattice,
  d_i is a shortest vector. Choose its unit direction n among
  h,g,g-h, up to sign. The reflection identity gives
     2 n dot (u_j-u_i) = - n dot (d_j-d_i).
  The right side is an integer since d_j-d_i is parallel to
  this lattice direction. This supplies additional exact
  upper and lower projection bounds before repeating section 2.

All rejections in this section are necessary independently of
the existence of an inflation or a regular Jacobian.

## 4. Extra cuts for regular inflation

Use the fixed-period squared-edge-length residual map on the
two planar sheets (16 spatial planar coordinates and 16
intrinsic coordinates). Its 24-component derivative must be
surjective for the ordinary regular inflation argument.

A monochromatic star at any vertex excludes that surjectivity.
In a planar neighborhood preserving the signs and nondegenerate
triangles, its spatial angle sum is locally constant: it is
the signed turning sum with every sign identical. Thus the
differential of its cone angle on spatial planar coordinates
is zero. The intrinsic angle sum is also locally constant
because the intrinsic sheet triangulates the fixed torus.
The nonzero derivative of that cone angle with respect to
independent squared edge lengths annihilates the residual
derivative. Nonzeroness follows, for example, by changing
one vertex's conformal weight in the cotangent angle formula
from Type6.md; the strict positive energy of that nonconstant
weight makes its own angle derivative nonzero. Height
derivatives vanish at the planar base as well. Hence the
regular residual Jacobian cannot have rank 24.

There is a second independent rank obstruction. After eliminating
the three spatial Euclidean motion degrees and the two intrinsic
translations, there are 27 planar variables. A surjective
24-row residual Jacobian gives a smooth local 3-dimensional
fixed-period planar solution manifold. This manifold locally
projects injectively and immersively into the 14 intrinsic
coordinates: given the intrinsic lengths and fixed face
orientation signs, placing one triangle in a rigid-motion
gauge and propagating across the dual graph uniquely and
smoothly determines every other spatial planar vertex.
Infinitesimally, zero intrinsic motion gives only rigid
spatial motions, which the gauge removes.

All exact equalities found in sections 2-3 hold throughout that
local manifold. If the rank of their integer coefficient matrix
is at least 12, their affine solution space after intrinsic
translation has dimension at most 2. That contradicts the
3-dimensional immersion. The checker computes a rigorous
lower bound on the rational rank by row reduction modulo 101.
A nonsingular minor modulo 101 is nonzero over the rationals.
This rejects only patterns whose dimension upper bound is
strictly below 3; no claim that dimension >=3 suffices for
regularity is made.

For the marking qualification in section 1, one may alternatively
apply these differential cuts to a regular nondegenerate base
in an already fixed marking, without any spatial lift. The
full coverage claim for the inflation strategy is for bases
that actually admit a strict embedded lift at this modulus.

## 5. Exact outcome

Run from the root (requires NumPy, not a real or Boolean solver):

    python3 research/type4_completion/planar_seed_screen.py --output /tmp/planar-orbits.json

The integer arithmetic in the equivalent scratch implementation
was run to completion:

| Stage | Rejected | Retained |
|---|---:|---:|
| All face signs, modulo reflection | 0 | 32,768 |
| Inconsistent component lifts | 30,045 | 2,723 |
| Contradictory difference bounds | 364 | 2,359 |
| Forced degenerate faces | 1,868 | 491 |
| Same-sign overlap inconsistency | 12 | 479 |
| Shared-face collinearity | 36 | 443 |
| Regularity-only tests | 38 | 405 |

The initial consistent-lift patterns give 2,705 distinct
pair-difference systems. There are 121 orbits of the 443 surviving
general patterns and 109 orbits of the 405 surviving regular
patterns. The checker enumerates all four Type 4 face-list
automorphisms, and checks that each preserves the marked
cocycle up to one of the twelve actual hexagonal lattice
isometries and a vertex coboundary. Global reflection normalizes
the last face sign to zero. All output orbits are explicitly
checked to lie in their respective surviving sets.

This replaces a search over a specific published folding
pattern by a finite necessary cover for the constructive
planar strategy. The surviving patterns require real metric
compatibility, strict face nondegeneracy, and a strict
spatial lift; neither their feasibility nor their
infeasibility follows from the screening. The 109 classes
are **not** a new exhaustive case cover of arbitrary 3D
Type 4 embeddings. They do not change the original 0/8
fixed-target exclusion count.

## 6. Next decisive use

For each surviving regular orbit, impose its already computed
linear equalities and shortest-lift bounds, then propagate
the signed planar isometries across a dual spanning tree.
Require every repeated vertex to agree exactly. Nondegenerate
intrinsic triangle areas and the consistent sign pattern
must be retained. A positive candidate needs a strict
edge-face lift certificate and the fixed-period residual
Jacobian rank check, as in the Type 6 construction. An exact
regular seed at the hexagon would give a Type 4 realization
on an open neighborhood of moduli. Closing all 109 classes
negatively would only eliminate this regular planar-inflation
route at the hexagon, not Type 4 universality.

No new Lean source or certified spatial witness is claimed.
