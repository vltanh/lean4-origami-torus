# Saturated shortest routes: a geometric obstruction to 14 Type 5 planar masks

**Result.** Fourteen complete orientation classes (72 masks modulo global
sign reversal) of the regular planar-inflation problem at the hexagonal
modulus have no nondegenerate facewise-isometric planar folding at all.
This reduces the preceding 76-class / 415-mask ledger to **62 classes /
343 masks**. The certificates require only two to four linear shortest-lift
inequalities, with coefficient one. No height feasibility or rank
calculation is needed. The result concerns mixed-sign stars; it does not
exclude singular inflation bases with monochromatic stars, general spatial
realizations, or any elongated cell.

## 1. The saturated-route theorem

Let a flat triangulated torus have a facewise-isometric continuous map into
the plane, with nondegenerate intrinsic triangles, distinct intrinsic
vertices, and both face orientation signs present at every vertex.
Work in its periodic intrinsic lift. An edge separating opposite face
signs is a crease; all other edges join two faces whose rigid isometries
agree across the edge.

For a fixed face-sign pattern and winding cocycle, define R(a,b) for
distinct vertices a,b to be the finite set of intrinsic lifts of the
displacement from a to b obtained by either of these rules:

1. Both vertices belong to a common edge-connected same-sign face
   component; use their coherent lift in that component.
2. They are the endpoints of a crease-edge path with every internal
   vertex incident to precisely two crease edges. Sum the directed
   cocycle along the path. Include all subpaths, not just maximal paths.

For the masks checked here the same-sign components have consistent
coherent lifts, and the crease paths terminate without a repeated vertex.
More generally a component with inconsistent lifts or a closed straight
crease chain is already impossible under these hypotheses.

**Claim:** a lift k preserves endpoint distance,
||p_b-p_a+k|| = ||r_b-r_a||, if and only if k belongs to R(a,b).

Proof of sufficiency. On any unfolded component, the map is a single
Euclidean isometry on its coherent lifts. At a mixed star the signed
angular change of the projected link is a multiple of 2*pi with absolute
value strictly below 2*pi: the intrinsic angles sum to 2*pi and both
signs occur. The signed change is therefore zero. The sums of the
positive-sign and negative-sign angles are each pi. At a vertex with
exactly two creases, each of the two angular sectors is monochromatic,
and each spans pi. The crease rays are opposite both intrinsically and
in the image, so the path in rule 2 is straight in both planes. The
displacement sum preserves endpoint distance.

Proof of necessity. The lifted map is nonexpanding: subdivide any
intrinsic straight segment into its face pieces and use the triangle
inequality. If its endpoints preserve distance, equality in the triangle
inequality forces the map of the entire segment to be a straight
unit-speed segment. A transverse crossing of a crease interior reflects
the direction, so is impossible. If the segment passes through an
interior vertex, the two opposite intrinsic tangent rays must map to
opposite planar rays. Each of the two half-links between those intrinsic
rays is a path of angular length pi with antipodal image endpoints. Its
image must be a minimizing semicircle, hence its orientation is constant
on all face portions in its interior. Since the star is mixed, the two
half-links have opposite signs and exactly the two segment rays are
crease rays. Thus the segment passes through the vertex along two
collinear crease edges, and the crease degree there is two.

Consequently a saturated segment containing no interior vertex is
contained in a single same-sign component (or runs along one edge).
A saturated segment containing an interior vertex is a chain of crease
edges with degree two at its internal vertices: once the segment
contains an interval of a crease edge it follows that edge until the
next vertex, where the preceding half-link argument applies again.
These are exactly the two rules. A repeated intrinsic point would
contradict the positive distance traversed by a unit-speed image
segment. This proves necessity.

The theorem uses no generic-position assumption or positive lower bound
on angles. It applies to every modulus and every fixed marking under the
mixed-star hypothesis. In particular, **every shortest lift tied with
a saturated lift must itself occur in the finite route set.** It also
improves the weak nearest-lift inequalities: a comparison with a missing
route must be strict.

## 2. Two-to-four-inequality certificates

Use the archived sharp Type 5 marking at tau=1/2+i*sqrt(3)/2,
with the face order of planar_patterns.md. Coordinates in the lattice
basis (1,tau) have squared norm N(x,y)=x^2+xy+y^2.
For k in R(a,b), let d=p_b-p_a+k. Global contraction and the route
theorem give

    2<d,l> <= N(l)                    (all lattice vectors l),

and equality is forbidden if k-l is not in R(a,b). Indeed equality
would give N(d-l)=N(d), hence a saturated missing lift.

For every mask in the table, the verifier enumerates R directly from raw
edge-connected monochromatic face components and straight crease paths.
No merged components, LP hull, Kawasaki polynomial reduction, or metric
solver is required. It checks that the known lift is in R and the missing
lift is not. The displayed certificate terms in verify_saturated_routes.py
are shortest inequalities on actual route lifts; their sum is exactly
the negative of the target weak inequality, including its constant.
Thus equality is forced, contradicting the required strictness. All
coefficients are one.

| Representative | Orbit size | Pair | Known lift | Forced missing lift | Terms |
|---:|---:|---|---|---|---:|
| 3500 | 6 | 01 | (0,0) | (1,-1) | 3 |
| 3731 | 6 | 01 | (1,0) | (1,-1) | 3 |
| 3737 | 6 | 01 | (1,0) | (1,-1) | 2 |
| 4014 | 6 | 56 | (1,0) | (0,0) | 4 |
| 5849 | 6 | 12 | (0,-1) | (-1,0) | 2 |
| 6873 | 3 | 13 | (0,1) | (-1,1) | 4 |
| 10838 | 6 | 05 | (-1,1) | (-1,0) | 2 |
| 10905 | 3 | 01 | (1,0) | (1,-1) | 3 |
| 10957 | 6 | 35 | (0,0) | (-1,0) | 4 |
| 10961 | 3 | 12 | (-1,0) | (0,-1) | 2 |
| 10965 | 6 | 12 | (-1,0) | (0,-1) | 2 |
| 11084 | 6 | 12 | (0,0) | (0,-1) | 4 |
| 12121 | 6 | 34 | (0,0) | (-1,0) | 2 |
| 12185 | 3 | 34 | (0,0) | (-1,0) | 2 |

For example, in 3737 the route set for pair 01 is {(0,0),(1,0)}.
The route 16 with lift (0,1) gives

    2<p6-p1+tau,tau> <= 1,

and route 06 with lift (0,0) gives

    2<p6-p0,-tau> <= 1.

Adding and using ||tau||^2=1 yields 2<p1-p0,tau> >= 0.
The known route 01 with lift (1,0) gives
2<p1-p0+1,tau> <= 1. Since 2<1,tau>=1, equality is forced,
and the missing lift (1,-1) would also preserve distance.
This is a contradiction. The other 13 arguments have the same form.

## 3. Validation and next gate

Run from the repository root:

    python3 research/type5_completion/verify_saturated_routes.py

The verifier reads the archived face and shift tables, checks the
six metric-preserving automorphisms and gauge transformations, enumerates
the actual route sets, verifies all integer row-sum identities, and
checks disjoint orbit counts. It also lists the 62 remaining
representatives and orbit sizes in its OPEN constant. The optional
--ledger flag replays the previous exact regular-planar screen and
checks that the six old geometric exclusions, fourteen new exclusions,
and 62 remaining representatives partition its 82 classes. That optional
mode uses the dependencies of the earlier screen.

The standalone certificate checker passed locally against a fixture of
the exact archived Type 5 face list and all 24 edge shifts retrieved
from the branch. A separate local reimplementation of the earlier
screen reproduced 448 masks in 82 classes and the complete remaining
ledger. LP was used to discover the short sums, but the final checker
requires only integer arithmetic. The optional combined repository
invocation was not run locally. No Lean source changed.

The earlier signed-area/Pluecker investigation also excludes some of
these same masks, including 3737 and 5849, but adds no independent
exclusions to this ledger. A Boolean oriented-matroid projection test
without metric constraints found satisfying sign assignments for its
tested remaining masks; those assignments do not construct a geometric
folding. The short-route proof replaces the more complicated polynomial
contradictions for the 14 masks above.

Next: use the finite route theorem's strict inequalities and full
geodesic compatibility in the remaining 62 classes. The present
certificates eliminate entire continuous classes before vertical lift
or inflation. The full Type 5 universality question remains open.
