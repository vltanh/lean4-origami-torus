# Direct Type 4 search without the convex-flip constraint

Status: numerical diagnostic, no certified embedding, no exclusion.
The mathematical reconstruction itself is the eight-parameter, at most
16-branch tetrahedral reconstruction in type4_focus/README.md; the direct
strict geometry proof in global_attack_support.md discharges its strict
support and strict K4 premises. This checkpoint implements the
reconstruction without a convex-coplanar quadrilateral restriction.

## Labels and reconstruction

Use the published labels of the Type 6 construction after flipping 57 to
23, without requiring either diagonal to be coplanar with the four
boundary vertices. The resulting Type 4 face list is
    015 052 031 024 043 136 145 174 167 264 276 347 356 465 532 723.
The Lutz relabeling is (0,3,2,5,4,1,6,7).
The old marked cochain is inherited except that 57 is removed and 23 has
shift (-1,1). This is the unique strict hexagonal marking orbit.

Gauge at universal vertex 4. Use anchor (4,3,5,6); its six prescribed
edge lengths determine a strict spatial tetrahedron from its Gram
matrix, up to congruence. Vertices 2 and 1 are the independent four-
neighbor conic roots. Vertices 0 and 7 are the independent degree-five
leaves. Thus six intrinsic anchor coordinates plus one parameter per
conic give at most 16 algebraic candidates. All metrics are recovered
by scalar root formulas; this is the existing complete mathematical
reconstruction applied directly, rather than a new restriction to the
flip locus. The mathematical proof retains nonzero linear and tangent
branches and uses a finite choice of conic coordinate direction.

The numerical implementation selects a coordinate of each root from
a sample (switching coordinates by the sign of the second sampled
coordinate), solves the conic, then solves the rank-four polarized
systems of the leaves by SVD and their scalar quadratics. It uses
floating-point arithmetic and skips ill-conditioned or linear cases;
the numerical experiments are not exhaustive.

## Diagnostic at x=1/2, W=3/4

The direct batched search used seed 24601, 25 batches of 30,000
parameter proposals, half uniform in the bounding square of the
hexagonal Voronoi cell and half perturbed from a pool of 19 low-
crossing candidates of the previous convex-flip search. It retained
both roots of each numerical quadratic. The archived scratch pool is
not a certified input or part of a proof. The old and new results are
not counts of distinct geometries.

| Filter | Count |
|---|---:|
| Shortest anchor edges | 230,358 |
| Positive definite anchor, metric and orientation filters | 218,772 |
| First independent conic roots | 421,362 |
| First root accepted | 222,144 |
| Second independent conic roots | 428,962 |
| Both roots accepted | 199,343 |
| First leaf candidates accepted | 398,666 |
| Full candidates after second leaf | 797,324 |

The full assignments pass all 24 metric residuals to tolerance 1e-8,
six strict hexagonal Voronoi inequalities per marked edge, positive
intrinsic face areas, and necessary nonedge contractions against nine
translates. The final cofactor screen covers the 140 disjoint
edge-face pairs. No candidate had zero potential crossings; best was
two (compared with three in the previous flip-constrained search).
Five local optimizations maximizing the signed cofactor separation
margin subject to the full edge equations all reached margins of
order 1e-14 or smaller, not positive certified margins.

The following exact combinatorial observation explains one recurring
failure of this refinement. For the tuple (a,b,c,d,e) consisting of
edge ab and disjoint face cde, write the five adjusted affine
cofactors
    C_i = (-1)^i det([1,r_j]_{j!=i}) * (+1 if i<2 else -1).
If all C_i have the same weak sign and some are nonzero, the
affine dependence supplies an intersection of the disjoint edge
and face (zeros allow lower-support intersections).

Use [ijkl] for the ordered affine determinant with increasing indices.
For edge 03 and face 246 the adjusted cofactors are
    -[2346], -[0246], -[0346], -[0236], +[0234].
For edge 05 and face 246 they are
    +[2456], -[0246], +[0456], -[0256], -[0245].
Thus whenever the four fixed terms in the first list are strictly
positive and those in the second list strictly negative, avoiding
the first crossing requires [0246]>0, while avoiding the second
requires [0246]<0. The zero case is also excluded. Such a region
of strict surrounding signs contains no embedding, regardless of
the metric, even when the free bracket vanishes. This is a direct
vertex/face-contact trap, not a newly discovered independent
constraint beyond the complete circuit formulation.

A second recurring trap is
    edge 15 / face 024: -[0245], +[0124], -[1245], -[0145], +[0125],
    edge 24 / face 015: +[0145], -[0125], -[1245], +[0245], -[0124].
Here four fixed signs force opposite strict signs of [1245].
The observed numerical refinement limits had these traps; enumerating
all sign assignments to the two (or, in the other observed limit,
five) nearly zero brackets never eliminated both crossings.
No exact metric limiting point is certified, and the two nearly zero
brackets in the first trap are not necessarily clique determinants.
Only the conditional sign obstruction is exact.

These diagnostics are evidence to stop repeating that local refinement,
not to infer nonuniversality. The direct constructive search now has
no artificial flip restriction, but remains a finite numerical sample.

## Pivot

See planar_seed_screen.md for a distinct constructive approach:
classify planar inflation bases by all face-sign masks in the strict
hexagonal marking. The exact necessary screen leaves 109 regular
orientation orbits. This includes every regular planar base with a
strict spatial lift, not all 3D solutions. Its real metric and lift
tests remain to be solved. The original obstruction count is 0/8.
