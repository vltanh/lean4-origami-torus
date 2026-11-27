# Linking obstructions and the elongated Type 7 marking

**Status:** No new universality type is closed. This checkpoint introduces a global metric obstruction, computes its effect on the remaining marking families, and derives a bounded exact rescaling for Type 7 ray_4. The orientation-filter conclusions use the earlier necessary SAT relaxation and inherit its audit qualifications. The metric diameter theorem itself is independent of that relaxation. The previous fixed-hexagon attack was redirected to the elongated range because of this global obstruction.

## 1. Linked parallel geodesics bound the diameter

For a primitive period h in the intrinsic lattice, orient the parallel closed geodesics consistently. Denote the linking number of any two distinct fibers by q(h). It is independent of the pair, and equals the linking of any pair of disjoint oriented simple cycles in that slope, by isotopy of parallel curves on a torus. Reversing the ambient orientation changes its sign, not its vanishing.

If q(h) != 0, the convex hulls of two distinct fibers must intersect: disjoint compact convex hulls admit a strict separating plane, which makes the link split. Each fiber has length |h|, and its diameter is strictly less than |h|/2. Indeed, equality would force both subarcs between a diametral pair to be straight segments, contradicting injectivity. The distance from any point of a fiber to any point of its convex hull is at most its diameter, by convexity of the norm. Thus the distance between any two surface points on different fibers is strictly less than |h|, and the same-fiber bound is even smaller. Compactness gives diam(T)<|h|. For any k-edge cycle of period g, its intrinsic length equals the sum of its extrinsic edge lengths and is at least |g|. Hence |g|<k|h|.

For each of the remaining markings there is a triangular cycle with nonzero vertical period. On the sharp-rhombic ray, such a period has length at least sqrt(y^2+1/4) for y>=sqrt(3)/2. Taking h=(1,0), the above inequality forces q(h)=0 whenever y^2>=35/4. For the two Type 5 interior markings the weaker sufficient threshold y>=3 follows from |g|>=y. These thresholds use the short triangular cycle; they are not asserted for arbitrary triangulations of arbitrary size.

## 2. Exact orientation filtering

At general position, the linking number of two disjoint polygonal cycles can be computed by algebraic intersection of the second cycle with the oriented triangle fan spanning the first. Each fan triangle/edge intersection is a five-point affine circuit with exactly that sign partition. The sign of the intersection is the determinant of the oriented triangle and the terminal endpoint of the directed edge. The fan is an oriented 2-chain even if it is not itself an embedded disk. All the intersections are transverse and no edge hits its boundary or diagonals in general position. For non-generic actual embeddings, perturb as in the prior orientation lemma: embeddedness and the strict K4 signs persist and the linking number is invariant, since the sufficiently small straight perturbation is an isotopy of the disjoint cycles. The perturbation need not preserve the metric.

`verify_linking.py` encodes this computation by exact Boolean clauses: two indicators per possible signed intersection, and a partial-sum automaton enforcing final signed sum zero. It applies the filter to all vertex-disjoint pairs of shortest total edge count with primitive horizontal winding in each marking. It then re-enumerates the projection onto the strict K4 signs, and the spanning-3-tree reconstruction signs, using Z3. Counts are necessary Boolean possibilities, not assertions of geometric or metric realizability.

| Marking | Previous K4 patterns | New K4 patterns | Previous tree branches | New tree branches |
|---|---:|---:|---:|---:|
| t4_ray_1 | 120 | 102 | 10 | 10 |
| t4_ray_2 | 120 | 36 | 10 | 7 |
| t5_interior_1 | 138 | 92 | 7 | 7 |
| t5_interior_2 | 138 | 92 | 7 | 7 |
| t5_ray_1 | 138 | 92 | 7 | 7 |
| t7_ray_1 | 316 | 270 | 12 | 12 |
| t7_ray_2 | 316 | 270 | 12 | 12 |
| t7_ray_3 | 316 | 88 | 12 | 9 |
| t7_ray_4 | 316 | 4 | 12 | 2 |

For t7_ray_4 there are only 16 full generic Boolean sign models modulo reflection, not merely 4 clique patterns. `verify_full_ring4.py` verifies all 16 cached models and checks UNSAT after blocking them. The blocked formula has 215 variables and 7786 clauses. An independent unoptimized DPLL replay did not finish within the short time limit used in this checkpoint; this new completeness check uses Z3, not an independently checked UNSAT trace.

## 3. Additional topology of the remaining triangulations

The linking quadratic form of an embedded torus in S^3 has the form q(ma+nb)=+/-mn in the integral basis of slopes that bound in the two complementary manifolds. One justification: Mayer-Vietoris identifies H1(T) with H1 of the two complementary compact manifolds in direct sum; each has rank one (Euler characteristic zero and connected boundary), hence the kernels are complementary primitive rank-one summands. The push-off linking pairing is bilinear and has skew part the intersection pairing, up to common orientation sign. Both basis slopes have self-linking zero, and the mixed coefficient has absolute value one: push into one side and use the bounding chain in the other side for one of the off-diagonal entries. Thus the discriminant is 1 in any integral basis. A pair of linked triangles has linking number 0 or +/-1, by intersecting the planar triangular disk with the other triangle (there are at most two crossings of its plane, of opposite signs).

`verify_topology.py` checks that in each of Types 4,5,7 there is an integral basis a,b with disjoint triangular cycle pairs of each class; both a+b and a-b have simple cycle representatives of at most five edges. The possible quadratic coefficients A=q(a), B=q(b), C (mixed term) satisfy A,B in {-1,0,1} and C^2-4AB=1. It follows A*B=0 and C=+/-1. Consequently the two zero slopes are among a,b,a+b,a-b. In particular both have representatives of at most five sticks. By the standard Alexander theorem for an embedded tame torus in S^3, at least one complementary side is a solid torus; the slope bounding in its complement represents a longitude (coefficient +/-1 in the core direction) and is isotopic to its core within the solid torus. Every polygon of at most five sticks is unknotted (minimum stick number of a nontrivial knot is six). Therefore **every embedded straight-edge realization of Types 4,5,7 is an unknotted torus**, independently of its flat metric. This argument uses standard knot-theoretic theorems, not a new formalization of them.

For Type 5 all three classes (1,0),(0,1),(1,-1) have exactly five unordered pairs of disjoint triangular cycles. Since each class has q in {-1,0,1}, the discriminant relation implies exactly one of the three q values is nonzero, and that value is +/-1. Thus there are exactly five linked pairs of disjoint triangular cycles in any embedded realization of that type. The labels are computed using the first sharp marking as a homology coordinate convention, not a restriction on the metric. At sufficiently large aspect ratio the linked slope cannot be the short direction.

## 4. Narrow-level theorem for Type 7 ray_4

The one-skeleton in this marking has the two 4-cycles A=(0,2,4,6) and B=(1,3,5,7), and all 16 edges between them. Adjust the vertical cocycle by the integer gauge q=(-1,-1,-1,-1,0,-2,-1,-2) (replace K_ij by K_ij+(0,q_j-q_i) and vertex b_i by b_i-q_i). Every ring edge then has vertical shift zero. Across A to B, the shift is either 0 or -1. Orient a cross edge from A to B in the former case, and from B to A in the latter. The resulting directed graph is strongly connected with directed diameter three, exactly verified in `verify_ring4.py`.

Write w=y^2, t=1/w, and l_i=0 on A, 1/2 on B. Write the adjusted intrinsic vertical coordinates as b'_i=l_i+delta_i. On each directed cross edge the normalized vertical displacement is 1/2+delta_j-delta_i. The strict shortest-edge inequalities at x=1/2 give

    w*(delta_j-delta_i) + |X_ij|/2 < 1/8,

where X_ij is the physical horizontal displacement. Every directed path of length <=3 therefore bounds delta_j-delta_i<3/(8w); taking paths in both directions gives |delta_j-delta_i|<3/(8w). This is an exact constraint at every aspect ratio of this marking, not an asymptotic assumption. Setting gamma_i=w*(delta_i-delta_0) normalizes gamma_0=0 and |gamma_j-gamma_i|<3/8. For a directed cycle of k edges it also gives sum |X_e|<k/4.

## 5. Bounded compactification

For w>=35/4, every cross squared distance is w/4+c_ij, with |c_ij|<1: with s=+/-1 for the directed A-to-B sign, c_ij=X_ij^2+s*(gamma_j-gamma_i)+t*(gamma_j-gamma_i)^2. The within-ring squared lengths are X_ij^2+t*(gamma_j-gamma_i)^2<1. Fix the extrinsic edge 01 on the z axis, r0=0 and r1=(0,0,L), L^2=w/4+c01. Each vertex is within distance <2 of its own ring anchor, by the ring paths. Let P_i be the two transverse coordinates and rho_i=2L*(z_i-L*I[i in B]). Comparing the squared distances to the anchor in the other ring yields |rho_i|<6, since these cross squared distances differ from L^2 by less than 2. Also |P_i|<2. Horizontal intrinsic lifts can be bounded using the fixed shifts and short-edge inequalities along graph paths.

Set lambda=1/(4L^2), so lambda*(1+4*t*c01)=t. With intrinsic physical horizontal lifts x_i, X_ij=x_j-x_i+K'_ij[0]+K'_ij[1]/2. For ring edges the exact metric equation is

    |P_j-P_i|^2 + lambda*(rho_j-rho_i)^2
      = X_ij^2 + t*(gamma_j-gamma_i)^2.

For A-to-B cross edges it is

    |P_j-P_i|^2 + (rho_j-rho_i) + lambda*(rho_j-rho_i)^2 + c01
      = X_ij^2 + s*(gamma_j-gamma_i) + t*(gamma_j-gamma_i)^2.

Here P0=P1=0, rho0=rho1=0. All actual realizations in this marking satisfy this bounded polynomial system for 0<t<=4/35. The normalized extrinsic coordinates (P_i,I[i in B]+2*lambda*rho_i) have the same affine incidence signs as the original ones. Thus the previous exact embedding constraints can be imposed in these coordinates, and intrinsic orientation/shortest-edge conditions in the intrinsic rescaled coordinates. This is a useful approach to the unbounded parameter range, not an assertion that all solutions of the metric equations are embedded.

At t=0, the correction equations in c01, the six rho_i, and seven gamma_i are linear of rank 14, leaving two residual quadratic identities. The four allowed clique-sign patterns have a special structure on the 4x4 matrix of determinants of oriented ring edge pairs: up to overall sign and a column permutation there is one positive entry in each row and column, with all other entries negative. In the limit these are weak signs of the cross products of the planar ring edge vectors. Because both sets of ring vectors sum to zero, this cross-product matrix has zero row/column sums. It is a balanced Laplacian with nonpositive off-diagonal entries after sign normalization, and rank <=2. If both sets span the plane, rank=2, so there are exactly two strongly connected components; balanced flow forbids edges between components and each connected Laplacian block has rank size-1. A 3+1 component partition forces a zero vector in each ring; a 2+2 partition forces pairs of opposite vectors in each ring. Thus if both limiting rings are simple nondegenerate planar quadrilaterals with no zero edges, they must be parallelograms (adjacent opposite vectors would retrace a segment). Otherwise degeneracies must be considered.

The naive t=0 relaxation is not infeasible: `verify_ring4.py` checks an explicit rational degenerate witness with gamma_i=0, all projected ring vectors collinear, and c01=1/16. It meets the metric equations, weak shortest-edge bounds, and weak clique signs, not actual embeddedness. A proof excluding t>0 would need to analyze departures from this limiting degeneracy, rather than simply asserting that the compact limit has no feasible points.

## 6. Reproduction and limits

Run with Python 3, assertions enabled, shared libz3, and SymPy (for the rank check):

```
python verify_linking.py
python verify_full_ring4.py
python verify_topology.py
python verify_ring4.py
```

The optional `search_ring4.py 4 1` uses SciPy and JAX and performs one local numerical search in each of the 16 full generic sign chambers at y=4. All 16 returned essentially zero separation margin (largest reported margin about 1.25e-13, with constraint violation of the same order). This is inconclusive; the search is not exhaustive over continuous parameters and strict full signs may omit nongeneric actual solutions. No numerical result is used as a proof.

The main new target is now to exclude or realize the two t7_ray_4 reconstruction branches on the compactified range. This does not resolve other Type 7 markings or the full Type 4/5/7 universality classification. No independent audit of the earlier papers or proof checkpoints is claimed.
