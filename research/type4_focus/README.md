# Type 4: eight-variable radical reduction

Status: proposed exact reduction of every Type 4 realization, for either sharp-rhombic marking, to eight continuous real parameters and at most 16 radical branches per parameter choice (up to rigid motions/reflection). This is **not** a Type 4 closure. It relies on the earlier strict-support and K4 nondegeneracy lemma, which still needs independent audit. No numerical feasibility assertion is made. This checkpoint attacks Type 4 independently of the ongoing Type 5 ledger.

## 1. Structure

Use the repository's oriented Type 4 faces:

    012 031 024 053 045 152 134 146 165 264 257 276 374 356 367 475

The graph has universal vertices 4,5. The core tetrahedron A=(4,5,1,6) is a K4. Vertices 2,3 are nonadjacent and are each adjacent to all four anchors. Vertices 0,7 are nonadjacent; their respective five neighbors are (1,2,3,4,5) and (2,3,4,5,6). Each has a five-cycle link. These statements follow directly from the face list; the edges are accounted for as 6+8+10=24.

Fix a lattice and marking, writing the physical lattice shifts as K_ij, antisymmetric, with the cocycle sum zero around every face. Gauge the lifts so K_4j=0 for every j (4 is universal), and set p_4=0 in the intrinsic plane and r_4=0 in extrinsic space. Every actual embedding has strict support at each vertex relative to its neighbors, and every K4 is noncoplanar, by the earlier orientation checkpoint. In particular any three consecutive vertices of any vertex link are noncollinear: if collinear, injectivity of their two consecutive edges puts their common vertex strictly between the other two, contradicting strict support there.

## 2. Six anchor parameters

Choose the intrinsic positions p_5,p_1,p_6 (six real scalars). The six squared edge lengths of A are fixed by these and K. Construct its extrinsic tetrahedron by its Gram matrix

    G_ik=(d_4i+d_4k-d_ik)/2, i,k in (5,1,6).

Reject unless G is positive definite; otherwise Cholesky factorization gives a unique tetrahedron up to ambient isometry, using rational arithmetic and positive square roots. Write R for the 3x3 matrix with rows r_i, i in (5,1,6); R is invertible. No extrinsic rotation variable is needed.

## 3. Two conics, one parameter each

For j=2,3, put u=p_j, v=r_j and s_i=p_i-K_ij for i in (5,1,6). Subtract the edge equation to 4, namely |v|^2=|u|^2, from the other three. This gives

    r_i . v = s_i . u + (|r_i|^2-|s_i|^2)/2.

Thus v=L_j u+b_j, where L_j=R^(-1)S_j and b_j=R^(-1)c_j; S_j has rows s_i and c_j has entries (|r_i|^2-|s_i|^2)/2. The entire four-edge condition for j is exactly the plane conic

    q_j(u)=|L_j u+b_j|^2-|u|^2=0.

This polynomial is not identically zero. Otherwise its constant term gives b_j=0, its quadratic part gives L_j^T L_j=I, and the linear equations defining L_j and b_j give s_i=L_j^T r_i and |s_i|=|r_i| for all three anchor rows. Orthogonal projection to im(L_j) would preserve the norms of all r_i, forcing all three independent r_i into a plane, a contradiction.

For a nonconstant quadratic q choose deterministically the first direction d among (1,0),(0,1),(1,1) with d^T (L^T L-I)d != 0. Such a direction exists whenever the quadratic part is nonzero. Set u=t e+h d with e a fixed complementary coordinate direction; t is the one free scalar and h is given by the quadratic formula (discard negative discriminants). If the quadratic part vanishes, solve the nonconstant linear equation along a coordinate with nonzero coefficient instead. A nonzero constant gives no solution. This covers degenerate conics, double roots and lines as well as nonsingular conics; no leading coefficient is divided by without checking it is nonzero. Each j has at most two solutions for each t. As 2 and 3 are nonadjacent their reconstructions are independent.

## 4. Degree-five leaves: no further continuous variables

For j=0,7 let u=p_j, v=r_j. Again subtract the equation to 4 from the four other neighbor equations:

    r_i . v - s_i . u = (|r_i|^2-|s_i|^2)/2.

The four rows form a 4x5 system for (v,u). They have rank at least three: the neighbor set contains the K4 (1,2,4,5) for 0 and (2,4,5,6) for 7, so its vectors r_i relative to 4 span R^3.

For actual embedded flat tori rank is four. To see this, suppose rank three, so there is a linear map L:R^3->R^2 with s_i=L r_i (also true for i=4 with s_4=r_4=0). At the leaf put U_i=r_i-v and W_i=s_i-u=L U_i+b, b=L v-u. All neighbor vectors have equal intrinsic and extrinsic lengths. For each successive pair in the five-cycle link, the opposite edge also has equal length, because the face cocycle makes its intrinsic displacement W_i-W_k. Consequently the five projective lines through the successive points (U_i,1) lie in the homogeneous quadric

    Q(U,t)=|U|^2-|L U+b t|^2=0.

Consecutive lines are distinct by the strict-support observation in section 1. If b!=0, align an intrinsic coordinate with b and absorb its affine term into t. The form is congruent to |U|^2-ell(U)^2-t^2, of rank at least three. If b=0 and rank at most two, the nonzero form in U has zero set contained in a plane or a union of two planes through the origin (the rank-zero case is impossible since L maps into dimension two). Every leaf face lies in that zero set by homogeneity and the edge identity. A planar star is forbidden by minimality. If both planes occur, transitions must be incident edge rays on their common line; there must be at least two distinct rays by the cyclic link, hence antipodal rays, forbidden by strict support. Rank three gives a projective quadric whose real lines all pass through its unique singular point: the nondegenerate three-dimensional quotient has maximal isotropic dimension at most one. Thus a regular link vertex cannot have two distinct incident lines; the five distinct link points cannot all be singular. Rank four admitting real lines must have signature (2,2), with its two projective line rulings. Distinct intersecting lines must alternate rulings, impossible on the odd five-cycle. Rank three of the linear system is therefore impossible.

Choose any nonzero 4x4 pivot minor of the four linear equations; their solution set is an affine line (v,u)=(v0,u0)+t(e,d). Restrict |v|^2-|u|^2 to this line. It cannot vanish identically if the line contains an actual embedded solution: identically zero would imply |e|=|d|>0 and e.(r_i-v)=d.(s_i-u) for every neighbor (using both the linear equations and derivative of the quadratic). In every incident face the isometry maps d to a vector with the same norm in its plane. Its inner products with the two independent edge vectors are those of e, so this vector is the orthogonal projection of e to the plane. Equal norms force e into every incident face plane. Any transition between distinct planes uses an edge parallel to e. A nonplanar star would need two opposite such rays, prohibited by strict support. A planar star is also impossible. This proves the nonzero quadratic assertion. Constant nonzero polynomials are infeasible; a linear polynomial has at most one root. Reject an identically zero leaf polynomial as incapable of containing an embedded flat realization. Hence each leaf has at most two choices. Leaves 0,7 are nonadjacent.

## 5. Exact coverage and remaining tests

There are six anchor parameters and two conic parameters, with at most 2^4=16 radical combinations for each parameter choice, up to ambient reflection. Deterministically selected conic directions and pivot minors are finite semialgebraic charts, not extra continuous variables. Every Type 4 embedding is recovered by some parameter choice; all 24 edge length equalities hold by construction. Conversely, a candidate is an embedding only after checking nondegenerate consistently oriented intrinsic faces, marking/degree one, and exact disjoint-simplex exclusions, including degeneracies. Strict nearest-lift and clique determinant conditions can be added as necessary filters.

At fixed metric the eight parameters are bounded: after the gauge K_4j=0 every intrinsic position is in the bounded Voronoi cell, including each root parameter t which is a fixed linear coordinate of u. This avoids an unbounded coordinate search. On the sharp-rhombic ray the modulus itself remains unbounded and needs separate handling. Near singular pivots the reconstruction must use certified charts or polynomial auxiliaries; a numerical failure or exclusion away from singularities is not a proof.

This improves the previous 14-intrinsic-variable spanning-3-tree system, which retained six unsolved metric equalities, to eight free continuous parameters and no residual edge-length equalities. The new target is the single hexagonal marking: find an exact embedded witness or exclude the full bounded semialgebraic reconstruction. The Type 5 radical argument in research/torus_type5_reconstruction_certificate/type5_algebraic_certificate is the source of the odd-link quadric idea; the two-conic core here is specific to Type 4.

No full nonlinear feasibility problem has yet been solved in this checkpoint.

## 6. Hexagonal symmetry: 31 necessary clique-sign classes

The two sharp-ray markings become equivalent at the hexagonal endpoint, by the lattice isometry with row-vector matrix ((0,1),(-1,1)) from the second representative to the first, followed by a vertex-lift gauge. All four Type 4 automorphisms are compatible with the first marking up to a hexagonal lattice isometry and a gauge. The four vertex permutations and their compensating matrices are:

| permutation (images of 0,...,7) | lattice matrix |
|---|---|
| 01234567 | ((1,0),(0,1)) |
| 01325467 | ((1,-1),(0,-1)) |
| 76235410 | ((-1,0),(0,-1)) |
| 76324510 | ((-1,1),(0,1)) |

The verifier checks these claims by comparing integer edge cocycles: the difference after relabeling and applying the lattice matrix must be a vertex coboundary. The 12 matrices are exactly the symmetries of the Gram form ((2,1),(1,2))/2. Each permutation acts on signed clique determinants by permutation parity and normalization by ambient reflection. The 120 necessary Type 4 clique patterns in the preceding SAT archive split into 29 orbits of size four and two of size two, totaling **31** classes. This is a joint marking/orientation quotient, rather than an unjustified independent quotient by graph symmetry. Run `python3 research/type4_focus/verify_hex_orbits.py` to enumerate the exact H01--H31 representatives; it reads the previously checked clique pattern archive. The enumeration was also executed in integer arithmetic in the research environment; the saved Python script is an equivalent standalone replay, not an independent audit of the previous SAT or geometric lemmas.

For each H01--H31, use the eight-parameter reconstruction and test the prescribed clique signs, complete embedding (including nonclique coplanarity), and intrinsic face orientations and degree. This is an exhaustive *necessary* branch decomposition at the fixed hexagonal metric. Each branch still contains a continuous feasibility problem; none is certified infeasible and no embedded witness has been obtained. A full exclusion of all 31 would establish Type 4 nonuniversality; a single positive witness would settle just this modulus.

## 7. Exploratory numerical check (not an exclusion)

A vectorized floating-point implementation of the two-conic and two-leaf reconstruction was tested on a seeded hit-and-run sample of 80,000 intrinsic points in the strict nearest-lift polytope, using their anchor coordinates and sampled root parameters. The best reconstructed candidate meeting strict intrinsic face orientation and nearest-lift checks still had six disjoint edge-face crossings (largest squared edge-length residual about 7.1e-16). A local constrained optimization over 30 nearby SAT sign models produced zero or slightly negative determinant/face/shortest-lift margins, not a certified embedding. These are exploratory computations, not proof certificates; no conclusion about infeasibility follows. The mathematical reduction and exact discrete symmetry checks do not depend on these experiments.

## 8. Affine-coordinate implementation for rigorous solving

The anchor Cholesky radicals need not enter feasibility solving. Write the ambient position of any vertex in the anchor basis, r_i=R^T c_i, with c_4=0 and c_5,c_1,c_6 the coordinate unit vectors. Then all squared extrinsic lengths are (c_i-c_j)^T G (c_i-c_j), where G=R R^T is the positive-definite Gram matrix already determined by the six anchor parameters. Every 4-point determinant has the sign of the corresponding affine-coordinate determinant after fixing a positive anchor orientation. For a root j, the equations become

    G c_j = S_j u + b'_j,
    c_j^T G c_j = |u|^2,

where b'_j has entries (G_ii-|s_i|^2)/2. This is the same conic using only rational functions of the anchor data. For a leaf j, subtracting the equation to 4 similarly yields

    c_i^T G c_j - s_i . u = (c_i^T G c_i-|s_i|^2)/2.

The rank and nonzero-polynomial proofs above are unchanged by this invertible linear change of coordinates. For leaf 0 the three neighbors (1,2,5) span the anchor coordinates because (1,2,4,5) is a K4; for leaf 7 use (2,5,6). Solve these three equations for c_j as an affine function of u, then the fourth equation is a nontrivial linear constraint on u by rank four. Solve that line using a nonzero pivot and enforce its one remaining quadratic. Thus only four univariate quadratic equations remain in addition to the eight independent real parameters. Keeping the four dependent scalars as algebraic variables avoids expanding nested square roots; all extrinsic coordinates are rational functions of the resulting twelve scalars, and all edge equations hold exactly when the four quadratic equations hold. The parameter count refers to free scalars, not the number of variables in an auxiliary polynomial encoding. The complete degeneracy-aware embedding constraints can be tested in c-coordinates, with no Cholesky calculations. This is a natural representation for interval arithmetic or exact sign elimination.

## 9. Full determinant-sign model enumeration

Run `python3 research/type4_focus/enumerate_hex_models.py` (requires libz3). The script enumerates the necessary generic Boolean models over each canonical clique representative, explicitly removing the old first-determinant reflection normalization in favor of the first clique sign. Each enumeration terminates in UNSAT after blocking the primary assignments. The local equivalent enumeration returned the following counts, totaling **2,405** models across the 31 representatives (not necessarily distinct under stabilizers of each clique orbit):

| Branch | Full generic models | Status |
|---|---:|---|
| H01 | 26 | Unresolved |
| H02 | 25 | Unresolved |
| H03 | 108 | Unresolved |
| H04 | 76 | Unresolved |
| H05 | 51 | Unresolved |
| H06 | 202 | Unresolved |
| H07 | 151 | Unresolved |
| H08 | 27 | Unresolved |
| H09 | 191 | Unresolved |
| H10 | 86 | Unresolved |
| H11 | 13 | Unresolved |
| H12 | 15 | Unresolved |
| H13 | 1 | Active; not excluded |
| H14 | 103 | Unresolved |
| H15 | 33 | Unresolved |
| H16 | 72 | Unresolved |
| H17 | 20 | Unresolved |
| H18 | 242 | Unresolved |
| H19 | 6 | Unresolved |
| H20 | 166 | Unresolved |
| H21 | 21 | Unresolved |
| H22 | 10 | Unresolved |
| H23 | 26 | Unresolved |
| H24 | 34 | Unresolved |
| H25 | 18 | Unresolved |
| H26 | 157 | Unresolved |
| H27 | 18 | Unresolved |
| H28 | 420 | Unresolved |
| H29 | 22 | Unresolved |
| H30 | 44 | Unresolved |
| H31 | 21 | Unresolved |

The smallest branch H13 has the sole full sign string `-++-++--++--+-+--+-++++--++-+-+++++-++--+--+--+--++--+-+-++--+--++----` in lexicographic four-subset order. In metric feasibility tests impose strict signs on the 23 cliques, weak signs on the other 47 determinants. This preserves possible coplanar nonclique configurations by the generic perturbation argument. An exploratory exact-coefficient QF_NRA relaxation of H13 (32 geometric coordinate variables, 356 polynomial assertions, edge equations, nearest-lift inequalities, oriented intrinsic faces, determinant signs and nonedge distance bounds) returned unknown/timeout at 10 seconds. It did not include the complete degeneracy-aware embedding tests, so even a SAT result would require further checks. No sign model or clique class was excluded. The next step is rigorous interval or algebraic elimination in the reduced eight-parameter affine-coordinate formulation, starting with H13, not further blind subdivision of the modulus ray.


## 10. H13: metric-only obstruction remains; universal-edge elimination

H13's singleton sign model is genuinely realizable by a generic embedded (not necessarily flat) polyhedral Type 4 torus. The new integer witness, in vertex order 0--7, is

    (1000,0,0), (0,1000,0), (3176,2372,-5000), (608,3405,-2561),
    (0,0,0), (0,0,1000), (452,5000,-3294), (1155,720,-1328).

All 70 determinants have the required strict signs, with minimum absolute determinant 449984000 in these integer coordinates. Exact circuit checks establish all 140 disjoint edge/face exclusions and 140 neighbor-support tetrahedron exclusions, and the mixed-side conditions at all eight vertices. In general position these imply simplicial embeddedness and strict support relative to neighbors. Reproduce with `python3 research/type4_focus/verify_h13_sign_witness.py`. The witness is for signs alone, not an isometric hexagonal torus. In particular, adding more necessary orientation-only relations cannot exclude the H13 model: its signs already come from a real embedded vertex configuration.

### Universal-edge Gram formulation

Fix the hexagonal marking and gauge K_4j=0. Let d_ij denote **squared** intrinsic edge lengths (d_ii=0). Vertices 4,5 are universal; L=d_45>0. After rotating physical 3D coordinates so r_4=0 and r_5 lies on the positive z axis, scale all coordinates by 2 sqrt(L). The scaled axial coordinate of vertex i is

    a_i=L+d_4i-d_5i.

For W=(0,7,2,3,6,1), write s_i for the two transverse coordinates of vertex i in this scaled realization. Their prescribed Gram entries, including diagonal entries, are

    C_ij=2 L (d_4i+d_4j-d_ij)-a_i a_j.

These are known whenever i=j or ij is an edge. Because 0145 is a K4, s_0 and s_1 form an independent basis, with positive-definite Gram matrix G=[[C_00,C_01],[C_01,C_11]]. The H13 sign of det(4,5,0,1) is positive. Write s_i=b_i[0] s_0+b_i[1] s_1. Then b_0=(1,0), b_1=(0,1), b_4=b_5=0. The prescribed 14 remaining Gram equations are precisely b_i^T G b_j=C_ij. Edge equations from vertices 4 and 5 follow from the axial coordinate formula and the diagonal Gram equations. Thus only 14 intrinsic variables and eight transverse coefficients are needed.

For every pair i,j in the indicated order W, the sign model gives det(4,5,i,j)>0 in generic position. For actual configurations we impose strict positivity for clique quadruples, weak positivity otherwise. Hence the transverse rays lie in the closed cone between s_0 and s_1, and their pairwise ordered determinants are nonnegative, strictly positive on the specified clique pairs. We do not require general position of noncliques. All other H13 determinant signs are read in the affine coordinates (b_i,a_i); the coordinate change has positive determinant. The 22-variable exact relaxation has 362 assertions (including redundant angular-order assertions), strictly shortest intrinsic lifts, consistently oriented nondegenerate intrinsic faces, the 70 required strict/weak signs and nonedge chord bounds for 25 lattice translates per nonedge. The exact-coefficient Z3 run at 15 seconds returned UNKNOWN (timeout); no branch exclusion follows. Reproduce with `python3 research/type4_focus/h13_edge45.py 15000`. Full degenerate simplex intersection tests are not included, so a relaxed SAT answer would still need verification.

### Fraction-free intrinsic-only reduction (mathematical)

The eight transverse coefficients can also be eliminated without radicals or selecting quadratic roots. In order, recover b_2,b_3 using their Gram entries with (0,1), recover b_6 with (2,1), then b_7 with (2,6). All those pairs, together with 4,5, form cliques and have the required strictly positive ordered determinants. All used distances exist. Each step has two linear equations

    [b_j^T G; b_k^T G] b_i = (C_ji,C_ki)^T.

The determinant of the coefficient matrix is det(G) det(b_j,b_k)>0. These eight equations therefore uniquely reconstruct all b's from the 14 intrinsic coordinates. Exactly six residual Gram equations remain. To evaluate them without division, maintain b_i=N_i/D_i with D_i>0. For a new i let the rows of A be N_j^T G,N_k^T G and set

    D_i=det(A),
    N_i=adj(A) (D_j C_ji,D_k C_ki)^T.

All denominators are positive on the required chart, and the six residual equations are N_i^T G N_j=D_i D_j C_ij. For affine determinant tests use homogeneous rows (D_i,N_i[0],N_i[1],D_i a_i), whose row-scaling factors are positive. The same numerator/denominator convention clears denominators in nonedge squared-distance comparisons. This gives a single rational reconstruction chart for H13 with 14 intrinsic coordinates and six residual equations, an alternative to the eight-free-parameter radical chart. It is intended for exact sign/interval elimination; expanding the recursively generated polynomials may be expensive. No claim that the 14-variable form is uniformly faster is made.

### Additional strict volume tests

The unique generic sign model has singleton circuits including 7 inside tetrahedron 0245, and 3 inside each of tetrahedra 1246, 2456, 2467. For a possibly nongeneric actual H13 realization, the weak-sign closure places the singleton in the closed corresponding tetrahedron: the containing tetrahedra are K4s and nondegenerate. In each case the shared-base replacement is also a K4. Thus the absolute volume of the replacement tetrahedron is positive and at most the original volume. In fact it is strictly smaller: equality would give barycentric coefficient one for the opposite vertex, forcing coincidence of two distinct vertices. Hence the following four inequalities hold even in the weak-sign closure:

    Vol^2(0245)>Vol^2(2457),
    Vol^2(1246)>Vol^2(1346),
    Vol^2(2456)>Vol^2(3456),
    Vol^2(2467)>Vol^2(3467).

Every quantity here is a polynomial in the intrinsic coordinates via the clique distance Gram determinant (common factor 1/36 if using Euclidean tetrahedron volumes). These are branch-specific metric inequalities available without extrinsic unknowns.

### Experimental status

A separate orthogonal-transverse-coordinate formulation (25 variables, 17 residual edge equations) was tried numerically using JAX Jacobians and SLSQP. Twenty generic-margin starts and 100 starts with nonclique/nonedge inequalities weak yielded no strict feasible witness. An additional 30 starts in tetrahedral affine coordinates, seeded with the sign-only witness, also yielded none. These searches are not exhaustive, and weak margins/near-degenerate configurations are not certificates. The scripts for these exploratory searches are not relied upon for any theorem. The exact sign witness and exact polynomial relaxation are the reproducible results of this iteration. H13 remains open; all 31 classes and the Type 4 universality classification remain unresolved.


## 11. H13: exact exclusion of 40 determinant degeneracies

**Status:** H13 remains open. The following is a necessary strengthening of its metric feasibility system, not a nonexistence certificate.

Let (D_Q) be the affine determinant of a sorted quadruple. In the weak closure of the H13 sign model, its assigned sign is weakly satisfied. Initially the 23 clique determinants are strict by the strict-support/K4 lemma. The following finite rule propagates strictness, without assuming general position of noncliques.

Suppose (D_Q=0). Choose a fifth vertex (w) and put (C=Q\cup\{w\}), in sorted order. If one replacement determinant (D_{C\setminus\{v\}}), (v\in Q), is already known strict, the five augmented point columns have rank four. Their signed cofactor dependence is nonzero; the coefficient at (w) is zero and each of the other coefficients is either zero or has its H13 cofactor sign. The nonzero coefficients must sum to zero. If their prescribed positive and negative sets are disjoint simplices, normalizing the coefficients gives a forbidden intersection of their subfaces. If either set is a singleton and the other consists of neighbors of that singleton, the dependence contradicts strict neighbor support. A single-sign set is impossible as well. Thus (D_Q) must be strict whenever this rule applies.

[verify_h13_strict.py](verify_h13_strict.py) checks this rule with only integer sign arithmetic. Two rounds force 35 and then 5 additional strict determinants, for 63 in total. The only determinants not proved strict are

    0147 0237 0256 0257 0467 1247 1357

The rule checks that all 24 quadruples obtained by uniting the two incident triangles at an edge are strict. In particular **all 24 edges are genuine creases**, even for a nongeneric H13 flat embedding. The original 23 strict signs are a premise, not a new proof of the earlier geometric reduction.

### Strict nonedge chord contraction

Let (i,j) be distinct nonadjacent vertices. If their extrinsic chord length equaled their intrinsic distance, an intrinsically shortest path would map to the straight chord (equality in Euclidean path length). It cannot pass through a third vertex: the two local chord rays would be antipodal, whereas the entire incident star has strictly supported directions. A straight intrinsic geodesic entering a face and crossing an edge transversely cannot stay straight extrinsically when the adjacent face planes differ. A geodesic locally along an edge continues along that edge until a vertex, which is already excluded. Thus a path mapping to a straight chord would have to lie in a single triangle or a single edge, impossible for nonadjacent vertices. Hence all four nonedge chords are strictly shorter than their intrinsic distances, and positive by injectivity.

At the hexagonal modulus in gauge (p_4=0, K_{4j}=0), each (p_i) lies in the open nearest-lift Voronoi cell. If a translate of (p_j-p_i) by the lattice vector (k=(a,b)) is nearest, it lies in the closed cell. The three integral strip coordinates of (k), (2a+b,a+2b,a-b), have absolute values strictly less than 3 and therefore at most 2. Exhaustive integer arithmetic leaves just the zero vector and the six unit lattice vectors. This proves that seven comparisons per nonedge suffice, rather than the previous 25-shift sample. No nearest lift is missed, including ties.

The updated [h13_edge45.py](h13_edge45.py) uses the 63 strict signs, all seven strict nonedge distance bounds, positive nonedge squared distances and the four strict volume comparisons. It has 22 real variables and 298 assertions (previously 362). A local equivalent generator produced the stated counts and was passed to libz3; the run was terminated by the external 15-second time limit, with no SAT/UNSAT answer. This is not a solver-certified infeasibility result.

### A checked limitation of a curvature relaxation

For a generic height direction, let (I_v=1-c_v/2), where (c_v) counts sign changes between consecutive neighbors in the cyclic link of (v), relative to the height of (v). Crofton's formula gives average (I_v=1-\theta_v/(2\pi)) for cone angle \(\theta_v\). Any total height order has every prefix strictly separable from its complement. Reject an order if a full-sign affine circuit of five points has its positive and negative supports in opposite sides of a cut. This is necessary even in the weak-sign closure: an actual strict height order persists under a sufficiently small generic perturbation that realizes a permissible sign model. The cut filter leaves 128 forbidden masks, 3298 orders, and 210 distinct index vectors, counting both height directions.

This coarse relaxation cannot give a nonzero weighted curvature inequality: it contains the following seven pairs of opposite index vectors. Each row gives the two height orders realizing opposite *relaxed* index vectors, not necessarily realizable orders in a particular geometry.

| order | opposite order |
|---|---|
| 02516374 | 51027436 |
| 02517436 | 42367015 |
| 02563741 | 54103726 |
| 02741356 | 15026374 |
| 04572136 | 15076342 |
| 06231574 | 15047632 |
| 07234165 | 23705164 |

The seven index vectors obtained from the first column, dropping coordinate 0, have determinant 2. Thus their span is the full sum-zero subspace. Any weight nonnegative on all relaxed index vectors is orthogonal to each pair and is constant, yielding only the Euler-characteristic identity. This excludes the proposed *linear weighted-index certificate using only the cut filter*, not all curvature-based methods. Enumeration and rank were checked locally with Python and exact integer/rational arithmetic.

A separate 12-start floating-point least-squares search varied the full extrinsic configuration, imposing zero cone deficits and penalizing violation of the H13 generic signs, without prescribing the hexagonal modulus. No strict flat witness was obtained; some residuals approached zero with sign violations. This does not rule out even generic flat H13 realizations, much less weak-sign ones. Do not treat it as an exclusion.

**Next gate:** a verified positive or negative metric result for H13. All 31 hexagonal classes remain unresolved; do not count 40 excluded determinant degeneracies as 40 excluded orientation models. The new strictness and chord lemmas are rigorous conditional consequences of the earlier embedding/marking reduction, which still needs audit.


## 12. Intrinsic-only angular-cycle reduction and exact relaxed witness

This iteration keeps H13 active. The angular order around the universal edge 45 is strict on all fifteen pairs by section 11, including pairs whose corresponding quadruples are not cliques. In the positively oriented transverse plane the six rays occur in the order

    0,7,2,3,6,1

inside an angular interval of width strictly less than pi. Retain the definitions L=d_45, a_i=L+d_4i-d_5i, and C_ij=2L(d_4i+d_4j-d_ij)-a_i a_j. For every transverse vertex require C_ii>0; for every one of the 11 edges among these six vertices require Delta_ij=C_ii C_jj-C_ij^2>0. Write the unique gap alpha_ij=arccos(C_ij/sqrt(C_ii C_jj)) in (0,pi), oriented by the given order.

The six complete transverse triangles, with vertices in angular order, are

    (0,2,1), (0,3,1), (7,2,6), (7,3,6), (2,6,1), (3,6,1).

For each i,j,k in this order, alpha_ij+alpha_jk=alpha_ik is equivalent to the following purely algebraic conditions:

* The 3x3 principal determinant of C on i,j,k is zero.
* C_ij C_jk-C_jj C_ik>0.
* C_ij/sqrt(C_ii)>-C_jk/sqrt(C_kk).

Indeed the determinant equality gives (C_ij C_jk-C_jj C_ik)^2=Delta_ij Delta_jk; the positive sign selects the cosine addition identity, and the final inequality ensures that the sum of the two angles is strictly less than pi. The last test can be written as a three-case polynomial disjunction using signs and squared comparisons, since both denominators are positive.

The tree with edges 02,26,61,72,36 fixes all angle differences. In sequence the six triangle equations recover the remaining edges 21,01,31,03,76,73. Thus no additional angular cycle equation is required. The two missing adjacent comparisons are alpha_72<alpha_02 and alpha_36<alpha_26. With these, the tree angles are strictly increasing in the stated order, and the equation on edge 01 ensures width < pi. Conversely these equations reconstruct the unique transverse configuration up to rotation, with s_i=sqrt(C_ii)(cos theta_i,sin theta_i), theta_0=0. Together with axial coordinates a_i, this satisfies all 24 squared edge lengths (after undoing scale 2 sqrt(L)). This is an exact equivalence for the metric and edge-45 angular order, not for the other H13 signs or embeddedness.

The standalone generator [h13_angular_cycles.py](h13_angular_cycles.py) implements these conditions in 14 intrinsic real variables, with 198 assertions including nearest-lift and face orientation constraints. No extrinsic-coordinate unknowns, high-degree rational reconstruction denominators, or transcendental functions occur in this relaxation. A local run of the same script with libz3 and a 5000 ms limit returned UNKNOWN (timeout).

### The relaxation is actually feasible

A numerical search in the six-cycle formulation found a strict metric/angular candidate. The new [verify_h13_angular_relaxation.py](verify_h13_angular_relaxation.py) replaces that approximation by an exact radical construction, using the eight-parameter core/leaf method of sections 1--5. Six anchor coordinates and the first coordinates of roots 2 and 3 are exact rationals. The remaining four quadratic roots are selected with signs (+,-,-,+) in vertex order (2,3,0,7). Integer-endpoint outward-rounded intervals on the 2^-200 grid check the reconstruction pivots, positive discriminants, positive-definite anchor Gram matrix and all strict geometric inequalities. The branch selection uses numerical midpoints only to choose one of two exact radicals, not to justify any asserted sign. All 24 edge equalities hold algebraically, by solving the linear equations and the four quadratics.

The local verifier returned:

    radical branch indices (0=positive sqrt) [(2, 0), (3, 1), (0, 1), (7, 0)]
    minimum intrinsic face double-area bound 0.07851660003335041
    minimum nearest-lift slack bound 0.0011524672433112825
    minimum nonedge squared chord slack bound 0.0006744159399265299
    H13 mismatched signs 17 crossing circuits 10
    PASS exact angular/metric relaxation witness; NOT embedded and NOT in H13

The period cocycle and consistent nondegenerate intrinsic face orientations certify the hexagonal domain metric. All 15 transverse angular signs, all seven nearest-lift nonedge chord comparisons per nonedge, and all 70 generic determinant nonzero tests pass. However, 17 other H13 signs disagree (including clique signs 2567 and 3567), and ten disjoint edge/face intersections are certified by the five-point circuits.

Consequently the 198-assertion relaxation is genuinely SAT, even though the nonlinear solver did not discover that fact. Adding the nonedge chord bounds and requiring generic configurations still cannot make this relaxation infeasible. Do not try to prove its UNSAT. The remaining H13 signs and embeddedness constraints are essential. An exploratory six-start full angular reconstruction search found no strict feasible configuration; a three-start refinement with clique signs alone (one initialized at the exact relaxation's numerical precursor) likewise found none. Neither is an exclusion certificate. The searches were floating point and are not premises of the exact witness.

**Status:** no H13 closure, no additional orientation branch closed. The six triangle equations offer a denominator-free local formulation, and the exact radical witness identifies which relaxation is inadequate. Future work must retain the remaining sign constraints (in particular the two mismatching cliques for this witness), or obtain a global metric obstruction at another modulus; further solving the proven-feasible relaxation is not productive.


## 13. Complete H13 polynomial system with five positive radicals

The 63 strict and seven weak signs actually suffice for simplicial embeddedness in this particular chamber. To see this, an intersection of disjoint simplices would give a support-minimal sign-compatible affine dependence on at most five distinct vertices. Every triple of vertices has a strict quadruple extension, as checked by enumeration, so there are no coincident or collinear vertices and the support has size four or five.

For five-point support, all five four-point cofactors are nonzero and their signs determine the unique Radon partition. The 56 five-subsets are checked against the prescribed H13 signs: none splits into two disjoint simplices. For four-point support, the dependent quadruple is one of the seven allowed zeros. Because a clique tetrahedron is nondegenerate, some fifth vertex is off its plane. Appending that vertex, the cofactor associated with the extra vertex is zero and the other four cofactors are nonzero. Their prescribed signs give the four-point circuit partition. Checking all seven quadruples and all four possible extra vertices (28 tests) rules out every partition into disjoint simplices. This also covers simultaneous zero determinants; no genericity assumption is needed. Thus the exact strengthened H13 sign conditions exclude all unwanted simplex intersections.

To reconstruct the transverse coordinates algebraically from section 12, use five positive variables t_ij satisfying t_ij^2=Delta_ij on the chosen tree edges. With the transverse plane identified with C, multiply all transverse positions by sqrt(C_00) (a positive factor). Start with z_0=C_00. Along each oriented tree edge i->j set

    z_j = z_i (C_ij + i epsilon_ij t_ij) / C_ii,

where epsilon_ij=+1 for increasing angular order and -1 for decreasing angular order. Since every denominator is positive, write z_i=(X_i+iY_i)/D_i with polynomial numerators and positive denominators. The complete three-dimensional coordinates are given by (X_i/D_i,Y_i/D_i,a_i), after the positive transverse rescaling. A tetrahedral determinant is computed from the three difference vectors relative to its first vertex, each multiplied by the corresponding product D_i D_j. The signs are unchanged. The physical nonedge squared chord comparisons also become polynomial after clearing positive denominators and undoing the transverse scaling.

[h13_angular_full.py](h13_angular_full.py) implements this full system: 14 intrinsic variables and five positive square-root auxiliaries, with 310 assertions including all 70 strict/weak determinant signs and the four nonedge chord bounds for seven translates each. Subject to the earlier winding, strict-support and sign-reduction audit, it is necessary and sufficient for an embedded hexagonal realization in H13; a SAT solution would itself settle the hexagonal metric positively, and a proved UNSAT result would close H13. Unlike the earlier 22-variable relaxation, no additional degenerate simplex intersection check is required mathematically. It is still a high-degree polynomial system, and fewer variables do not guarantee easier solving.

Reproduced locally:

    variables 14 assertions 198
    PASS all 56 five-point and 28 four-point circuit sign tests
    full variables 19 assertions 310
    UNKNOWN timeout

The final line is the libz3 result at 5000 ms; the circuit enumeration passed, but the metric system remains unresolved. The earlier exact angular-relaxation witness does not satisfy this complete system. No branch closure is claimed.


## 14. Hand proof: a sharp convex-hull bound for linked short fibers

This checkpoint uses mathematical reasoning only: no SAT enumeration, numerical optimization, nonlinear solver, interval search or computer-assisted proof. The aim is an obstruction valid on a whole modulus interval rather than more subdivision of H13 at one metric. It strengthens the earlier linking checkpoint's threshold, but does not settle the hexagonal metric.

### Lemma (three intersecting convex hulls)

Let C_1,C_2,C_3 be simple closed rectifiable curves in Euclidean 3-space, each of length at most L. Suppose their convex hulls intersect pairwise. If x_i belongs to conv(C_i), the perimeter of the triangle x_1 x_2 x_3 is strictly less than

    (3 sqrt(3)/2) L.

Proof. Any triangle with vertices in conv(C_i) has perimeter at most L. Indeed, the perimeter is convex in each of its three arguments separately. Express each of its vertices as a finite convex combination of points on C_i and apply convexity in all three arguments. Each resulting triangle on the curve has perimeter at most its length, by traversing the three intervening arcs. Also diam(conv(C_i))=diam(C_i)<L/2: between any two distinct points on a simple closed curve there are two arcs, and equality of their lengths with the chord would force the two arcs to coincide.

Choose p_12, p_23, p_31 in the respective pairwise intersections. For i=1,2,3 with indices cyclic, let m_i be the midpoint of p_(i-1,i) and p_(i,i+1), and let d_i be their distance. The triangle perimeter bound just proved gives

    |x_i-m_i| <= (|x_i-p_(i-1,i)|+|x_i-p_(i,i+1)|)/2
               <= (L-d_i)/2,

and 0<=d_i<L/2. The medial triangle on the m_i has perimeter (d_1+d_2+d_3)/2, including the degenerate case.

If the x-triangle is degenerate, each of its pairwise distances is strictly less than L by going through the corresponding intersection point, so its perimeter is strictly less than 2L. Otherwise let A_i be its interior angles, u_i=(x_(i+1)-x_i)/|x_(i+1)-x_i|, and P its perimeter. Expanding the identity P=sum_i <u_i,x_(i+1)-x_i> around m_i gives

    P <= perimeter(m_1,m_2,m_3) + sum_i |u_(i-1)-u_i| |x_i-m_i|
      <= (d_1+d_2+d_3)/2 + sum_i (L-d_i) cos(A_i/2)
       = L sum_i cos(A_i/2) + sum_i d_i (1/2-cos(A_i/2)).

Here |u_(i-1)-u_i|=2 cos(A_i/2). If every A_i<=2 pi/3, all the d_i coefficients are nonpositive. Concavity of cosine on [0,pi/2] and sum A_i=pi yield

    P <= L sum_i cos(A_i/2) <= (3 sqrt(3)/2) L.

Equality would require all A_i=pi/3 and all d_i=0. In that case the three intersection points coincide at a point p, and |x_i-p|<L/2 by strict diameter of conv(C_i); the perimeter estimate is therefore strict.

If one angle A_i>2 pi/3, write c=cos(A_i/2)<1/2. The other two angles have cosine of half-angle at most 1 and at least 1/2. Dropping their nonpositive d-terms and using d_i<=L/2 gives

    P <= L(c+2) + (L/2)(1/2-c)
       = L(9/4+c/2) < (5/2)L < (3 sqrt(3)/2)L.

This proves the lemma without a general-position assumption. The constant is optimal for the abstract pairwise-convex-hull relaxation if degenerate doubled segments are allowed as limits: take three segments of length L/2 from a common point in coplanar directions 120 degrees apart, with x_i their outer endpoints. Thus improving the bound further requires additional geometry, not just the pairwise intersection and length premises.

### Consequence for every embedded flat torus with linked short fibers

Let h be a primitive lattice period and L=|h|. Suppose the linking number of two distinct parallel h-geodesics is nonzero. Every such fiber is a simple closed curve of length L, and the linking number is the same for every distinct pair (up to a common orientation convention), since the ordered pair of distinct parallel fibers can be moved continuously on the torus. Two linked curves have intersecting convex hulls: disjoint convex hulls admit a strict separating plane and hence have zero linking. For any three points of the torus, take their three h-fibers, using the same curve for repeated fibers. Their hulls intersect pairwise, so the lemma applies.

In particular, every three-edge cycle of the triangulation has perimeter strictly less than (3 sqrt(3)/2)L. Its intrinsic perimeter equals its extrinsic perimeter by facewise isometry. If its period is g, its lifted path has length at least |g| by the Euclidean triangle inequality. We obtain the global necessary condition

    |g| < (3 sqrt(3)/2)|h|

for every triangular cycle whenever q(h)!=0.

On the sharp-rhombic ray with basis (1,0),(1/2,y), choose h=(1,0). Each remaining marking has a triangular cycle of nonzero vertical winding, with period length at least sqrt(y^2+1/4) (for vertical coefficient +/-1 its horizontal component has magnitude at least 1/2; for larger coefficients the bound is also immediate on this ray). Consequently

    q(1,0)!=0  =>  y^2+1/4 < 27/4  =>  y^2 < 13/2.

Thus **q(1,0)=0 throughout y^2>=13/2**, improving the earlier threshold y^2>=35/4. This applies to every remaining sharp-ray marking of Types 4,5,7, independently of the SAT filters, conditional only on the corresponding marking's having the indicated triangular period. For Type 4 that property can be read directly from the two basis cycles 014 and 015. In the interior strip the same reasoning gives the general bound on every triangular period, not an assertion that the sharp-ray threshold carries over unchanged.

### Direct H13 application, without any solver

Use the first sharp-ray marking with the fixed H13 vertex labeling. The cycles (0,1,4) and (2,5,6) are vertex-disjoint triangular cycles, both of period (-1,0): in the gauge K_4j=0 the first sum is (-1,0), and the second is (-1,1)+(0,-1)+(0,0)=(-1,0).

Their linking can be read by hand from the already recorded integer sign representative in section 10. The oriented triangle 014 is in z=0, with closed disk x>=0, y>=0, x+y<=1000. Vertices 2 and 6 have negative z, and vertex 5 has positive z. On edge 52 the plane intersection occurs at parameter 1/6 from 5 toward 2; its two coordinates are positive and their sum is 5548/6<1000. On edge 56 the plane intersection occurs at parameter 1000/4294 from 5 toward 6; the coordinate sum is 5452*1000/4294>1000. Edge 26 stays on the negative side. Thus precisely one transverse crossing of the disk occurs, and the triangular cycles have linking number of absolute value one.

This is not an assumption that the integer representative is flat. The plane-side determinants and the five-point circuits for those two edge/triangle tests are strict in H13 even when the seven allowed nonclique determinants vanish: the tests involve only the vertex sets {0,1,2,4,5} and {0,1,4,5,6}, neither of which contains an allowed zero quadruple from section 11. Hence their sign partitions, and the linking conclusion, transfer to every actual H13 realization under the earlier strictness lemma.

In this marking the triangular cycle (0,1,5) has period (-1,1), of length sqrt(y^2+1/4). The new lemma therefore gives, entirely by hand,

    H13 with the first sharp-ray marking is impossible for y^2 >= 13/2.

No exclusion at the hexagonal endpoint y^2=3/4 follows. Nor does this eliminate other H13 relabelings on non-equivalent markings away from that endpoint. The result is a global elongated-range obstruction, not closure of the H13 hexagonal branch or of Type 4. All 31 hexagonal classes remain unresolved. The preceding geometric proof-audit qualifications still apply.

No computer-assisted calculation was used for this section; the sign representative and strictness lemma are prior data. The central linking bound itself needs neither that representative nor an orientation enumeration.


## 15. Hand-proof global attack: bounded caps and tube, all scales

[Detailed proof](elongated_hand.md). We now use the entire elongated sharp-rhombic ray as the nonuniversality target, rather than continuing the nonlinear H13 hexagonal reformulations.

For every elongated eight-vertex origami-torus sequence the normalized vertical image is a doubled segment with exactly two turns. A barycentric retraction of a nearby horizontal fiber proves each turn carries a horizontal essential cycle. Each turn cluster has three to five vertices. If its physical vertical width diverges, rescale by that width: the two tail directions are opposite, so there is a local turn carrying at least three of the cluster vertices. The cluster strictly shrinks, and after at most two refinements one obtains a bounded physical-width cap. This treats nested intermediate-scale degenerations without assuming relative-interior macroscopic limits.

For Type 4 the graph after removing universal vertices 4,5 is the join of an independent pair and a four-vertex path. The chordless cycles and their lattice periods give six disjoint horizontal triangle-pair classes in ray 1, and two triangle/quadrilateral cap-pair classes in ray 2, with explicit vertical level intervals. Each row has a direct edge through each strip. The bounded cap diameters imply the two representative cap levels are y/2+O(1) apart, and the entire surface lies within a uniformly bounded distance of an actual edge of length y/2+O(1). This holds on both markings, including all endpoint and intermediate-scale degenerations. In ray 2 at least one final cap is isolated, so its physical vertical width tends to zero and its limiting transverse perimeter is one.

No solver, numerical search or computer-assisted enumeration was used. The hand proof inherits the earlier winding-classification premise for the Type 4 tables. It does not exclude any of the eight surviving necessary cap-pair families. Type 4 universality and the H13 hexagonal gate remain open; the next goal is an exact obstruction to the two annuli embedding within the common tube, not more sign subdivisions.
