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