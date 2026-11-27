# Type 7: two-candidate reconstruction at fixed intrinsic coordinates

## Scope and status

The following reduction works for **every** Type 7 marking and modulus, not just the sharp ray. It uses the strict local support lemma for vertex-minimal paper tori in [orientation_checkpoint](../orientation_checkpoint/README.md), whose independent geometric audit remains outstanding. This is a proof of a reconstruction reduction conditional on that lemma, not a proof of universality/nonuniversality. No numerical feasibility is claimed.

## Theorem (two candidates)

Fix the lattice, edge winding cocycle, and eight intrinsic vertex positions in the universal cover, up to a common translation. Assume all face lengths are those of the prescribed marked flat torus. Up to ambient Euclidean isometry, at most **two** embedded Type 7 realizations satisfying strict local support and nondegeneracy of each K4 exist. They can be reconstructed by one quadratic equation and successive linear equations (plus exact validation), including potentially coplanar nonclique quadruples.

In the Lutz labels the one-skeleton is K8 minus the matching 04, 15, 26, 37, i.e. K_{2,2,2,2}. Select one vertex a_i from each opposite pair as an anchor, and call its unique nonneighbor b_i, for i=0,1,2,3. Both the anchors and the leaves form K4s. The anchor tetrahedron is nondegenerate by the earlier K4 lemma. Its six edge lengths determine it up to ambient Euclidean isometry. Each leaf b_i has known distances to the three anchors other than a_i. Those three spheres intersect in precisely two points reflected across the plane of those anchors, or in no admissible points. Tangency would make the K4 formed by b_i and those three anchors coplanar, which is excluded. Write lambda_j(x) for the affine barycentric coordinates of x in the anchor tetrahedron, with sum_j lambda_j=1. In particular lambda_i(b_i) != 0.

Define a directed graph on the four leaf indices: i -> j, i != j, when lambda_j(b_i) != 0. This is precisely the condition that the distance from b_i distinguishes the two mirror candidates for b_j. Indeed, reflection in the plane lambda_j=0 changes the squared distance to b_i by a nonzero multiple of the signed distance of b_i from that plane, because b_j is not on it.

**Claim: the directed graph is strongly connected for any admissible embedding.** Otherwise it has a nonempty proper set S of indices with no outgoing arc (for example a sink strongly connected component). Then for every i in S, b_i belongs to the affine span of the anchors a_j with j in S.

- |S|=1: the leaf equals its anchor, violating injectivity.
- |S|=2: the four associated vertices all lie on a line. They contain the embedded four-edge cycle K_{2,2}, which cannot be embedded in a line.
- |S|=3: the six associated vertices all lie in the anchor plane and their induced graph is K_{2,2,2}, the octahedral graph. Its embedded straight-line drawing is a simple planar graph with 6 vertices and 12 edges. Euler's formula (and 3-edge minimum face size) forces every region, including the exterior region, to have a triangular boundary. Triangular boundaries are nondegenerate because overlapping edges are excluded. At least one vertex is interior to the exterior triangle; its incident bounded triangular regions fill a neighborhood in the plane, so it lies in the convex hull of its planar neighbors. This contradicts strict support relative to those neighbors (a fortiori relative to all its neighbors).

Thus no such S exists.

**Reconstruction algorithm.** Fix any first leaf index i and choose either of its two mirror positions. If the anchor or a leaf sphere intersection is degenerate, reject. With a set S of placed leaves, find any i in S and j outside S for which lambda_j(b_i) != 0. The prescribed length of the leaf edge b_i b_j selects at most one mirror position of b_j. If neither works, reject. If no such pair exists before all leaves are placed, reject by the claim. Repeat. The deterministic choice of any available arc cannot miss a valid realization: for an actual realization every selection must choose the actual leaf position, and strong connectivity guarantees an outgoing arc for every proper set of already placed leaves. Finally verify every prescribed edge length, nondegenerate faces, strict K4 signs, and full embeddedness, and the intrinsic marking/flatness conditions.

There are just two possibilities for the first leaf, with no additional branching, even if some off-diagonal barycentric coordinates vanish. In particular this does not impose generic signs on actual nonclique quadruples. The previous 12 spanning-3-tree sign branches are unnecessary for this reconstruction.

## Polynomial / rational implementation without coordinate square roots

Put a_0 at the origin. Let G be the 3-by-3 Gram matrix of a_1-a_0, a_2-a_0, a_3-a_0, obtained from the six prescribed squared anchor distances D_{a_i,a_j}. Require G positive definite; put H=adj(G), g=det(G)>0.

For each leaf b_i let z_i = D_{a_i,b_i} denote its unknown squared nonedge distance. All other D_{a_k,b_i} are prescribed. Define the three-vector
    u_i[k] = (D_{a_0,a_k} + D_{a_0,b_i} - D_{a_k,b_i})/2, k=1,2,3.
Here u_i is affine in z_i. The unique ambient point having these inner products with the anchor basis has basis coordinates H*u_i/g. Its barycentric coordinates lambda_1,lambda_2,lambda_3 are these basis coordinates and lambda_0=1-sum(lambda_1,lambda_2,lambda_3).

Its four distances to the anchors hold exactly when
    u_i^T H u_i = g D_{a_0,b_i}.
This is a quadratic in z_i with precisely the same two mirror candidates above when the sphere intersection is admissible. For each pair of leaves, the known edge equation becomes
    2 u_i^T H u_j = g (D_{a_0,b_i}+D_{a_0,b_j}-D_{b_i,b_j}).
This is bilinear in z_i,z_j, and with z_i fixed is affine in z_j. Its coefficient of z_j is nonzero precisely when lambda_j(b_i) != 0, as can also be checked directly by substitution. Consequently the reconstruction requires just one univariate quadratic followed by three linear divisions, and a finite number of residual polynomial equalities and inequalities. The first-leaf root is chosen by the sign of lambda_i(b_i) (same or opposite side as the missing anchor).

The full embedding circuit tests can be evaluated in anchor basis coordinates, using determinants of barycentric-coordinate rows multiplied by the positive denominator g. The affine orientation of the anchor basis is arbitrary and can be fixed globally; nonclique minors may vanish. Nonedge distance upper bounds and the remaining six leaf-edge equalities can be checked explicitly. Using the deterministic propagation above is preferable to arbitrarily dividing by a coefficient that could vanish.

For the continuous global problem one still has the 14 intrinsic coordinates and the fixed-modulus constraints. This result eliminates the extrinsic multibranch explosion, not the continuous feasibility problem. It applies without an aspect-ratio restriction. For the elongated ray_4 case, separately use the previous narrow-level estimates to bound intrinsic coordinates and the exact orientation restrictions. Do not mistake the two reconstruction candidates at each intrinsic placement for two total configurations.

## Next exact gate

Use the joint marking/triangulation symmetry to reduce the 16 elongated ray_4 generic sign models, and combine their strict K4 signs with the two-candidate reconstruction. Attempt exclusion or construction of an entire symmetry family; never infer exclusion from a solver timeout. The earlier full sign archive is necessary only up to generic perturbation, not a claim of genericity of actual metric realizations.

## Stronger theorem: the prescribed edge lengths determine the embedded Type 7 torus

Under the same strict-support and orientation-projection premises, any two admissible Type 7 realizations with the same **24 labeled edge lengths** are congruent. This strengthens the two-candidate result to at most one for every marking and modulus. No assumption of genericity of the actual metric realization is needed.

Suppose two noncongruent admissible embeddings have the same edge lengths. Fix any anchor tetrahedron by a rigid motion. By the propagation theorem, if even one leaf agrees, all agree. Hence all four leaves must be opposite mirror candidates, for **every** choice of anchor tetrahedron.

### Unanimous anchor lemma

Choose inward unit normals n_i to the anchor face opposite a_i, and let H_i>0 be the perpendicular altitude of a_i above that face. Let m_i be the orthogonal projection of leaf b_i to that face, and s_i>0 the unsigned altitude of b_i; both are determined by its three known anchor distances. Thus the two leaf candidates are b_i^+ = m_i+s_i*n_i and b_i^- = m_i-s_i*n_i.

Call an anchor unanimous if the four actual leaves have all positive or all negative relative barycentric signs lambda_i(b_i). In this case the noncongruent candidate would switch all + signs to - signs, or conversely. Put c_i=s_i*H_i>0. For i!=j, direct expansion of the two squared leaf distances gives
    D^+_ij - D^-_ij
      = 4 (m_i-m_j) dot (s_i*n_i-s_j*n_j)
      = -4 [c_i*lambda_i(m_j) + c_j*lambda_j(m_i)].
Since lambda_j(m_j)=0 and sum_i lambda_i(m_j)=1, summing after division by c_i*c_j gives the strict identity
    sum_{i<j} (D^+_ij-D^-_ij)/(c_i*c_j) = -4 sum_j 1/c_j < 0.
Consequently the all-plus and all-minus choices cannot have equal leaf-edge lengths. One unanimous anchor suffices for uniqueness. The weights are positive regardless of where the face projections lie; no convexity assumption about the projections is used.

### Checkerboard obstruction for the remaining clique signs

The 16 anchor cliques are the vertices of a four-dimensional cube (select one member of each opposite pair). Adjacent cliques differ in one vertex. Order the vertices by their pair index. The relative side of b_i is the ratio of the determinant signs of adjacent cliques, since replacing the vertex a_i in its slot changes the determinant by the factor lambda_i(b_i).

If two noncongruent realizations exist, the preceding propagation argument forces every relative side to reverse for every anchor. Thus the ratio of their clique chirotopes must alternate on the four-cube. After normalization by global reflection at anchor 0123, the only possible second clique pattern is the checkerboard twist: negate the sign of a clique if it contains an odd number of vertices from {4,5,6,7}. The same twist formula works for sorted clique orders because the sorting parities cancel in the ratio.

The exact necessary orientation archive in orientation_checkpoint has 316 projected Type 7 clique patterns modulo reflection. The new finite checker (verify.cjs) verifies:
- 308 patterns have a unanimous anchor;
- the other eight have no checkerboard-twisted partner in the archive;
- equivalently, the only four patterns whose checkerboard twist also occurs all have a unanimous anchor.

The eight exceptional patterns therefore cannot have a second admissible realization either. This proves the rigidity claim, conditional on the earlier strict-support lemma and completeness of the necessary SAT projection. It is stronger than generic global rigidity: it asserts uniqueness for all admissible embedded flat realizations, including coplanar nonclique quadruples. It does not assert rigidity of arbitrary placements of the graph without the local support/orientation conditions. No literature-priority claim is made.

### Exact finite symmetry reduction on the elongated ray_4

The 32 Type 7 simplicial automorphisms are enumerated by testing the face set. Their stabilizers of the four sharp-ray markings, allowing lattice isometries and integral vertex gauge, have sizes 16,16,32,32. We use only the four lattice isometries that work for every aspect ratio on the ray: identity, central inversion, and the two reflections. In basis coordinates these are (m,n),(-m,-n),(m+n,-n),(-m-n,n).

For y^2>=35/4, the earlier linking checkpoint gives 16 necessary generic full orientation models for ray_4. Under its 32-element marking stabilizer they form exactly two orbits of size 8. One-based indices in ring4_full_signs.json:
    R1 = [1,2,5,8,10,11,14,15]
    R2 = [3,4,6,7,9,12,13,16]
Use representative 1 for R1 and 3 for R2. With anchor A=(0,1,2,7), leaves B=(4,5,6,3), their relative height signs are respectively ---- and ++++. Thus each canonical branch has a **single** prescribed mirror choice for all four leaves, even before propagation. Any actual degenerate realization can be generically perturbed for the necessary sign classification, then relabeled by a marking stabilizer; K4 signs are strict and persist. Enforce nonclique signs only weakly when solving the actual metric equations. Do not restrict actual embeddings to general position.

The next exact target is to decide these two continuous intrinsic feasibility problems on the compactified range, or at one selected elongated metric. The 16 generic sign models are not sixteen independent nonlinear searches any longer. However, neither R1 nor R2 has been shown feasible or infeasible by this checkpoint, and the other three sharp-ray markings are still open.

### Reproduction

Run from this directory:
    node verify.cjs

The same finite integer/combinatorial computation was executed on the current branch's JSON inputs before upload. It checks graph structure, clique sign unanimity, checkerboard partners, the marking stabilizers and the two ray_4 orbits. For completeness of the input archives, independently replay the earlier orientation_checkpoint/verify_projection.py and linking_checkpoint/verify_full_ring4.py; these were not rerun in this checkpoint. No nonlinear solver result is asserted.

### Exact Gram-completion systems for R1 and R2

The new generator generate_ray4.py instantiates the Gram completion above, retaining the entire range y^2>=35/4 if no fixed aspect ratio is supplied. Set t=1/y^2, use the earlier integer gauge and narrow-level estimate, and write the adjusted normalized vertical coordinates as parity(i)/2+t*gamma_i, with x_0=gamma_0=0. Squared distances are multiplied by t, so each prescribed scaled squared edge length is t*X^2+Y^2. This avoids inverse powers of t. Use the four scaled squared nonedge distances as additional variables. There are 18 real unknowns at a fixed aspect ratio and 19 when t varies, versus 29 for the earlier Cartesian reconstruction at a fixed metric. All expressions are polynomial with rational coefficients after expansion of define-fun aliases.

For orientation and intersection tests, use inner-product coordinates U, not the higher-degree coordinates H*U: multiplying actual anchor-basis coordinates by G is an invertible linear map of positive determinant. This keeps the affine determinants at degree at most six in the fixed-metric intrinsic coordinates and four nonedge distances. The Gram and cross-distance constraints enforce all 24 prescribed edges exactly. The generator retains intrinsic face orientation/degree one, strict nearest-image inequalities, necessary bounds from the narrow-level theorem, nonedge metric upper bounds, strict K4 determinants, weak nonclique signs, and the full earlier degeneracy-complete minimal-affine-circuit intersection test. In particular actual coplanar nonclique configurations are not excluded merely for being coplanar.

For an actual embedded ray_4 torus in the elongated range, one of these two systems must be satisfiable after a marking-preserving symmetry; this necessity inherits the earlier geometric/SAT audit qualifications. Conversely a satisfying assignment supplies a nondegenerate marked flat intrinsic triangulation and an embedded Euclidean realization via the positive definite Gram matrix. One must extract and certify an actual witness before reporting a construction. The finite constraints do not supply a decision procedure with a practical runtime bound.

Reproduce from this directory:
    python generate_ray4.py /tmp/type7-4-fixed 16
    python ../sharp_ray_checkpoint/solve.py 5000 /tmp/type7-4-fixed/R1.smt2 /tmp/type7-4-fixed/R2.smt2
    python generate_ray4.py /tmp/type7-4-range

Fresh local generation from transcribed current archive data produced two 256,956-byte fixed-metric systems (18 real unknowns each) and two 256,948-byte full-range systems (19 real unknowns each). The fixed y=4 queries parsed successfully in libz3, but both returned unknown (timeout at 5000 ms). The variable-t systems were generated, not solved. Neither timeout is an exclusion. The four sharp-ray marking families remain unresolved; only ray_4's elongated orientation classification is reduced to the two symmetry branches here.
