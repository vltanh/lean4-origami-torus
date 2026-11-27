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
