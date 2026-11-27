# Type 5: four maximal elongated limit families

**Status: Type 5 universality remains unresolved; B1.1 at the hexagonal modulus remains 0/14 excluded.** This is a new global attack on the sharp ray, not a closure of the previous branch. The first-scale theorem and interior second-scale compactification below do not use the orientation archive. The cap-hull exclusion uses the earlier necessary generic sign enumeration, strict-support perturbation and marking reduction, which retain their proof-audit qualifications.

## 1. Every elongated limit has exactly two turn levels

Assume a sequence of Type 5 embedded flat tori with lattice (1,0),(1/2,y), y tending to infinity, and use the sole sharp-ray marking from the earlier exhaustive winding enumeration. Gauge the intrinsic shifts K out of universal vertex 1 to zero. Write the physical intrinsic coordinate of vertex i as (x_i,y*b_i). The strict shortest-image inequalities imply |x_i|<1/2 and |b_i|<=1/2+O(1/y^2) in this gauge. Every edge's physical horizontal displacement has absolute value <1/2. Each intrinsic horizontal fiber is a closed geodesic of length one, so the extrinsic diameter of each fiber is at most 1/2.

Scale the extrinsic embedding by 1/y and translate a point to zero. The scaled image of (0,y*b), 0<=b<=1, is 1-Lipschitz and uniformly bounded; its endpoint mismatch is at most 1/(2y) because of the shear. Pass to a convergent subsequence, also fixing the limits of the vertex vertical levels and the unit vertical directions of the finitely many face isometries. All points in the same horizontal fiber have the same limit. Denote the resulting closed curve by c(b).

On a face lift with positive limiting vertical span, choose two points at two levels in the span's interior. The difference of their scaled images is (b'-b) times the face's unit vertical direction, plus an error tending to zero: the horizontal span of the face is <1/2. Thus c is affine with unit speed throughout that limiting vertical span. Every open gap between limiting vertex levels is contained in at least one such span, by covering of the torus by the finitely many triangles. Consequently c is a closed unit-speed polygon with possible turns only at vertex levels.

At a genuine turn level no face lift can have that level strictly between its minimum and maximum vertical coordinate. Consider the limiting piecewise affine circle map b on the abstract triangulated torus, given by the vertical cocycle and limiting vertex lifts. Its homotopy class is the primitive vertical period class. The preimage of a turn level is a subcomplex. A sufficiently nearby regular level is a disjoint union of polygonal circles representing the Poincare dual of the vertical period class (or count oriented intersections with a loop on which the class evaluates to one). Hence at least one component has nonzero horizontal homology. It can be deformed into the turn subcomplex: in each simplex meeting the nearby level, normalize its barycentric weights on the vertices at the turn; the weights have positive sum and the simplexwise maps agree on shared faces. The straight barycentric homotopy stays on the abstract torus. Approximating this loop by an edge walk in the subcomplex and decomposing the walk into simple cycles gives a simple cycle of nonzero horizontal homology. A simple essential circle on a torus is primitive, so the cycle winds +/−(1,0). It has at least three vertices.

The vertex sets at different turn levels are disjoint. Eight vertices allow at most two turns. A nonconstant closed unit-speed polygon has at least two. Therefore it has exactly two, its two unit directions are opposites, and each segment has parameter length 1/2. After translation and an orthogonal transformation, c is the segment from 0 to 1/2 on an axis, traversed twice. This argument applies to every subsequential elongated limit, without assuming the limit embedding is injective.

## 2. Exact finite enumeration

Shift the vertical circle so the turns are at 0 and 1/2. Use labels 0,1,2,3 for the sets {0}, (0,1/2), {1/2}, (1/2,1). Interchange the turns if necessary so vertex 1 has label 0 or 1. In origin-1 gauge, write the limiting normalized vertical lift as b_i=t_i-t_1+q_i, where t_i has the specified label and q_i is an integer, q_1=0. For every edge ij the interval from t_i to t_j+q_j-q_i+K_ij^n must be contained in some [k/2,(k+1)/2]; otherwise its face spans a genuine turn. This condition depends only on the labels, not the actual interior coordinates. Because vertex 1 is universal and K_1i=0, all q_i are in {-1,0,1}. Each cap (turn level) contains at least three vertices and a primitive horizontal cycle.

The standard-library checker enumerates this finite condition exactly. There are 36 normalized relative cells; every one is contained in an endpoint closure of one of seven maximal cells. The permutation (6,5,2,4,3,1,0,7) preserves the cocycle up to gauge and physical vertical reflection (m,n)->(m+n,-n), valid for all sharp moduli. It identifies the seven maximal cells in four classes. The representatives below are ordered by vertex labels 0,...,7; q is in the same order.

| Family | Labels | Integer q | Turn cycles |
|---|---|---|---|
| F1 | 00120221 | (0,0,0,-1,0,0,-1,0) | 014, 356 |
| F2 | 00220231 | (0,0,0,-1,0,0,-1,0) | 014, 235 |
| F3 | 00230232 | (0,0,0,-1,0,0,-1,0) | 014, 257 |
| F4 | 01200202 | (0,0,0,0,0,0,0,0) | 0364, 257 |

There are at most two free continuous vertical levels in each family. This is a necessary limit classification, not an assertion that these limits can be approached by embeddings. The checker also gives exact rational intrinsic placements approaching the midpoint of all seven maximal cells for every y^2>=256. It chooses small vertical corrections eta_i/y^2 in a topological ordering of directed cross-cap edges. All strict nearest-lift constraints and all strict intrinsic face areas hold uniformly (check the affine inequalities at y^2=256 and their slopes); the fixed cocycle has degree one up to orientation by the earlier marking reduction. Thus intrinsic feasibility alone does not close this direction.

## 3. Bounded second scale in the relative interiors

Fix a sequence whose limiting vertical labels are in the relative interior of one maximal cell (the interior variables are strictly between their turn endpoints). The exact combinatorial check shows that each cap induces just its simple horizontal cycle, each cap edge has two incident faces extending into opposite strips, every face has positive limiting vertical span, and each strip has a cap-to-cap edge. No claim of uniform bounds across the boundary of a maximal cell is made.

In a face let u_f,v_f be its unit horizontal and vertical directions in R3. At a cap edge with intrinsic displacement (X,Y), the two face representations agree:
    X*(u_f-u_g)+Y*(v_f-v_g)=0.
The limiting vertical directions on the two strips are opposite unit axial vectors. Dotting with the limiting axis first shows Y=o(1), since |X|<1/2 and both u vectors become perpendicular to the axis. Hence the two cap clusters have bounded extrinsic diameters.

Choose the actual axis e along a cap-to-cap edge in the positive strip, pointing from cap A to B. A cap-to-cap edge in the other strip, oriented A to B, differs in extrinsic vector by O(1) because its endpoints are in the same bounded clusters. Its intrinsic vertical displacement has opposite sign and magnitude asymptotic to y/2. Thus the vertical directions of faces containing these edges differ from +e and -e respectively by O(1/y).

For any two faces with an overlap of physical vertical intervals of length L, choose points at two common levels separated by L (or slightly inside the overlap). Points at the same level have extrinsic distance at most 1/2, and the horizontal spans within each face are at most 1/2. Subtracting the two facewise displacement identities gives L*||v_f-v_g||<=2. Every face in a strip overlaps its cap-to-cap reference face on an interval of length >=c*y for some c>0 depending on the limiting interior levels. Consequently all face vertical directions are +/-e+O(1/y) on their respective strips, and u_f dot e=O(1/y). Since v_f is unit, v_f dot e=+/-1+O(1/y^2).

Return to the cap edge identity and dot with e: now Y=O(1/y), and the cap edge axial displacement is also O(1/y). Thus each cap's intrinsic physical vertical width and extrinsic axial width are O(1/y). For representative cap vertical levels separated by Delta, the two cap-to-cap edge squared lengths differ by O(1) extrinsically (bounded transverse components and axial differences O(1/y)). Intrinsically their difference is Delta^2-(Delta-y)^2+O(1). Hence Delta=y/2+O(1/y), and the chosen axis edge length is y/2+O(1/y).

This yields an exact bounded coordinate system along any such sequence. Translate the intrinsic vertical turn origin to the representative A vertex; retain the integer q from the limiting cell. Write adjusted normalized levels as tau_i+eta_i/y^2, with tau_i=0 or 1/2 on the caps, and tau_i equal to the actual adjusted level on an interior vertex (eta_i=0 there). Then eta_i is bounded. Let f(tau)=tau on [0,1/2] and 1-tau on [1/2,1]. The extrinsic coordinates in an orthonormal frame with axis e have bounded transverse coordinates P_i and axial coordinate y*f(tau_i)+rho_i/y, with rho_i bounded. Indeed on each edge its transverse displacement is O(1), and the axial displacement differs from the signed intrinsic vertical displacement by O(1/y); telescope along graph paths, fixing the representative A vertex at zero. The preceding angle estimates prove these assertions even if the cap polygons themselves collapse.

Set t=1/y^2, X_ij=x_j-x_i+K_ij^m+K_ij^n/2, v_ij=tau_j-tau_i+q_j-q_i+K_ij^n, and d_ij=f(tau_j)-f(tau_i). The finite label condition gives d_ij^2=v_ij^2. Canceling the leading y^2 terms in the exact edge metric identities gives

    ||P_j-P_i||^2 + 2*d_ij*(rho_j-rho_i) + t*(rho_j-rho_i)^2
      = X_ij^2 + 2*v_ij*(eta_j-eta_i) + t*(eta_j-eta_i)^2.

This is polynomial on each cell. At positive t, normalized extrinsic coordinates (P_i, f(tau_i)+t*rho_i) preserve all affine incidence signs and intersections by invertible axial rescaling. The strict horizontal nearest inequalities are |X_ij|<1/2; for a directed positive cap-to-cap edge the long nearest condition is eta_j-eta_i+|X_ij|/2<1/8 for sufficiently large y. Other nearest and intrinsic orientation inequalities can be used directly in the adjusted lifts. At t=0 replace strict inequalities by weak ones, and do not assume embeddedness of the limit.

## 4. Exact elimination of axial corrections at t=0

On either strip write sigma=+1 or -1 so v_ij=sigma*d_ij, and U_i^sigma=rho_i-sigma*eta_i. At a cap both U values are independent coordinates; for an interior vertex only its strip's value is used. The limiting non-cap metric equations become

    2*d_ij*(U_j^sigma-U_i^sigma)=X_ij^2-||P_j-P_i||^2.

On each strip the checker verifies a connected spanning subgraph of edges between different cap levels or between a cap and an interior vertex, omitting all interior-interior edges. The d's on this subgraph cannot vanish anywhere in the open cell. Thus solve along a spanning tree of each strip, and impose residual equations on every remaining edge; no generic rank assumption is needed even if interior vertices have equal levels. Fix both U constants at the reference cap vertex. The rank of the correction equations is 12 for F1-F3, 13 for F4. Including the cap metric equations, the residual system has 12,12,12,11 quadratic equalities in horizontal/transverse coordinates respectively, with coefficients rational in the one or two interior levels. For residual edges with d=0 use the displayed equation directly. Clear only the known nonzero tree denominators. The cross-cap nearest conditions are then linear comparisons on reconstructed eta differences.

The naive weak t=0 relaxation is feasible in **all four families**: four exact collinear transverse witnesses with quarter-unit horizontal/transverse coordinates and sixteenth-unit corrections are included in the checker. They were found using a bounded discrete SMT query at the midpoint levels, then checked by exact rational arithmetic independently of the solver. They satisfy every limiting edge equation, weak intrinsic face orientation, weak horizontal and cap-cross nearest conditions. The transverse collinearity means all normalized 3D affine minors vanish, so merely imposing weak orientation signs cannot exclude them. They do not prove that any is approachable at positive t. In particular do not pursue plain t=0 metric infeasibility.

## 5. One global nondegenerate limit exclusion

The earlier necessary generic sign archive contains 751 Type 5 orbits, 4506 labeled models modulo reflection after expanding the six triangulation automorphisms. For sufficiently elongated sharp-ray embeddings the short-direction linking number vanishes by the earlier diameter/linking bound. All five disjoint horizontal triangle pairs must therefore have zero linking. Exact affine circuit evaluation keeps 3004 of the 4506 models.

If a cap's limiting transverse polygon spans the plane, some triple of cap vertices is noncollinear. In the bounded normalized coordinates its determinant with any outside vertex has strict sign of a fixed side, since every outside limiting axial level is strictly on that side. Thus for all sufficiently large y, that triple has the same determinant sign with every vertex outside the cap, even if other four-point determinants are zero. A sufficiently small generic perturbation preserves these strict signs as well as the necessary orientation conditions and linking. Filter the 3004 models by this condition for both caps, allowing any cap triple for the quadrilateral.

| Family | Models compatible with both caps spanning |
|---|---:|
| F1 | 0 |
| F2 | 60 |
| F3 | 130 |
| F4 | 40 |

Therefore **in the relative interior of F1, at least one limiting transverse triangle is collinear**. This excludes an entire nondegenerate two-cap limit family, not an individual point. It also applies to the symmetry mate of F1. The counts use the prior archive's completeness and perturbation/linking premises, not a fresh independent SAT proof. F2-F4 remain unresolved even in the two-spanning-cap case. Boundary cells with additional vertices approaching a turn require a separate uniform or multiscale argument. The exact finite cap-hull test is in verify_hulls.cjs.

## Reproduction and next gate

Run python3 verify.py and node verify_hulls.cjs from this directory. The first checker was run locally on transcribed repository cocycle and face data, with all assertions enabled; the second exact enumeration was executed using the actual GitHub archive and marking input. The rational t=0 witnesses were checked locally. No full positive-t solve or independent geometric proof audit has been carried out in this checkpoint.

The remaining nonuniversality gate is eventual exclusion of all four closed maximal families, including transverse degenerations and endpoints. The first-scale reduction is exhaustive under the earlier marking enumeration; the bounded second-scale system is presently proved only for relative interiors. There is no proof that any elongated sharp modulus is impossible. No Type 5 universality or B1.1 chamber status has changed.
