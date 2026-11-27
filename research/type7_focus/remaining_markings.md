# Remaining Type 7 markings: quantitative fixed-metric localization

## Scope and status

The previous final-polynomial certificate closes ray_4 at y^2 >= 35/4, conditional on its geometric premises. The other three markings are not closed by this checkpoint. The goal here is to replace an unbounded continuous degeneration argument by rigorous constraints valid at a common **finite** target modulus, and to check whether the successful orientation-only method can suffice for the other markings.

The new bounds are consequences solely of shortest edge lifts, the winding data, and the Euclidean edge metric. They do not require the earlier strict-support or orientation-SAT reduction. Their applicability to an exhaustive Type 7 classification does require the prior marking enumeration.

## 1. Ray_1 and ray_2: exact cyclic metric equations

Write the vertex labels cyclically modulo 8. Every edge has cyclic step 1, 2 or 3; the four missing edges are the opposite pairs. At either marking, the cocycle correction from the path of k consecutive step-1 edges to the step-k edge is (1,0), for k=2,3. The step-1 Hamiltonian cycle has period (-4,1) for ray_1 and (-3,1) for ray_2. Each consecutive triangular cycle (i,i+1,i+2) has period (-1,0). These are checked against the archived cocycle in verify_remaining_markings.cjs.

Write the physical horizontal displacement and normalized vertical displacement of the step-1 edge i as x_i,b_i. Thus the physical edge is (x_i,y*b_i), and sum_i b_i=1. Since every edge has |X|<1/2, the three horizontal displacements of each oriented consecutive triangle must all be negative (their sum is -1). In particular -1/2<x_i<0. Put t=1/y^2 and E_i=(r_(i+1)-r_i)/y, using extrinsic vertex positions r_i. Then sum E_i=0 and
    |E_i|^2 = b_i^2+t*x_i^2.
Polarization of the step-2 and step-3 edge equations gives exactly
    E_i dot E_(i+1) = b_i*b_(i+1) + t*(x_i*x_(i+1)+x_i+x_(i+1)+1/2),
    E_i dot E_(i+2) = b_i*b_(i+2) + t*(x_i*x_(i+2)-x_(i+1)-1/2).
Both bracketed corrections have absolute value at most 1/2. These are global cyclic identities, not assumed asymptotic behavior.

## 2. Exactly seven possible large-step masks at a finite metric

**Theorem.** For either ray_1 or ray_2 at any y>=10^6, label a step-1 edge large when |b_i|>=1/1000 and small otherwise. The large indices have exactly two connected components in the graph that joins cyclic indices at distance 1 or 2. Each component has signed vertical sum greater than 0.44. There are at least four small steps; the two components have cyclic spans of at most three edges each and are separated by gaps of at least two small edges. In particular there are two disjoint consecutive horizontal triangular cycles whose extrinsic convex hulls have distance greater than 0.32*y.

Proof. Set delta=1/1000. The nearest-lift inequalities on the sharp lattice imply |b_i|<1/2+t/8<0.501. The small edge normalized length is at most |b_i|+sqrt(t)/2<0.001001. For large indices define U_i=E_i/b_i, and W_i=U_i/|U_i|. The metric identities imply |U_i|>=1 and, whenever two large indices are adjacent in the distance-1-or-2 graph,
    |U_i-U_j|^2 <= (3/2)*t/delta^2.
Moreover |U_i-W_i| <= t/(8*delta^2). At y>=10^6 it follows that |W_i-W_j|<0.003 and |U_i-W_i|<10^-6.

For each connected component C, choose a representative unit direction W_C from one of its indices, and let B_C=sum_{i in C} b_i. A path has at most seven edges. Thus
    |sum_{i large} E_i - sum_C B_C*W_C|
      < 8*0.501*(7*0.003+10^-6) < 0.085.
The sum of the norms of all small E_i is less than 0.009. Closure therefore gives |sum_C B_C*W_C|<0.095. On the other hand sum_C B_C>1-8*delta=0.992. There must be at least one large index, and a single connected component is impossible. Three components would require at least three large indices and six separating small indices, more than eight. Exactly two components remain.

The reverse triangle inequality gives ||B_1|-|B_2||<0.095. Since their sum is greater than 0.992, both must be positive and each is greater than (0.992-0.095)/2>0.44. The cyclic span of each component includes any intervening small edge within the component; the two spans and two separating gaps partition the cycle. The spans each have at least one edge and the gaps each have at least two. Thus each span has length at most three. Across either component span the normalized displacement has norm greater than 0.44-0.085-0.009=0.346. All vertices along either of the separating gaps lie within 0.009 of the corresponding endpoint of that span, by the small-edge length bound. Their two convex hulls have distance greater than 0.346-0.018>0.32. Each gap contains at least three consecutive vertices, hence a horizontal triangle. This proves the asserted finite-metric separation.

The checked cyclic rotation i -> i+1 preserves both markings up to integer vertex gauge. Exhaustively enumerating the 255 nonempty masks of eight indices gives exactly seven rotation classes having two connected components in the distance-1-or-2 graph:
    03, 04, 014, 015, 025, 0125, 0145.
Digits are large-edge indices, not vertex configurations. These seven masks are an exhaustive necessary finite **branch partition at y=10^6** for each of ray_1 and ray_2 (and uniformly for larger y). Each branch retains real variables. No mask has been proved infeasible.

### Limiting consequence (not needed for the finite-metric theorem)

Along any sequence with y tending to infinity, pass to limits of the bounded b_i and E_i. Nonzero b_i with cyclic distance at most two have E_i/b_i equal by the exact dot-product identities. The same component argument, now with zero errors, gives exactly two components, each with sum 1/2 and opposite unit directions. There are at least four zero vertical steps. Inside either span every partial sum belongs to [0,1/2]: its prefix and suffix are paths of at most three edges, hence their limiting sums have absolute value at most 1/2 by the shortest-lift bounds on their chords. Thus all normalized extrinsic vertices, and therefore their affine triangles, lie on a single segment of length 1/2 in the limit. This is a collapse theorem, not an impossibility theorem.

## 3. Ray_3: exact global energy identity forces one of two short-ring partitions

Here take A=(0,2,4,6), B=(1,3,5,7). Each directed ring has period (1,-2), hence horizontal winding zero and normalized vertical winding -2. Choose baseline lifts x_i^0,b_i^0 with horizontal displacement zero and normalized vertical displacement -1/2 along each ring edge. Set x_0^0=x_1^0=b_0^0=b_1^0=0. This is a gauge for the real coordinate equations; no claim is made that the baseline is an actual intrinsic placement. Write the actual lifts as x_i=x_i^0+xi_i and b_i=b_i^0+eta_i. Let bars denote arithmetic means within a ring, and define
    a=mean_B(xi)-mean_A(xi)+1/4,
    h=mean_B(eta)-mean_A(eta).
Use xi' and eta' for deviations from the appropriate ring means.

The cross-edge displacements from A to B are
    X_ij=a+xi'_j-xi'_i+C_ij,
    V_ij=h+eta'_j-eta'_i+D_ij,
where each row and column of C contains two +1/4 and two -1/4, and each row and column of D contains two 0 and two -1/2. The checker verifies the two shift arrays exactly. Ring edges have X=xi_j-xi_i, V=-1/2+eta_j-eta_i.

Let G be the sum of the 16 squared cross-edge lengths minus the sum of the eight squared ring-edge lengths. In any Euclidean realization, for the extrinsic centroids c_A,c_B,
    G = sum_{i=0}^3 |r_i-r_(i+4)|^2 + 16*|c_A-c_B|^2 >= 0.
Indeed for a four-point ring the sum of its four edge squares plus its two diagonal squares equals four times the sum of squared distances to its centroid. The cross-edge sum gives four times each within-ring variance plus sixteen times the squared centroid difference.

Compute G instead from the intrinsic displacements. Centered linear cross terms vanish because the shift arrays have constant row and column sums. The same elementary four-point variance identity, in each scalar coordinate, gives
    G = 1+16*a^2 + sum_{i=0}^3 (xi_i-xi_(i+4))^2
        + w*sum_{i=0}^3 (eta_i-eta_(i+4))^2 - 16*w*h*(1/2-h),
where w=y^2. This is an exact identity, including the order-one terms.

On each directed long-ring edge the strict nearest-lift inequality gives
    eta_j-eta_i > (-1/8+|X_ij|/2)/w.
Summing around that ring shows sum |X_ij|<1. The horizontal difference across either opposite pair is bounded by the smaller of the absolute path-length sums along the two ring arcs, hence |xi_i-xi_(i+4)|<1/2. Following the directed ring paths in both directions bounds any eta difference in one ring by 3/(8w), and opposite differences by 1/(4w). Averaging the horizontal nearest-lift inequalities on the two cross-shift classes gives |a|<1/4. Averaging the vertical bounds gives -1/(8w)<h<1/2+1/(8w).

Consequently G>=0 implies
    16*w*h*(1/2-h) < 3+1/(4w).
If h lies in [0,1/2], set d=min(h,1/2-h). Then h*(1/2-h)=d*(1/2-d)>=d/4. Outside that interval the preceding vertical bound already puts h within 1/(8w) of an endpoint. For w>=16 it follows in either case that
    min(|h|,|h-1/2|) < 1/w.
This proves quantitative alignment at every fixed y>=4, not just as y tends to infinity.

At the selected endpoint, the vertices divide into the two short rings 0145 and 2367 if h is near 0, or 0347 and 1256 if h is near 1/2. The two choices are equivalent by checked cyclic rotation. Centered eta differences across A,B have absolute value at most 3/(4w). Thus all eight edges inside the selected two short rings have |V|<7/(4w), and all sixteen edges between them have |V|>1/2-7/(4w). The latter include the original long-ring edges, for which the bound is even stronger. All edges still have |X|<1/2.

In particular for y>=8 each short edge has length less than sqrt(1/4+49/(16w))<0.55; each short-ring hull has diameter less than 1.1, by the shorter of the two paths around the ring. Every cross-partition edge has length greater than y/2-7/(4y)>=3.78125. Taking any cross-edge endpoint pair as anchors, the two convex hulls have distance greater than 3.78125-2.2>1.5. They must therefore be strictly separated. At y=10^6 we can impose the canonical phase near h=0 and all these exact linear vertical bounds in the fixed-metric feasibility system. This leaves one localized continuous ray_3 branch, not a certified exclusion.

The identity uses neither Ptolemy inequalities nor the orientation archives. In the limit the two short rings become point clusters at distance 1/2 in the normalized coordinates, so again every normalized surface converges along a subsequence to a segment of length 1/2.

## 4. Why final-polynomial elimination alone cannot finish

The exact integer witness coordinates in verify_remaining_markings.cjs realize a generic straight-edge embedding of the Type 7 triangulation with strict local support at every vertex and the mixed-side condition. The first witness works with the zero-horizontal-linking relaxation of both ray_1 and ray_2, and the second with ray_3. Exact integer affine determinants check all 70 brackets nonzero, every five-point circuit avoids disjoint edge-face crossings and forbidden neighbor-convex-hull containments, and every vertex has a mixed-side incident face. Generic position makes these circuit tests sufficient for embedding and strict support. They are not flat metric witnesses.

For each of the three markings the checker additionally tests all 691 disjoint simple cycle pairs (lengths 3–5; any disjoint cycles in an eight-vertex graph fit these lengths). Their signed linkings agree with a linking quadratic form n*(k*n+s*m), where (k,s) is (-1,-1) for ray_1, (0,-1) for ray_2, and (0,-1) for ray_3, in the checker's ambient orientation convention. In particular horizontal self-linking vanishes. The ray_1/ray_2 witness has eight separated short-triangle pairs out of twelve; the ray_3 witness has both short-ring pairs separated. These witnesses satisfy the qualitative separated-hull requirement too. They demonstrate that the necessary orientation/linking relaxation used to close ray_4 is genuinely realizable in the other markings; final polynomials cannot prove it infeasible. Metric conditions are essential. They do not show that the exact localized metric systems are feasible.

## 5. Numerical search and next gate

A limited local SLSQP search at y=4 for ray_3 tried ten archived orientation classes using 24 scaled edge length equations, strict nearest-lift and intrinsic face area inequalities, and strict full generic determinant signs. No positive-margin candidate was found (best feasible numerical margin approximately -2.4e-15). This is not an exhaustive search or any proof of infeasibility, and generic searches do not address actual nongeneric configurations. Do not count it as a closed branch.

Use the common explicit metric y=10^6. The finite branch partition for a direct exact fixed-metric attack is now 7 masks for ray_1, 7 for ray_2, and one canonical two-cluster phase for ray_3; ray_4 is already conditionally excluded at that metric. These are **15 continuous semialgebraic branches**, not 15 point configurations. Impose the derived bounds in the earlier complete 18-variable Gram completion systems and retain degeneracy-complete intersection tests. A certificate excluding every one of these branches would give a specific flat torus not realizable by Type 7. The bounds do not themselves imply such a certificate. No branch among the remaining three markings has been closed here.

## Reproduction

From research/type7_focus run:
    node verify_remaining_markings.cjs

The checker was executed on the current branch's archived edge shifts and face list, using integer arithmetic (BigInt for determinants), and passed the winding, phase, cyclic symmetry, seven-mask enumeration and exact witness checks. The hand derivations of the inequalities are given above. Previous geometric audit qualifications for the ray_4 closure remain unchanged.

### Fixed-metric Gram relaxation trials

The new generate_remaining.py produces all fifteen localized systems at y=10^6, each with 18 real unknowns (14 intrinsic coordinates and four missing squared distances). The systems impose the derived mask/phase constraints, strict shortest lifts, oriented intrinsic faces of absolute degree one, positive distances, nonedge contraction against a finite set of lattice shifts, positive-definite Gram anchor 0123, ten bordered Gram completion equations and nonzero clique minors. The rank-three Gram part is exact; the system omits the general embedding intersection conditions, so it is a necessary relaxation, not sufficient for existence.

The locally generated versions (from the transcribed case data) were run with libz3. Seven ray_1 masks and ray_2 mask 03 returned UNKNOWN at a 2000 ms per-query solver limit. The remaining six ray_2 masks and ray_3 phase0 returned UNKNOWN at 500 ms. These short first attempts are not a practical exhaustion, and no branch is excluded. Generated systems are about 56–59 kB. Reproduce with:
    python generate_remaining.py /tmp/type7-remaining 2000
Use a longer timeout for subsequent experiments, but require a checkable infeasibility proof or a certified witness; do not interpret UNKNOWN as evidence of impossibility. The script is now committed with the actual archive loader.

## Faster local metric test and stopped approaches

For each of the 16 clique-adjacent edges ab, unfold the two actual incident faces abc and abd in a single intrinsic chart. Write b-a=(u,v), c-a=(p,q), d-a=(r,s) in coordinates with metric X^2+wY^2. Choose orientation so that A=uq-vp>0 and B=vr-us>0. Put L=u^2+w v^2. Let Delta be the squared length of cd in the unfolded chart minus its prescribed squared edge length. All 16 K4s of Type 7 occur exactly once in this way. Exact enumeration of the archived cocycles confirms that the two lifts of cd are distinct in every marking, so Delta>0 by strict shortest lifts.

The Gram matrix of the extrinsic three vectors b-a,c-a,d-a has the intrinsic inner products except that the c,d entry is increased by Delta/2. Direct determinant expansion gives the identity
    det G = Delta*(w*A*B - Delta*L/4).
Consequently every true realization satisfies
    0 < Delta*L < 4*w*A*B.
Conversely, for these six lengths, nondegenerate intrinsic triangles and this strict inequality give a positive definite Gram matrix (use the positive 2-by-2 leading minor of abc and Sylvester's criterion). This is a local tetrahedron criterion, not global completion. It gives a low-degree intrinsic-only necessary test for each of the 16 cliques, avoiding general Gram determinant expansion. The determinant identity was verified with SymPy and the clique/lift counts by exact integer enumeration.

For ray_1/ray_2, write beta_i for the normalized vertical step-1 displacement and use the large-step mask convention at y>=10^6. For a large step i, its clique-adjacent opposite edge is the step-3 chord from i+3 to i+6. Write S=beta_(i+3)+beta_(i+4)+beta_(i+5), with indices modulo 8. Its unfolded alternative has vertical displacement S-1 (up to reversing both directions). The nearest-lift constraints give |X|<1/2 and |V|<1/2+1/(8w) for every edge. Thus A,B<0.501, L>=w/10^6, and the new test gives Delta<1,004,004. The horizontal squared-distance contribution to Delta is greater than -1/4. Hence
    S > 1/2 - 1,004,004.25/(2*w),
    S < 1/2 + 1/(8*w).
These are further necessary linear localization bounds at the fixed target. None of the seven unsigned masks is excluded just by these estimates; do not count them as closure.

### Approaches tested and stopped

- Spherical-angle LP: introduce the 15 pairwise neighbor-ray angles at each vertex, normalized by pi. Impose triangle angle sums for all graph triangles, flatness (sum 2) at each vertex, spherical triangle inequalities, perimeter <2 for spherical convex polygons in a strict supporting hemisphere, and the weak crossing-diagonal inequalities inferred from the generic sign model. On all 66 locally archived ray_3 representatives the uniform rational assignment of 1/3 to every angle passes every inequality, with margin 1/3 for the marked strict inequalities. This was checked in exact rational arithmetic, not merely inferred from LP status. This particular relaxation is too weak and should not be pursued.
- Consistent-cross-lift metric-circuit filter: enumerating all 2-versus-3 five-vertex partitions with a complete bipartite cross graph yielded zero extra exclusions in all four markings.
- Rescaled ray_3 construction search at y=4: 16 local starts in separated-hull orientation chambers found no positive certified margin (best numerical margin about 1.7e-13). A proper half-turn-symmetric ansatz, matching 12 independent edge equations, also yielded no positive certified margin in 18 local starts at y=4. These are failed exploratory searches, not impossibility proofs.

No new marking or mask has been closed. Retain the original single-metric target; do not create additional asymptotic branches on the basis of the above observations. The main unresolved requirement is a certificate of infeasibility (or a certified positive realization that changes the intended direction) for the full metric-and-embedding system. 

## Uniform exact feasibility of the ray_3 metric-only relaxation

**New result (not an embedded torus):** for every y>=10^6, the localized ray_3 metric-only system has a strictly nondegenerate Euclidean realization with distinct vertices, all 24 correct edge lengths, strict shortest lifts, consistent intrinsic face orientation of degree -1, all four nonedge distances strictly below intrinsic distances, and all 70 affine determinants nonzero. The same 20 disjoint edge-face pairs intersect throughout this family. Thus the Gram relaxation in generate_remaining.py cannot be proved UNSAT in phase0 at the common target or at any larger y. Do not spend more solver time trying to refute that relaxation.

The exact certificate in verify_metric3_uniform.py uses the following stable reconstruction. Let t=1/y^2, take the baseline lifts and canonical short-ring partition A=0145, B=2367 from section 3, and write the horizontal and normalized vertical lift corrections as x_i and t*gamma_i, with x_0=gamma_0=0. Let X_ij be the corrected horizontal edge displacement, Y0_ij the baseline normalized vertical displacement (zero within a short ring and +/-1/2 across the rings), and dgamma=gamma_j-gamma_i. Define c0=X_02^2+2*Y0_02*gamma_2+t*gamma_2^2, L=sqrt(1/(4*t)+c0), and den=1+4*t*c0. Choose r_0=0, r_2=(0,0,L); set transverse coordinates P_0=P_2=0 and rho_0=rho_2=0. For each other vertex define
    r_i=(P_i, L*I[i in B]+rho_i/(2*L)).
For a directed edge let ell=I[j in B]-I[i in B] and drho=rho_j-rho_i. The edge equality after multiplying by den is the polynomial
    den*(|P_j-P_i|^2+ell*drho+ell^2*c0-X_ij^2-2*Y0_ij*dgamma-t*dgamma^2)
      +t*drho^2 = 0.
The anchor edge 02 holds by definition. The other 23 equations in 32 real variables are checked by a uniform contraction certificate, with nine variables fixed to specified rational values and 23 pivot variables in a box of radius 10^-8 around a specified rational center. All polynomial coefficients are rational, including the parameter t.

For each fixed t in [0,10^-12], let f be the vector of these 23 polynomial expressions in the pivot variables and C the rounded inverse of the midpoint Jacobian at t=10^-12. The code verifies by outward-rounded integer intervals on the whole product box that
    ||C*f(center,t)||_infty < 6*10^-13,
    ||I-C*D f||_infty < 2*10^-6.
These bounds prove the map u -> u-C*f(u,t) is a contraction of the closed box into itself, uniformly in t. The second bound implies C is invertible, so its fixed point satisfies all 23 equations exactly. NumPy is used only to choose C; every assertion that certifies the fixed point is verified using integer interval arithmetic with outward rounding at 10^-45. The t=0 fixed point is only a polynomial limit; the Euclidean reconstruction is for t>0.

The same interval box verifies all strict nearest-lift comparisons and canonical phase bounds, negative oriented face areas (the symbolic sum of double areas is -2), positive and strictly contracted squared nonedge distances against every lattice translate, and strict signs of all 70 affine determinants. For the latter, use scaled axial coordinates I[i in B]+2*(t/den)*rho_i; when all four vertices are in a single short ring, cancel the common positive factor 2*t/den. The verified signs give 20 prohibited edge-face intersections by the ordinary five-point affine circuit test, including edge 03 against face 245.

Reproduce:
    python3 verify_metric3_uniform.py
Requires SymPy, NumPy, and assertions enabled. The uniform interval checks were run locally on the transcribed current cocycle and face list; the committed version loads these directly from the archive. The local contraction bounds were approximately 5.328e-13 and 1.313e-6; all 70 determinants and 20 crossings were certified. The explicit rational box and pivot indices are in the verifier.

**Implication for the research direction:** the rank-three metric relaxation is rigorously feasible, even throughout the entire selected elongated range. The next attack on ray_3 must use embeddedness (strict local support, necessary orientations, or disjoint simplex constraints), not longer runs of the incomplete Gram system. A follow-up numerical search seeded from this metric solution in the twelve nearest separated-hull orientation models found no positive embedding margin; that is not an infeasibility certificate. This checkpoint closes no further marking. Ray_4 remains conditionally excluded; the other three are open.
