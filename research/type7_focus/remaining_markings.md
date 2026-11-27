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
