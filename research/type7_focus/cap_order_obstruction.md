# Exact two-cap obstruction for Type 7 and a quantitative consequence for ray_3

## Scope

The verified two-cluster localization and phase bounds suggest using the two short rings 0145 and 2367 in ray_3 rather than attempting to refute the already certified feasible metric-only Gram system. Here we prove an exact obstruction to these two rings being contained in disjoint supporting planes, and a necessary quantitative degeneracy condition at the chosen finite metric. This uses the previously verified necessary orientation formula, with the strict-support/mixed-side and K4-nondegeneracy lemmas as premises. The blocked Boolean formula is independently replayed. We do **not** claim to exclude all configurations near these planes. Ray_3 is not yet closed.

## 1. Two-cap supporting-plane theorem (no aspect-ratio restriction)

Let A=(0,1,4,5) and B=(2,3,6,7), in cyclic order. In the Type 7 graph the short ring edges form the two four-cycles and all sixteen cross edges are present. Suppose the surface has a straight-edge embedded realization satisfying strict local support relative to neighbors, the mixed-side incident-face condition at every vertex, and noncoplanarity of every K4. These are necessary for flat Type 7 by the earlier geometric lemma.

**Theorem.** It is impossible for A and B to be in separate planes, each of which strictly supports the opposite four vertices on one side. In particular this excludes distinct parallel planar caps.

To reduce to parallel planes, let f,g be affine functions with f=0 on A, f>0 on B, g=0 on B, g>0 on A. They are linearly independent as affine forms and h=f+g is positive throughout the convex hull of the eight vertices. Complete f,h to a basis l1,l2,f,h of affine forms. The invertible projective transformation
    p -> (l1(p)/h(p), l2(p)/h(p), f(p)/h(p))
maps the caps to planes of heights 0 and 1. On the convex hull it is a continuous bijection, maps line segments onto line segments, preserves convex-hull containment and sends the triangulated surface to an embedded straight-edge complex. It also preserves affine determinant signs up to a single global sign, because each positive denominator just rescales the corresponding homogeneous row. The strict local support, mixed-side, and clique-nondegeneracy conditions therefore persist. Flatness need not persist; only its necessary consequences are used here.

In the resulting configuration all four triples within each cap are noncollinear. Indeed a triple of a cyclic quadrilateral consists of two successive ring edges. If their middle vertex is between its two neighbors on the line, strict local support fails at the middle vertex; if not, the two edges overlap, violating embedding. Each pair of ring edges (one from each cap) forms a K4, hence every corresponding mixed tetrahedron is strictly nondegenerate. The two rings are unlinked because a plane strictly separates them.

Perturb the eight vertices sufficiently slightly into general position. The earlier necessary orientation formula applies to the perturbed configuration, the two cap rings remain unlinked, and all strict signs of three cap vertices and one opposite vertex and of the sixteen K4s persist. For each triple T within A the determinant sign of [T,b] is independent of b in B, since in the unperturbed configuration it is its planar triangle area times the positive height difference. The corresponding statement holds within B (negative height difference). All these necessary equalities are encoded directly by 48 additional Boolean clauses. The proof needs no assertion of general position of the original configuration.

The resulting formula has 215 variables and 7,818 clauses (only the unlinking of A and B, not of any other pair, is imposed). The exact SAT enumeration gives 16 full generic orientation patterns modulo global reflection. Blocking these 16 patterns makes the formula UNSAT. The independent existing exhaustive C++ DPLL checker replayed the 7,834-clause blocked formula in 1,027 nodes. No previously cached ray_3 sign list is needed.

Let e_0,...,e_3 and f_0,...,f_3 be the cyclic planar edge vectors of the two unperturbed parallel caps. In each sign pattern, every sign of cross(e_i,f_j) is prescribed by the corresponding K4 determinant: in the order A edge followed by B edge the bracket equals -cross(e_i,f_j). The signs of cross(e_i,e_(i+1)) and cross(f_j,f_(j+1)) are given by the three-plus-one brackets, with opposite signs for A and B's height differences. Thus 24 strict planar cross-product signs are prescribed.

Represent each nonzero vector as a signed positive multiple of a unit vector with line angle in a common half-open interval of length pi. Write its sign as z_i in {-1,1}. If a prescribed cross-product sign for vectors i,j is s_ij, then the corresponding line angles must satisfy angle_i<angle_j when z_i*z_j*s_ij>0, and angle_j<angle_i otherwise. Strict comparisons cannot form a directed cycle. Global reversal of all eight vectors leaves every cross-product sign unchanged, so only 2^7 sign choices need be tested.

For **all 16 orientation patterns and all 128 sign choices**, the exact integer graph check finds a directed cycle. Hence no such eight planar edge vectors exist. Contradiction. This proves the theorem, conditional on the earlier geometric premises. No continuity across a degenerate cap is assumed.

## 2. A finite-metric consequence for every elongated ray_3 realization

Use the verified ray_3 localization in remaining_markings.md, choosing its canonical phase with caps A,B as above (the alternative phase is equivalent by the checked rotation). For y>=8, each short ring hull has diameter less than 1.1. Write w=y^2. Every long cross-edge squared length differs from w/4 by less than 2.05: its horizontal displacement has absolute value <1/2, and its normalized vertical displacement differs from +/-1/2 by <7/(4w). Thus the absolute correction is at most 1/4+7/4+49/(16w)<2.05.

Choose the cross edge 02 as a longitudinal axis, r0=(0,0,0), r2=(0,0,L), L=|r2-r0|>y/2-7/(4y). Write r_i=(P_i,L*h_i) with two-dimensional P_i, and c_i=0 for A, 1 for B. We have |P_i|<1.1, P0=P2=0. Comparing the squared length from each vertex to the opposite anchor with L^2, and subtracting its squared distance to its own anchor, gives
    |2*L^2*(h_i-c_i)| < 4.1+1.21=5.31.
For w>=64, L^2>(1/2-7/(4*64))^2*w, so in particular
    |h_i-c_i| < 13/w.
This bound is valid at finite y; it does not require a limiting cap, or that its transverse area be nonzero.

Let D(q) denote the affine determinant of the four normalized extrinsic points (P_i,h_i), and D0(q) the determinant after replacing h_i by c_i. Expand their difference along the vertical coordinate in the 3-by-3 difference matrix. Each of the three terms is at most (26/w)*(2.2)^2 in absolute value, since each height-difference error is <26/w and each projected pairwise difference has norm <2.2. Hence
    |D(q)-D0(q)| < 400/w.

**Necessary finite-metric degeneracy condition.** At least one of the following 24 planar determinants has absolute value at most 400/w:
- the eight signed double triangle areas from triples within A or B;
- the sixteen cross products cross(e_i,f_j) of projected cyclic ring-edge vectors, one from each cap.

Otherwise every one of those determinants is strictly larger than the possible error. The normalized actual 3+1 and K4 signs agree with their planar replacements; the 3+1 signs are constant over the opposite cap, and all twenty-four projected cross-product signs are strict. The caps are strictly separated by the verified finite-metric localization, so their short cycles are unlinked. Perturb the actual configuration generically, preserving the strict signs and unlinking. The exact Boolean and line-order contradiction from Section 1 now applies to these signs and the projected edge vectors. Contradiction.

At the fixed target y=10^6 the bound is 4*10^-10. Thus any actual ray_3 embedding must be extremely close to a transverse determinant degeneracy; one cannot have a uniformly nondegenerate projected pair of quadrilaterals with all cross-edge directions nonparallel. This is a new necessary constraint on the **finite** 18-variable system, not another assumption of general position. The union of the 24 small-determinant inequalities can be imposed without eliminating an actual degenerate solution.

## 3. Verification and remaining obstruction

From research/type7_focus:
    python3 verify_cap_order.py /tmp/cap_blocked.cnf
    g++ -O3 -std=c++17 ../orientation_checkpoint/check_unsat.cpp -o /tmp/check_cap_unsat
    /tmp/check_cap_unsat < /tmp/cap_blocked.cnf

Fresh local results on the transcribed repository inputs:
    vars 215 clauses 7818
    PASS complete enumeration: 16 models, every one of 128 signed line orders cyclic
    UNSAT nodes 1027
The committed verifier uses the existing repository formula and linking encoder directly. The separate attempted Z3 DRAT trace did not pass the local RUP checker; it is not used for this proof. The exhaustive DPLL replay supplies the independent Boolean check instead. The geometric premises still require independent audit as before.

The exact holonomy/linear-angle relaxation is not a solution: adding the essential-cycle turning sum equal to k*pi for every k-edge essential simple cycle, and both sector upper bounds on every extrinsic angle, still admits the uniform pi/3 assignment. On the three remaining markings there were 2,254 distinct essential-cycle rows and 353 distinct sector rows, and all 66 archived ray_3 orientation models retained strict feasible angle margins. This was tested using the existing angle system; it is a negative result, not a proof of closure.

The new theorem excludes a complete geometric construction class, but it does not exclude configurations with small projected determinants and nonplanar caps. The verified exact metric-only witness cannot imply nonuniversality (it is not embedded), and the phase bound alone does not control signs near a zero determinant. The necessary next step is to combine the above finite error bound with exact metric constraints and strict embedding near the degeneracy locus, or find a certified embedded witness. No ray_1 or ray_2 branch, and no full ray_3 marking, is closed by this checkpoint. The earlier conditional ray_4 closure remains unchanged.
