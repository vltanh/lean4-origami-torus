# Type 4: eight finite-metric branches and sharper ray-2 phase constraints

**Status: open, 0/8 maximal branches excluded.** This checkpoint gives a single explicit modulus, tau=1/2+10^6 i, at which the eight-family attack is exhaustive, not merely an asymptotic necessary classification. It uses the already verified general eight-vertex two-gap theorem (../type5_focus/fixed_elongated/README.md, sections 1--2), the two Type 4 sharp-ray markings, the strict K4 premise, and the exact ray-2 bounds in ray2_exact_phase.md. No new proof of those inherited results is claimed.

## 1. Fixed-metric cover including cap boundaries

Put y>=10^6 and epsilon=1/1000. The general two-gap theorem uses only eight vertices, sixteen faces and strict shortest lifts, so applies to Type 4. There are two gap centers s,t on the normalized vertical circle, with

    119/250 < t-s < 131/250.

The two epsilon-near clusters contain essential horizontal cycles and their extrinsic convex hulls have distance >11y/25. Vertices in the same cluster have extrinsic squared distance <=4 epsilon^2 y^2+1/4. A chord in such a cluster has zero vertical winding in its coherent local lifts, by the strict shortest-edge bound. Splitting an essential simple horizontal cycle along chords yields at least one essential chordless horizontal cycle. The complete chordless cycle list from the Type 4 hand proof therefore suffices.

Gauge at universal vertex 4, with normalized vertical lifts b_i and b_4=0. Label vertices by 0 (first cap), 1 (open strip), 2 (second cap), 3 (other open strip). For each vertex choose an integer q_i so b_i-q_i is in [s-epsilon,s+1-epsilon), with q_4=0 and the names of the gap centers chosen so vertex 4 has label 0 or 1. The radial edge 4i gives |b_i|<1/2+1/(8y^2), hence q_i is in {-1,0,1}. Under the monotone collapse of the two epsilon neighborhoods, every edge interval is contained in a closed half-turn interval, since an edge straddling a gap with both endpoints outside its epsilon neighborhood would contradict the definition of a gap.

[type4_gap_enum.py](type4_gap_enum.py) exhausts this finite condition using quarter-unit labels 0,1,2,3 and integer lifts. It requires a chordless essential horizontal cycle in each cap and tests the half-turn condition for every edge. The four triangulation automorphisms are enumerated exactly, and each allowed marking stabilizer is checked by comparing the transformed integer cocycle with the original up to a vertex coboundary. The allowed sharp-ray lattice symmetries are I,-I and the two coordinate reflections. The first marking has two compatible automorphisms; the second has four.

There are 56 relative cells in the first marking and 9 in the second. To avoid unnecessary smaller endpoint branches, take maximal closed cells: a strip label can absorb either of its neighboring cap labels, with the integer lift adjusted at the seam. The containment test checks every vertex in quarter-unit coordinates, allowing a simultaneous shift by an even number of quarter units (renaming gap centers and changing their lift). Its finite-metric implication is obtained by broadening the first strip to [s-epsilon,t+epsilon] and the other strip to [t-epsilon,s+1+epsilon]. These broadened intervals contain both neighboring cap intervals with exactly the checked lift adjustments. A maximal cell retains all its own cap vertices. Thus every actual embedding covered by a relative cell is covered by a maximal one, including endpoints and degenerate configurations. No strict inequality of an open strip is incorrectly imposed at a collapsed boundary.

There are ten maximal cells in ray_1 and four in ray_2. Quotienting by the checked marking symmetries gives the following eight representatives. The integer q's are listed in vertex order 0,...,7.

| ID | Labels | q |
|---|---|---|
| ray1_1 | 00120212 | (0,0,0,-1,0,-1,0,-1) |
| ray1_2 | 00130222 | (0,0,0,-1,0,-1,0,-1) |
| ray1_3 | 00230223 | (0,0,0,-1,0,-1,0,-1) |
| ray1_4 | 01200223 | (0,0,0,0,0,-1,0,-1) |
| ray1_5 | 02200323 | (0,0,0,0,0,-1,0,-1) |
| ray1_6 | 12200023 | (0,0,0,0,0,0,0,-1) |
| ray2_1 | 12220002 | (0,-1,0,-1,0,0,0,-1) |
| ray2_2 | 20220012 | (0,0,0,-1,0,0,0,-1) |

In particular the earlier asymptotic eight-family attack now has an explicit common finite target. The listed representatives are closed-family covers rather than disjoint relative cells. This is enough for an exhaustive nonexistence proof. Excluding all eight at the common modulus would settle Type 4 negatively.

## 2. Exact product bounds for the entire second marking

The following derivation works at every y>=10, not just the fixed large metric. Use the physical coordinates and notation of ray2_exact_phase.md:

    p4=0, p2=(c,Y2), Y2=y/2+u/y,
    -3/8<u<1/8, |c|<1/2,
    L=|r2-r4|, |L-y/2|<1/y, L>y/2-3/(8y).

Set r4=0 and choose e=r2/L as the unit axis. Write the physical intrinsic coordinates of the remaining vertices as p_i=(x_i,Y_i) and decompose r_i=z_i e+P_i with P_i perpendicular to e. The previous tube theorem gives |P_i|<3/2. The universal vertex 4 gauge gives |x_i|<1/2 and |Y_i|<y/2+1/(8y).

For i=0,6 the shift K_2i is zero, so polarization of the preserved edge lengths to 4 and 2 gives exactly

    L z_i = c*x_i+Y2*Y_i.

For i=1,7 the directed shift K_2i is respectively (-1,1),(0,1), with physical components (k,y), k=+/-1/2. The corresponding identity is

    L z_i = (c-k)*x_i+(Y2-y)*Y_i+c*k-k^2/2+u.

No approximated edge length is used in these identities. Define H_i=Y_i for i=0,6 and H_i=-Y_i for i=1,7. The strict nearest-lift bounds on edges 2i give Y_i>(u-1/8)/y for i=0,6 and Y_i<(u+1/8)/y for i=1,7. Consequently

    -1/(2y)<H_i<y/2+1/(8y).

Since |L-y/2|+|u|/y<11/(8y), both |Y2-L| and |Y2-y+L| are <11/(8y). Also L> (397/800)*y for y>=10. In the first polarization equation the numerator for |z_i-H_i| is bounded by 1/4+(11/8)*(1/2+1/(8y^2)); in the second it is bounded by 5/4+(11/8)*(1/2+1/(8y^2)). Dividing by L proves, uniformly,

    |z_i-H_i|<5/y, i=0,1,6,7.

This is stronger than merely bounding the distance to the axis, and remains valid if edge 45 or a cap degenerates.

For the three edges 16,01,67, the intrinsic vertical components have absolute values |H1+H6|, |y-H0-H1|, |y-H6-H7|, respectively. Their extrinsic squared lengths are (z_j-z_i)^2+|P_j-P_i|^2. Since |H_j-H_i|<y/2+5/(8y) and |(z_j-z_i)-(H_j-H_i)|<10/y,

    (z_j-z_i)^2-(H_j-H_i)^2
       < 10+225/(2y^2).

The transverse squared difference is <9. Dropping the nonnegative squared intrinsic horizontal displacement from the metric equality now gives

    4 H1 H6 <21,
    (y-2H0)(y-2H1)<21,
    (y-2H6)(y-2H7)<21.

Here 19+225/(2y^2)<=20.125 for y>=10. These are upper bounds, not assertions that the products have positive signs near the endpoint of a strip. Let t_i=2 H_i/y. The exact necessary inequalities used in the new solver are

    -1/y^2<t_i<1+1/(4y^2),
    t1*t6<21/y^2,
    (1-t0)*(1-t1)<21/y^2,
    (1-t6)*(1-t7)<21/y^2.

They cover all placements of the intermediate vertex and all cap degenerations. They imply a particularly simple finite-metric cap localization. The checked symmetry (0,1,2,3,4,5,6,7)->(7,6,3,2,4,5,1,0), combined with vertical reflection, exchanges t1,t6 and t0,t7 without changing the metric or marking. Thus we may assume t1<5/y, since if both t1,t6 were >=5/y the first product would exceed its upper bound. Then 1-t1>1/2, hence t0>1-42/y^2. At least one of t6,t7 is >1-5/y, by the third product. The triangle 145 is consequently in a physical vertical interval of width <3, and the quadrilateral 0263 or 0273 is in a coherent physical vertical interval of width <3 near the half-period level. If t6>=1/2, then t1<42/y^2 and the triangle has width <22/y. If t6<1/2, then t7>1-42/y^2 and quadrilateral 0273 has width <22/y. Thus at least one of the two cap cycles is quantitatively thin. This is a global finite-metric statement, with no positive lower bound on any cap edge or determinant.

## 3. Cubic signed-Gram feasibility, without orientation branching

Use the gauge at 4, write p_i=(x_i,b_i) in coordinates with squared norm x^2+w b^2, w=y^2=10^12. For i,j different from 4 define

    S_ij=(|p_i-p_j|^2-D_ij)/2,

where D_ij is squared extrinsic chord length. Every S_ij is nonnegative by metric contraction. S_ii=0, and all edge entries are affine expressions in the intrinsic coordinates: if K_ij=(m,n), use k=m+n/2 and

    S_ij=-k*(x_j-x_i)-w*n*(b_j-b_i)-(k^2+w*n^2)/2.

If K_ij is nonzero this is strictly positive by uniqueness of the intrinsic shortest edge. For the four nonedges S_ij is an unknown. The centered Euclidean Gram matrix is G=S+P diag(1,w) P^T, with P the seven-row intrinsic coordinate matrix. Introduce the signed Gram block

    H = [S, P; P^T, -diag(1,1/w)].

Then G is PSD of rank three exactly when H has inertia (3,2), rank five.

For **both markings**, the sparse pivot (2,6,1,3) has matrix

    M = [0 0 A B; 0 0 0 C; A 0 0 0; B C 0 0],

where A=S_12>0, C=S_36>0, and B=S_23>=0 is a nonedge slack. Its inverse scaled by AC is

    N = [0 0 C 0; 0 0 -B A; C -B 0 0; 0 A 0 0].

Direct multiplication gives MN=AC I. The pivot has inertia (2,2), since its two-by-two offdiagonal block is invertible. No assumption of strictness of the nonedge slack B is necessary. For the remaining indices J=(0,5,7,8,9), impose

    AC H_ij-H_(i,pivot) N H_(pivot,j)=U_i U_j (i,j in J, i<=j),
    sum U_i^2>0.

Schur complementation proves the desired inertia and rank exactly. These are fifteen cubic polynomial equations (the coefficients in H and N are affine), using 14 intrinsic, 4 missing slack, and 5 auxiliary variables. The full formula has higher degree in the incidence tests; only the metric equations are cubic.

The generator [type4_fixed_cubic.py](type4_fixed_cubic.py) adds the broadened gap intervals with centers eliminated by pairwise lower/upper comparisons, both cap separation/diameter constraints, strict nearest edge lifts, consistent intrinsic face orientations with signed double-area sum +/-2, positive chord lengths and necessary nonedge contractions. In ray_2 it also imposes the exact product and earlier phase bounds. It requires all clique tetrahedral affine Gram determinants positive (the verified strict K4 condition).

For --full, use the augmented affine Gram H_aff=1*1^T+G_ext, where G_ext includes the zero row/column at 4. It is PSD of rank four. Every prohibited intersection of disjoint simplices supplies a minimal sign-compatible dependence supported on two to five vertices. On such a set the Gram has rank one less than its size, and its adjugate is a positive scalar multiple of the kernel vector outer product. Normalize the first kernel coordinate positive. A prohibited sign pattern is therefore equivalent to determinant zero and strict prescribed signs of the first-row cofactors. Conversely these signs, with the determinant zero, give an affine dependence whose positive and negative parts are disjoint simplices. The rank-one test on the signed Gram ensures these implications even when many nonclique minors vanish. The resulting 546 exclusions cover all disjoint-simplex pairs on supports of size at most five, including degeneracies. With the intrinsic degree-one face orientation conditions, a solution of the full formula would itself give an embedded flat realization, and an independently proved UNSAT result would exclude the entire corresponding family. The finitely many extra nonedge comparisons are necessary; exact isometry and embeddedness of any full solution imply all other metric contractions as well.

## 4. Reproduction and remaining gate

From this directory:

    python3 type4_gap_enum.py
    python3 type4_fixed_cubic.py /tmp/type4-cubic
    python3 type4_fixed_cubic.py /tmp/type4-full --full

To run a local libz3 query (timeout in milliseconds):

    python3 -c 'from type4_fixed_cubic import solve; from pathlib import Path; print(solve(Path("/tmp/type4-full/ray2_1.smt2").read_text().replace("(check-sat)",""),5000))'

The local exact finite enumeration gave the 56/9 relative counts, 10/4 maximal counts, and 6/2 representatives above. The local generator used the transcribed face and gauged marking data; the saved version adds an exhaustive chordless-cycle and cocycle check. The numerical result is not being substituted for the proof of finite coverage. The generator's initial necessary systems (using equivalent clique coordinate-minor tests) timed out at 8000 ms each. The final affine-Gram necessary systems timed out at 3000 ms each. The final eight full systems, with 23 variables and 865 assertions for ray_1 or 890 for ray_2, all returned UNKNOWN (timeout at 5000 ms). No SAT/UNSAT result was obtained. The final local generator version was executed; a fresh checkout replay is still needed for the archived import version.

An independent exploratory sampling of the published Type 3 three-parameter planar family at the sharp ray (150,000 parameter samples for each w=3/4,1,4,100, ten two-flip paths) found no simultaneously convex pair of flips to Type 4 among the numerically flat samples. This is inconclusive and not a premise of any theorem here.

**Actual remaining gate: 0/8 full maximal families excluded at tau=1/2+10^6 i.** This is a finite target including all collapsed-cap boundaries, not an additional infinite hierarchy. The product theorem is a new exact restriction, not closure of ray_2. No construction on the sharp ray was certified, and Type 4 remains open.
