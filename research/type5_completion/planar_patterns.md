# Type 5: exact planar-pattern reduction at the hexagon

## Scope and result

This is a finite cover of the **regular planar inflation route**, not of arbitrary three-dimensional embedded realizations. The hexagonal marking is the archived sharp Type 5 representative. As in the regular inflation construction, all intrinsic faces are nondegenerate, and each vertex has both signs among its incident projected faces (the horizontal angle-defect derivative vanishes at a monochromatic star). Singular inflation and other nonplanar realizations are not excluded.

After identifying global reversal of all 16 face signs, there are 32768 masks. The exact screen leaves 448 masks in 82 symmetry classes. Six whole classes, totaling 33 masks, are then excluded by uniform geometric height-order contradictions. **415 masks in 76 classes remain.** No elongated cell or full hexagonal feasibility branch is closed.

## Geometric finite screen

Use the face order and edge shifts in the source archive. Gauge p0=0, use lattice coordinates x+y*tau, tau=exp(i*pi/3), and squared norm x^2+xy+y^2. Bit i of a mask records the sign on face i; bit 15 is zero after global reversal. For this archived marking the sum of oriented doubled intrinsic triangle areas in lattice coordinates is identically -2, not +2. Thus every true face has negative determinant in the recorded orientation. An earlier exploratory count used the opposite convention; the counts here use the corrected convention and exact rerun.

A facewise isometric planar map is globally nonexpanding for the intrinsic metric.

* A same-orientation edge-connected face component develops by a single rigid isometry. If one vertex acquires two distinct lifts, their distinct intrinsic positions would have the same image under that isometry, an impossibility. Two same-sign components agreeing at two distinct coherently lifted vertices must use the same rigid isometry, after adjusting a common lattice translation. Merge them and apply the same consistency check.
* Crease edges separate faces of opposite sign. At a mixed star the intrinsic angle sum is 2*pi and the signed projected angular sum is a multiple of 2*pi of absolute value strictly below 2*pi. Thus the two sign-angle sums are each pi. At a vertex with exactly two crease edges their rays must be opposite, so they cannot bound a nondegenerate face. A chain through degree-two crease vertices is straight both intrinsically and in the folded plane. Its coherent displacement realizes the distance of its image endpoints; global contraction implies it is a shortest lattice displacement. The checker also tests closed straight chains and a chord using the same lift; none is needed for the reported extra exclusions.
* For any two vertices in the same developed component, and endpoints of a straight crease path, the coherent displacement d is a shortest lift by the same contraction argument. For every shortest lattice vector l, the necessary inequality is 2<d,l> <= ||l||^2. These six inequalities have integer coefficients using twice the Gram matrix. The LP is used only to propose certificates. A nonnegative rational combination giving 0 <= negative excludes the mask. A combination giving the negative of the sum of selected inequalities forces each selected inequality tight. Exact integer identities, including constants, are checked before using the equalities; no floating feasibility tolerance is used for exclusion. Surviving rows need not describe the full affine hull.
* At a mixed vertex the product of alternating conjugated and unconjugated complex crease rays is negative real: the alternating angular sums are pi. Use tau^2=tau-1 to impose its exact imaginary equation and real sign. A nonzero intrinsic face area cannot vanish.
* At a planar realization each K4 squared-distance Gram determinant is zero. The signed sum of folded oriented face areas is zero by cancellation on a closed oriented surface. The checker removes factors known nonzero because they divide a nonzero actual face area, and tests constant contradictions and linear consequences. This last filter is only attempted for small affine dimension. It is safe to leave extra candidates.
* All six vertex symmetries used for the quotient preserve the marked hexagonal metric up to lattice change and gauge, checked by the script.

Exact first-reason ledger (masks / symmetry classes):

| Reason | Masks | Classes |
|---|---:|---:|
| Monochromatic star (regular-route restriction) | 8088 | 1406 |
| Inconsistent component | 21849 | 3696 |
| Inconsistent merged component | 624 | 109 |
| Consecutive crease rays | 627 | 108 |
| Linear infeasibility | 45 | 9 |
| Zero intrinsic face | 991 | 173 |
| Kawasaki sign | 45 | 8 |
| Nonzero metric product | 51 | 9 |
| Survive | 448 | 82 |

## Six complete parametric families

All planar configurations in the following six representative masks obey the indicated affine parametrization derived by the screen, followed by necessary exact residual equations. This covers the entire possible domain, not just numerically obtained foldings.

Write x0,x1 for the coordinates of p1, x2,x3 for p2, and so on through x12,x13 for p7. Let a_f be minus the recorded oriented intrinsic area determinant, strictly positive. In planar coordinates set r1=0, r5 and r2 equal to the coherent intrinsic displacements from 1 (after an overall rigid motion/reflection). The anchor face 152 has nonzero area. Each remaining vertex j is adjacent to the three anchors, so its planar coordinates are uniquely determined by

    2<r5,rj> = d15+d1j-d5j
    2<r2,rj> = d12+d1j-d2j

where dij denotes squared intrinsic edge length. The determinant of the two anchor vectors is nonzero. Put Rij=||ri-rj||^2-dij. The script checks the exact identities below and all 24 edge residuals after substitution. All variables A,B,T in the parametrizations lie strictly between 0 and 1.

* 10919: free x9,x11,x13. Areas 053,045,012,465,357 give a=-(3*x11+1)>0, b=3*x13-1>0, d=x11-x13+1=(1-a-b)/3>0, t=x11-x9>0, d-t>0. Take a=A, b=(1-A)B, t=(1-A)(1-B)T/3. Then x11=-(a+1)/3, x13=(b+1)/3, x9=x11-t.
* 18353: free x1,x11,x13. Areas 031,024,256,136,237,274 give -1/3<x11<x1<0 and 2*x11+1/3<x13<1/3. Take x11=-A/3, x1=-AB/3, x13=(1-2AT)/3.
* 3021: free x3,x11,x12,x13. Set h=x13-x12-1, l=x12-x13+3*x3, k=x12+1, g=(h+3k)l-3k. Residuals R17=(-2*x12-x13+3*x3-3)g/l^2 and R37=-3k*g/l^2 imply g=0: otherwise k=0 and l=0, contrary to face 012. Areas 024,053,012,136,164,263,357 give 0<h,l<1, (2h-1)/3<x11<h/3, 3k+h<1. Therefore k=hl/(3(1-l)) and h+l<1. Take h=A,l=(1-A)B,x11=(2A-1+(1-A)T)/3, x12=k-1,x13=k+h,x3=(1+h+l)/3.
* 3052: free x0,x1,x11,x13. Set h=x13,l=h-x0-2*x1, g=x0*h-2*x0+2*x1*h-x1-h^2+h-1. Residuals R01=-(x0-x1+1)g/l^2 and R03=-(2*x0+x1-h+1)g/l^2 imply g=0, since otherwise x0=(h-2)/3,x1=(h+1)/3 forces face 012 degenerate. Areas 024,053,152,263,136,465 give 0<h,l<1 and (2h-1)/3<x11<h/3. Take h=A,l=B,x11=(2h-1+(1-h)T)/3,x1=(1+h+lh-2l)/3,x0=h-2x1-l. The projected points r0 and r7 coincide identically.
* 4017: free x1,x4,x5,x11. Set g=3*x11*(x4-x5-1)+2*x4+x5. The difference R03-R13=-x1*g/[x11*(3*x1-3*x11-1)] implies g=0 by the strict face areas 012,274,152. Set h=-3*x11, b=-3*x1, t=x4-x5. The areas give 0<b<h<1 and 0<t<1. Take x11=-A/3,x1=-AB/3,x4=((A+1)T-A)/3,x5=((A-2)T-A)/3.
* 18289: free x9,x10,x11,x13. Set h=3*x9+2,l=x10+2*x11-3*x9. Areas 031,024,164,256,237,274 give 0<h,l<1 and 2*x9+1<x13<1/3. Residual R36=-3*x9*l-3*x11+6*x9+1 gives x11=-x9*l+2*x9+1/3. Take x9=(A-2)/3,l=B,x10=3*x9+l-2*x11,x13=2*x9+1+2*(1-A)*T/3.

Every necessary domain above is covered by the open parameter cube. Nonzero denominators follow from the anchor face and the displayed strict bounds. The verifier checks positive intrinsic face areas on each cube. It certifies the projected determinant signs needed for the obstruction by exact rational Bernstein coefficients (after clearing denominators of fixed sign); unused signs may be unresolved. No claim is needed that every point in the parameter cube is a full valid folding in the original mask.

## Geometric circuit obstruction, including nongeneric projections

A minimal projected affine dependence has support of size 2 (coincident points), 3 (distinct collinear points), or 4 (all four triples noncollinear). Cofactor determinants, using an external point in the collinear case, certify its positive and negative supports. Normalizing both sets of coefficients to sum to 1 gives an intersection point of their projected convex hulls. Use a canonical sign convention with smallest support vertex positive.

Whenever the two disjoint supports fit into two actual faces, a putative vertical lift must give strictly different heights at their common projected point. For any two such witnesses using the same pair of faces, the signs of their height differences relative to that face order must coincide. Indeed the height difference is affine along the segment joining the two projected points, inside both projected triangles. Neither point lies in the projection of the common simplex: uniqueness of barycentric coordinates in each nondegenerate projected face and disjointness of the two supports rule this out. The common projected simplex is a face of each projected triangle, and the segment cannot meet it. A sign reversal would therefore yield an actual forbidden intersection. This argument also works for faces sharing an edge or vertex and for coincident or collinear projected vertices.

Each witness supplies a binary height sign. An edge of the witness graph records equality or negation of two signs, derived from the face order. A negative-product cycle is contradictory. In the following table ij/kl means the crossing of the two projected edges, with canonical sign convention; each listed sequence closes back to its first witness. The successive sign multipliers are in the final column. The verifier constructs the cycles from the face list and the certified determinant signs.

| Mask | Orbit size | Witness cycle | Multipliers |
|---|---:|---|---|
| 3021 | 6 | 02/35, 01/37, 01/27, 03/24 | + + + - |
| 3052 | 6 | 0/7, 24/35 | + - |
| 4017 | 6 | 04/26, 24/56, 27/45, 05/23 | + + - + |
| 10919 | 3 | 36/47, 16/27, 14/23 | + + - |
| 18289 | 6 | 04/13, 03/24, 03/27, 05/23, 36/45 | - + + - - |
| 18353 | 6 | 13/24, 03/27, 05/23, 04/36 | + + + - |

In 3052, the first comparison is the height difference z0-z7 at the forced coincident projected pair. Faces 024 and 357 give the same sign as the crossing height difference of 24 and 35; faces 053 and 274 give the opposite sign. This is a two-step contradiction without perturbing the projection.

## Verification and remaining gate

From the repository root, with Python, NumPy, SciPy, and SymPy:

    python3 research/type5_completion/verify_planar_patterns.py
    python3 research/type5_completion/verify_planar_families.py

Both passed locally using a fixture transcribed from the archived face and shift tables; both scripts check those input tables and the default invocation reads the repository archive. Numerical LP proposals are validated by exact rational certificates; failed proposal recovery is not an exclusion. The second script replays the screen, domain identities, 24 edge equations, Bernstein signs, geometric cycles and final orbit counts, then prints the remaining (representative, orbit size, affine parameter count) ledger. The exact affine parameter count is for the retained affine constraints, not the dimension of an actual folding space.

Exploratory nonlinear search found approximate planar foldings in 16 classes; their sampled lifts failed (15 height-order cycle failures, one linear feasibility failure). This is not a certificate for those classes. Only the six complete families above are charged to this ledger.

Next gate: tackle the remaining 76 symmetry classes, using full-domain parametrizations and geometric sign certificates; or find an embedded lift and establish an exact metric-preserving inflation. The old two-flip family exclusion is separate and is not double-counted. No Lean theorem or full Type 5 classification is asserted.
