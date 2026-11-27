# Type 7 ray_4: positive slack transport and exclusion of every two-dimensional two-ring limit

## Status

New results: (i) an exact positive transportation identity for **all** ray_4 embeddings, at every modulus on the sharp ray, and (ii) a global asymptotic obstruction to both limiting rings spanning a plane, including the case of one vanishing side in each ring. The second conclusion uses the earlier elongated orientation archive, joint symmetry reduction, and bounded compactification; their audit qualifications remain. This does not exclude actual embeddings with collapsing rings as y tends to infinity. No claim of ray_4 or Type 7 nonuniversality.

## 1. Exact transport identity, not an asymptotic approximation

Use the ring labels A=(0,2,4,6), B=(1,3,5,7) in cyclic order and the gauge from linking_checkpoint/verify_ring4.py. Denote the oriented intrinsic ring edge vectors by a_i,b_j (i,j=0,...,3), and their extrinsic straight-edge vectors by e_i,f_j. The two intrinsic ring windings are both (1,0), while the extrinsic rings close:
    sum a_i = sum b_j = (1,0),   sum e_i = sum f_j = 0.
Let alpha_i,beta_j be the physical horizontal components of a_i,b_j.

For each ring edge pair, label the four corners (A_i,B_j), (A_i,B_{j+1}), (A_{i+1},B_j), (A_{i+1},B_{j+1}). Correct the four cross-edge shifts to a common chart using the two ring-edge lifts. The exact cocycle has three equal corrected shifts and a single different shift, always at corner (0,1) or (1,0). The difference between the exceptional actual shift and the common-chart shift is one of the four long Voronoi neighbor shifts, namely +/-tau or +/-(tau-1), at every sharp modulus tau=1/2+iy.

For the exceptional edge, define delta_ij as half the difference between the squared length in the common chart and its actual squared length. The latter is strictly shorter (an embedded straight edge realizes a unique shortest intrinsic path; any other path of the same length would have to map to the same straight segment, contradicting injectivity). Hence delta_ij>0. The four-point Euclidean dot-product identity, comparing the intrinsic common chart with the actual six distances in the K4, gives
    e_i dot f_j = a_i dot b_j - delta_ij.
Summing rows and columns proves the **exact** identities
    sum_j delta_ij = alpha_i,  sum_i delta_ij = beta_j,
    sum_ij delta_ij = 1.
In particular every horizontal ring step is strictly positive, and each is strictly smaller than 1/2 by uniqueness of the horizontal shortest lift. This eliminates all backward horizontal ring steps without any aspect-ratio approximation or orientation assumptions. Each row/column of the transport matrix is a prescribed positive marginal. Each of the 16 cross edges appears exactly once as the exceptional edge.

For a cross edge (i,j) with i in A, j in B, write X for its physical horizontal displacement and its normalized vertical displacement as n+1/2+t*(gamma_j-gamma_i), where t=1/y^2 and the adjusted shift n is 0 or -1. If the exceptional correction is (m',n'), then n'=-(2n+1) and d=m'+n'/2 is +/-1/2. Exactly
    delta_ij = d*X + 1/8 + n'*(gamma_j-gamma_i).
Thus the transport matrix is affine in the bounded rescaled intrinsic variables even when the aspect ratio varies. The companion exact checker verifies the cocycle and symbolic marginal identities.

## 2. Limit setup

Suppose there is a sequence of embedded ray_4 tori with y tending to infinity. Apply the earlier joint symmetry classification and pass to a subsequence in one of the two canonical sign families (representatives 1 and 3 in ring4_full_signs.json, 1-based). Use the earlier compactification: fix edge 01 as axis, take transverse coordinates P_i, normalized axial coordinates tending to 0 for A and 1 for B, with P_0=P_1=0. All variables x,gamma,rho,P,c01 in that compactification stay bounded; pass to a convergent subsequence. For this argument no strict inequality is assumed to survive the limit. Let e_i,f_j now denote the **limiting planar transverse ring edges**, and let a_i,b_j now denote their nonnegative lengths (scalar notation in the remainder). By the transport theorem and the limiting ring metric equations,
    0 <= a_i,b_j <= 1/2; sum a_i=sum b_j=1.
The weak full sign model has all cyclic A triples with the same oriented area sign and all cyclic B triples with the same oriented area sign, namely both negative in the chosen ambient orientation. This follows from the minors with three vertices from one ring and one from the other (the axial coordinate reverses sign for B). The 4x4 matrix of K4 determinant signs in cyclic edge order is
    R1            R2
    -+--          ---+
    --+-          +---
    ---+          -+--
    +---          --+-
where the limiting tetrahedral determinants for an A-edge/B-edge pair are minus the planar cross products of their vectors. Multiply the cross-product matrix by -1 and permute the columns to place the rare nonnegative entries on the diagonal. This gives a weak balanced Laplacian matrix L: diagonal nonnegative, off-diagonal nonpositive, row and column sums zero.

Suppose both limiting ring edge sets span R^2. Their 4x4 cross-product matrix has rank exactly two by factoring through the two-dimensional plane. A balanced Laplacian of size four and rank two has precisely two connected components. Proof: a directed graph with edge weights -L_ij for i != j is balanced, so its strongly connected components cannot have nonzero edges between them (apply balance to a source component of the condensation DAG). On each component the kernel consists of constants by the maximum principle; hence the rank is four minus the number of components. The only partitions are 2+2 and 3+1.

## 3. Exclude the 2+2 case, including nongeneric signs

Each pair of rows in one block is parallel to both B edges in the other block, and vice versa. Since both ring edge sets span R^2 and both blocks have rank one, these pairs are nonzero parallel edges, opposite within each pair by closure. If an opposite pair were cyclically adjacent, the ring would have coincident opposite vertices, and two cyclic triples of its vertices would have nonzero opposite area signs, contradicting the weak full sign model. Thus both rings are nondegenerate parallelograms.

Write their cyclic edges as (u,v,-u,-v) and (w,z,-w,-z). Let their lengths be (a,b,a,b) and (c,d,c,d), with a+b=c+d=1/2. The K4 sign matrices above force w parallel to u and z parallel to v: for example the entries in rows 0 and 2 and columns 0 and 2 all have the same weak sign, but the two rows are negatives. Thus those cross products vanish. The triple signs imply the two rings have the same cyclic orientation. Consequently, with unit directions U0,V0 along u,v,
    u=a U0, v=b V0, w=sigma*c U0, z=sigma*d V0,
where sigma=+1 for R1, -1 for R2 (read the rare sign of the pair u,z). This statement uses only strict nonparallelism of u,v and the nonzero lengths, not general position of the eight limiting points.

The two nonclique minors (0,1,4,5) and (2,3,6,7), evaluated at limiting heights 0,1, impose opposite weak inequalities on (a-c)/2, after division by the common nonzero absolute area of the unit direction basis. The exact sign check in the companion script proves that they force a=c for either R1 or R2. Hence b=d.

But the cross-edge metric equations of the compactification give
    u dot w - u dot z + v dot w + v dot z = 0.
Here is a direct exact derivation of the residual identity. At t=0 the cross correction equations are
    c01 + rho_j-rho_i - (1+2n_ij)*(gamma_j-gamma_i)
         = X_ij^2 - |P_j-P_i|^2.
In lexicographic ring order A x B (16 entries), two left-null vectors of the correction matrix are
    N0=(0,0,-1,1, 1,0,0,-1, -1,1,0,0, 0,-1,1,0)
    N1=(1,-1,0,0, 0,1,-1,0, 0,0,1,-1, -1,0,0,1).
The horizontal lifts are x=(0,h,a,h+c,-1/2,h+1/2,a-1/2,h+c+1/2), where h=x1. The transverse positions are P_A=(0,u,u+v,v), P_B=(0,w,w+z,z). Write U=u dot w,V=u dot z,W=v dot w,Z=v dot z. The two exact residuals are
    N0 dot RHS = (4U-4V+4W+4Z+8ac-4a+4h+1)/2,
    N1 dot RHS = (4U-4V+4W+4Z-8ac+4a-4h-1)/2.
Their sum gives the identity. At a=c and b=d its left side equals sigma*(a^2+b^2), which is nonzero. Contradiction.

## 4. Exclude the 3+1 case, with collapsed edges allowed

A singleton block has zero row and column. Since both other ring sets span the plane, precisely one edge of each ring is zero. The two nonzero triples of edge vectors are nondegenerate triangles with perimeter one. The rare entry pairs the zero A edge i with the zero B edge i+1 in R1 or i-1 in R2. Simultaneous rotations of the labels by 2 preserve the canonical weak sign models once the all-A and all-B minors (identically zero at t=0) are ignored. They preserve the marking up to lattice isometry and gauge. Thus we may take i=0. The checker verifies these symmetries and the following parallelism constraints.

For R1 the zero edges are e0=f1=0. The equality of the corresponding duplicate vertices in each ring and the weak full signs force the cross product of e1 and f0 to vanish: the quadruple (0,1,3,4) inherits both signs after identifying the coincident vertices. The cyclic orientation and the remaining K4 signs force e1 and f0 to point in the same direction (e1 crossed with f2 has the same nonzero sign as f0 crossed with f2). For R2 the zero edges are e0=f3=0, and the analogous quadruple is (0,4,5,7); e1 and f2 point in the same direction.

Rename the surviving A triangle edges as (a*n,u,u'), and the surviving B triangle edges as (c*n,v',v), where n is their common unit base direction and a,c>0. Thus u and v' are on the clockwise side of n, u' and v on the opposite side. In R1, u=e2,u'=e3,v'=f2,v=f3, c=|f0|. In R2, u=e2,u'=e3,v'=f0,v=f1, c=|f2|. Applying N0+N1 to the cross correction equations, imposing the zero edges, the common base directions, and the two perimeter identities, yields in both cases
    |u| |v| - u dot v = 1/2 - a - c.                (*)
This is another exact polynomial identity checked by the companion script. The transport identity also identifies its left side as the limiting cross slack for the indicated u,v pair.

Let the direction angles of u,u',v',v with respect to n be -theta, phi, -psi, chi, respectively, all four named unsigned angles strictly between 0 and pi. Both triangles close and have clockwise orientation. The K4 sign matrix in this order implies
    theta >= psi,   chi >= phi,   phi+psi >= pi.
(The three signs are cross(u,v')>=0, cross(u',v)>=0, cross(u',v')>=0.) Put p=cot(theta/2), q=cot(phi/2), r=cot(psi/2), s=cot(chi/2), all positive. These inequalities imply p<=r, s<=q, qr<=1. From triangle closure and perimeter one,
    a=(1-pq)/2,  |u|=q*(1+p^2)/(2*(p+q)),
    c=(1-rs)/2,  |v|=r*(1+s^2)/(2*(r+s)).
For example the vertical closure is |u|*sin(theta)=|u'|*sin(phi), and the perimeter identity is |u|*(1-cos(theta))+|u'|*(1-cos(phi))=1; substitution of the half-angle formulas gives these expressions. In particular pq<1 and rs<1. A direct dot product gives
    2*(|u|*|v|-u dot v) = qr*(p+s)^2/((p+q)*(r+s)).
Let z=qr<=1, U=p/r<=1, V=s/q<=1. Since
    (p+s)/(p+q) >= V,   (p+s)/(r+s) >= U,
the left side of the last display is at least z*U*V. But
    z*U*V - (pq+rs-1) = (1-z)+z*(1-U)*(1-V) > 0.
Strictness holds if z<1; if z=1 it follows from pq<1 and rs<1, which imply U,V<1. Thus
    |u|*|v| - u dot v > (pq+rs-1)/2 = 1/2-a-c,
contradicting (*). This excludes every 3+1 limit with both rings spanning the plane.

## 5. Consequence and remaining gate

**Conditional asymptotic theorem:** Every sequence of embedded Type 7 ray_4 realizations with y tending to infinity has, after the bounded normalization and passage to any convergent subsequence, at least one limiting ring whose transverse vertices are collinear. In particular no sequence can have a fixed positive lower bound on the planar area spanned by each limiting ring.

This is a uniform exclusion of all limits with two spanning rings, not merely of the symmetric two-plane construction or of nondegenerate parallelograms. No assertion that the limit itself must be embedded has been used. The orientation signs of nonclique quadruples were imposed only weakly.

If exactly one ring is collinear while the other spans R^2, the same Laplacian matrix has rank one. There is a single two-vertex block and two singleton blocks. Every singleton column (or row on the collinear side) forces the corresponding edge to be zero because the other ring spans. Thus the collinear ring has exactly two nonzero edges of lengths 1/2, necessarily opposite, and the other two edges vanish. The remaining possibilities are one spanning ring and one such collapsed two-stick ring, or two collinear rings (possibly in distinct directions). These are the next targets. The previously certified fully collinear t=0 witness still exists, so this theorem does not prove eventual nonexistence. Neither positive-t R1 nor R2 has been closed.

## Reproduction

Run the companion check_limit.py using Python 3 with SymPy and assertions enabled. It checks the exact finite shift, sign and polynomial identities; the balanced-Laplacian and half-angle inequalities are the hand proof above. The earlier compactification and SAT orientation archives must be independently audited/replayed for the full implication.
