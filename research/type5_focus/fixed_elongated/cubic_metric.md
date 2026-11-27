# Type 5: cyclic deficit inequalities and an exact cubic metric encoding

**Status: open. Neither any of the 19 fixed-elongated branches nor the hexagonal B1.1 chambers have been excluded.** This checkpoint exploits all three universal vertices and a sparse signed Gram pivot rather than adding a new marking or an orientation subcase. The earlier strict-support/K4 lemma and marking classification remain premises requiring audit.

## 1. Cyclic deficits in the three universal-vertex gauges

At a universal vertex v, choose intrinsic lifts of its seven neighbors using the incident edges, and translate both the intrinsic and extrinsic positions of v to zero. In physical Euclidean intrinsic coordinates p and extrinsic coordinates r, let

    S_ij = r_i dot r_j - p_i dot p_j
         = (|p_i-p_j|^2 - |r_i-r_j|^2)/2.

The equality holds because every neighbor's radial norm is preserved. Metric contraction gives S_ij>=0. Consecutive link neighbors have S_ij=0. The three links, in one of their two cyclic directions, are

    v=1: 0 2 5 7 4 6 3
    v=2: 0 1 5 6 3 7 4
    v=5: 0 3 7 1 2 6 4.

The finite checker confirms in each gauge that every nonconsecutive *edge* has nonzero shift, hence strict S_ij>0 by uniqueness of shortest intrinsic edge lifts. The diagonal is zero. Also S=R R^T-P P^T has at most three positive and two negative eigenvalues, and rank at most five.

Write a_i=S_(i,i+2), b_i=S_(i,i+3), using cyclic link indices, not vertex labels. All b_i are strictly positive, including the single missing gap-three edge of each link. To see this, if S_ij=0 then the lifted map preserves all three distances of the triangle (v,p_i,p_j). A 1-Lipschitz map preserving the vertex distances of a triangle is affine isometric on the whole triangle: for x=sum lambda_k p_k and c=sum lambda_k r_k, compare the weighted sums of squared distances of f(x) to r_k and x to p_k. The variance terms are identical, so |f(x)-c|^2<=0. The two endpoint rays cannot coincide or be antipodal, by injectivity and strict support. The triangle thus contains initial segments of all rays in their smaller angular sector. Those segments map by one planar isometry, so their full radial edge vectors do too. Both combinatorial arcs between the gap-three endpoints contain a known nonconsecutive edge (checked from the cocycle), which would then have zero slack, a contradiction. No nonclique genericity assumption is used.

Likewise a_i and a_(i+1) cannot both vanish. Three consecutive rays with zero pairwise deficits are congruent to their intrinsic planar rays. Two consecutive such triples share a nondegenerate face, so a single planar isometry maps all four rays, which contradicts strict positivity of b_i.

## 2. New quadratic inequality, including zero-gap degeneracies

For any five successive link indices the deficit submatrix has form

    [ 0 0 a b c ]
    [ 0 0 0 d e ]
    [ a 0 0 0 f ]
    [ b d 0 0 0 ]
    [ c e f 0 0 ]

where a=a_i, d=a_(i+1), f=a_(i+2), b=b_i, e=b_(i+1), c=b_(i+4). Its determinant is exactly 2*a*d*f*(b*e-c*d). The inertia bound implies this determinant is nonnegative. If a,d,f are all positive, division gives b*e>=c*d.

This same inequality holds in all zero cases. For d=0 it is immediate. If a=0 then the first three rays are congruent to three intrinsic planar rays. Strict support implies their two consecutive positive angular steps sum to less than pi (otherwise the three rays do not lie in an open semicircle). Consequently the middle ray is a positive linear combination of the first and third, with coefficients alpha,beta>0, in both intrinsic and extrinsic coordinates. The corresponding rows of S satisfy the same combination, so d=alpha*b and e=alpha*c+beta*f. Hence b*e-c*d=b*beta*f>=0. If f=0, use the last three rays instead: b=alpha*a+beta*c, d=beta*e, giving b*e-c*d=alpha*a*e>=0.

Thus for all seven indices in all three gauges,

    b_i*b_(i+1) >= b_(i+4)*a_(i+1),
    a_i+a_(i+1)>0,   b_i>0.

These are exact conditions on affine slack variables. At fixed metric only 18 unknowns are needed (14 intrinsic coordinates and four missing slacks in gauge 1). For an edge its slack is affine in the lifted coordinates; for missing chords other gauges change the slack by half the difference of two squared chart displacements, also affine. The checker verifies that the three gauge lifts of each missing pair differ by distinct lattice shifts. At most one gauge can have zero slack for that pair, since two different intrinsic straight segments would map to the same straight extrinsic segment, contrary to injectivity. The optional --extra constraints impose this strict condition.

## 3. Sparse affine pivot: exact cubic equations for the metric

Gauge at 1 and use intrinsic coordinates (x_i,b_i) with norm squared x^2+w*b^2, w=y^2. Define the 9-by-9 symmetric signed Gram matrix H indexed by the seven rays and two fixed negative directions 8,9:

    H = [ S      P               ]
        [ P^T   -diag(1,1/w)    ],

where P's rows are (x_i,b_i). Its Schur complement against the negative block is exactly the Euclidean centered Gram G=S+P diag(1,w) P^T. The prescribed distances can be realized in R^3 spanning that space precisely when H has inertia (3,2) and rank five.

A fixed pivot consists of rays (2,5,7,4). Put A=S_27, B=S_24, C=S_54. These slacks are strict positive edge slacks, and its matrix M and scaled inverse N are

    M = [ 0 0 A B ]       N = [ 0  0  C 0 ]
        [ 0 0 0 C ]           [ 0  0 -B A ]
        [ A 0 0 0 ]           [ C -B  0 0 ]
        [ B C 0 0 ]           [ 0  A  0 0 ].

Exactly M*N=A*C*I, det M=(A*C)^2, and M has inertia (2,2): its offdiagonal two-by-two block is invertible. No choice of a generic pivot or lower bound on A,C is required.

For the five remaining indices J=(0,3,6,8,9), define

    L_ij = A*C*H_ij - H_(i,B0) N H_(B0,j).

These 15 upper-triangular entries are polynomials of degree at most three in the 18 unknowns, since H and N are affine. The necessary and sufficient metric equations are exactly

    L_ij = u_i*u_j (i,j in J, i<=j),   sum u_i^2 > 0,

with five additional variables. Indeed the rank-one positive semidefinite Schur complement adds exactly one positive eigenvalue to the (2,2) pivot. Conversely any Euclidean realization of rank three supplies a real rank-one factor u of this scaled complement. This is a 23-variable formulation with 15 **cubic** metric equations instead of expanded high-degree Gram determinants. It is an alternative to the prior 14-variable reconstruction, not a reduction in continuous dimension.

In an embedded flat realization, u_8 and u_9 cannot both vanish. If they did, the two negative directions would belong to the nondegenerate four-dimensional pivot span. Its orthogonal complement to the negative plane would then have dimension two, so the four pivot rays' extrinsic projections and vertex 1 would be coplanar. This contradicts the strict K4 lemma, since these five vertices form a K5. The --extra mode imposes the stronger nonzero condition.

A further algebraic elimination is available, without an additional genericity premise. Each of the three outside rays 0,3,6 has exactly one missing distance to the four pivot rays, and its three known pivot neighbors together with 1 form a K4. Fix the intrinsic coordinates and the two negative residual components. The two equations L_(i,8)=u_i*u_8 and L_(i,9)=u_i*u_9 are linear in the missing pivot slack and u_i. Their coefficient matrix is nonsingular at actual solutions: otherwise there is a nonzero signed-space vector orthogonal to the three known pivot rays and to both negative directions. Such a vector is a pure extrinsic vector orthogonal to three independent extrinsic anchor rays, impossible. Solve those equations; the last missing slack S_06 follows linearly from L_06=u_0*u_6. The three residual diagonal and two known offdiagonal equations remain, in addition to the three negative-block residual equations. Equivalently, choose a nonzero negative residual component, use the ratio of the other to it, and eliminate the common scale by L_kk=u_k^2>0. This gives two projective reconstruction charts, each with 14 intrinsic variables and one ratio, seven remaining metric equations, and rational expressions with explicitly nonzero denominators. This latter optional rational elimination is a hand derivation, not implemented or solver-tested here.

## 4. Exact embedding tests on polynomial coordinates

For each index i let T_i consist of its four inner products with the pivot rays, followed by u_i (zero for pivot rays and the origin). The cubic equations imply that the T_i realize H in a nondegenerate signed five-dimensional space with inner product M^-1 on the first four coordinates and 1/(A*C) on the last coordinate. The negative basis vectors T_8,T_9 have inner product block -diag(1,1/w). Thus the polynomial coordinates

    C_i = T_i + x_i T_8 + w*b_i T_9

are the orthogonal projections onto their three-dimensional positive complement. Their Euclidean Gram in that complement is exactly G. The ordinary five-coordinate representation of C is an injective linear image of the three-dimensional extrinsic realization. All simplex incidences and affine dependencies are consequently unchanged. Every coordinate of C has degree at most two.

In --full mode require every clique tetrahedron nondegenerate, and forbid every disjoint-simplex sign-compatible affine circuit of support two to five, using all appropriate coordinate minors of C (five coordinate axes rather than three). For n<=4 the rank condition uses all affine minors with n-1 axes; for n=5 rank deficiency is automatic since C lies in a three-dimensional subspace. A minimal dependence is one-dimensional, so some choice of n-2 coordinate axes gives all nonzero alternating cofactors. The checker forbids the specified signs, not coplanarity itself. Consistent nonzero intrinsic face orientations and signed double-area sum -2 imply the degree-one intrinsic PL homeomorphism as in the prior proof. Consequently the full system is exact under the inherited marking/strict-support premises, with all metric equations at most cubic and no additional continuous embedding variables. It is not a claim that the whole Boolean system has degree three: incidence minors have degrees up to eight for rank tests and six for circuit cofactors.

## 5. Verified progress and limitations

The new quadratic necessary system (without --extra) is feasible at the hexagonal metric and each of the four maximal elongated branches. verify_cubic.py stores rational models from actual Z3 queries and checks every corresponding inequality using Fraction; the determinant and sparse inverse identities are checked by SymPy. These five exact witnesses are not Euclidean rank-three realizations. **Do not pursue infeasibility of the quadratic relaxation in these branches.**

The local tests used transcribed current repository face and cocycle inputs, the earlier phase propagation, and the exact branch labels. The five rational checks passed and both symbolic identities passed. The final import version was not replayed via a fresh checkout; it uses the already existing repository generate.py and phase.py rather than the local transcription. An initial 2-second quadratic pass gave SAT at the hexagon and ten of nineteen elongated labels, UNKNOWN for the other nine. Adding all 6-by-6 principal deficit determinant equalities in each of three gauges returned UNKNOWN at 3 seconds for the hexagon and the four maximal branches. In an initial cubic run the hexagon and 00120221 returned UNKNOWN at 5 seconds; a later parallel run reported UNKNOWN for 15 elongated labels before its external timeout, with the other four not decided. Full cubic systems with the extra conditions at hex and 00120221 returned UNKNOWN at 1 second. These are not exhaustive runs and establish no exclusions. Neither a certified full metric witness nor a certified contradiction was obtained.

Run from this directory:
    python verify_cubic.py
    python cubic.py /tmp/type5-quad quad
    python cubic.py /tmp/type5-rank rank
    python cubic.py /tmp/type5-cubic cubic
    python cubic.py /tmp/type5-cubic-full cubic --full --extra
    python ../solve.py 5000 /tmp/type5-cubic/*.smt2

The key remaining gate is the simultaneous signed rank-one compatibility and embedding condition, not another decomposition into more orientation cases. All nineteen fixed-elongated branches remain open; the fixed-hexagon attack is still open. No Type 5 universality classification or independent proof audit is claimed.
