# Active Type 4 case: coverage audit and the limit of pure linking

The active case is `ray2_2` at `tau=1/2+10^6 i`, with labels `20220012`
and gauge `(0,0,0,-1,0,0,0,-1)`. Its selected cap cycles are 145 and
0273; vertex 6 lies in the broadened intervening strip. This note does
not close the case.

## Coverage and metric formulation

A fresh exact replay checked both hard-coded cocycles in
`type4_focus/type4_gap_enum.py` against the current archived ray markings,
after gauging all edges from vertex 4 to zero. They agree. The replay gave
56/9 relative cells, 10/4 maximal cells and 6/2 symmetry representatives.
The root roadmap's eight label/cap rows agree with those representatives.
In particular `ray2_1` is 456/1273 in its canonical labels, carried to
145/0263 by the checked automorphism `(7,6,2,3,5,4,1,0)`.

The finite cover uses closed, broadened intervals, so it does not discard
strip endpoints or collapsing cap edges. Eliminating two center variables
is valid: intervals `[L_s,U_s]`, `[L_t,U_t]` admit
`119/250 < t-s < 131/250` precisely when both intervals are nonempty and
`L_s+119/250<U_t`, `L_t<U_s+131/250`. The pairwise lower/upper comparisons
in the generator implement these inequalities.

The signed-Gram pivot is sound. Its off-diagonal two-by-two block is
invertible because `A,C>0`, and therefore has inertia `(2,2)`. The identity
`M*N=A*C*I` makes the imposed rank-one positive Schur complement
`U*U^T/(A*C)` equivalent to total inertia `(3,2)` and rank five. Removing
the fixed negative two-dimensional block gives a Euclidean Gram matrix
of rank three. This remains valid when the nonedge slack `B` vanishes.

The full augmented-Gram circuit tests also retain degeneracies. For a
minimal affine dependence on `n<=5` vertices, its Gram matrix has rank
`n-1`; its adjugate is a positive scalar times the kernel vector's outer
product. The signed first-row cofactors therefore detect its positive and
negative supports after normalizing the first kernel coordinate positive.
Every forbidden simplex intersection contains such a conformal minimal
dependence. These are algebraic sufficiency/necessity checks; the inherited
geometric two-gap theorem and strict-K4 theorem remain prerequisites.

## Both linking alternatives have actual geometric witnesses

The existing integer H13 coordinates in
`type4_focus/verify_h13_sign_witness.py` give a generic, embedded Type 4
surface with strict local support and the mixed-side condition. They are
**not** a flat metric realization. For the active cap sets their first
coordinates satisfy

    r1.x = r4.x = r5.x = 0,
    min(r0.x,r2.x,r7.x,r3.x) = 608,
    r6.x = 452.

Thus the triangle and quadrilateral convex hulls are strictly separated,
and vertex 6 lies strictly between them. The exact integer checker
`linking_witness.py` verifies all 608 vertex-disjoint simple-cycle pairs.
Their linking values are those of `q(m,n)=-m*n` in the second marking.

The cap-preserving automorphism `(0,1,3,2,5,4,6,7)` fixes vertex 6. The
checker verifies its face action and marking action, including the lattice
reflection `(m,n)->(-m-n,n)` and integer vertex gauge. Applying it to the
same coordinates gives linking form `q(m,n)=m*n+n^2`, again with all 608
pairs checked exactly.

These cover both possible linking forms up to ambient reflection. Indeed
`q(1,0)=0` and discriminant one give `q(m,n)=B*m*n+C*n^2`, `B=+/-1`.
Disjoint triangle pairs have slopes `(0,1)` and `(1,-1)`, so `|C|<=1`
and `|C-B|<=1`. Hence `C=0` or `C=B`.

**Consequence:** strict local support, embeddedness, cap-hull separation,
the ordering of vertex 6 between the caps, and all homological linking
conditions cannot by themselves exclude this case. A successful proof
must use the flat edge metric or quantitative consequences of it. These
witnesses are not asserted to meet the finite metric, cap widths, phase
bounds, or cubic equations, and do not establish feasibility of the full
active system.

Reproduction:

    python3 research/type4_completion/linking_witness.py

The check uses integer arithmetic only and passed.
