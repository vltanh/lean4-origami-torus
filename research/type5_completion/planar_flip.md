# The two-flip planar family cannot be inflated at the hexagon

**Result.** At the modulus x=1/2, y=sqrt(3)/2, no member of the
three-parameter planar family in Doyle--Lander--Schwartz--Trettel,
[*A Universal 8-Vertex Origami Torus Triangulation*, §3.1](https://arxiv.org/html/2611.21909v1#S3.SS1),
with the listed intrinsic triangles positively oriented, has an embedded
vertical lift on the Type 5 triangulation obtained by the flips
12 -> 05 and 67 -> 12. In fact every sequence of strictly convex projected
diagonal flips from that family reaches only three labeled triangulations;
the displayed one is the only Type 5 state.

This excludes an entire proposed universal construction, not Type 5
existence at the hexagon. It is independent of the elongated F1 ledger.
No new Lean theorem is claimed.

## 1. Coordinates and exact parameter domain

Use the source's labeling, and multiply the physical second coordinate by
y. Shear it by Y -> Y-bX, where b=1/2-2k. Write l=lambda and
c=1/2-k+2k^2=(3/4+b^2)/2. The eight projected points become

| i | X | Y-bX |
|---|---|---|
| 0 | 0 | 0 |
| 1 | u | 2ku/l |
| 2 | u-1/2 | (1/2-u)(1-2k) |
| 3 | -k-bl | lc |
| 4 | k | c |
| 5 | u-1/2 | c |
| 6 | u-k | 0 |
| 7 | u | c-(u-k)/(1-l) |

Vertical liftability is unchanged by this invertible affine coordinate
change (with heights left fixed). The domain is

    0 < k < u < 1/2,  0 < l < 1,
    g = c*l*(1-l) - (u-k)*l - 2*k*u*(1-l) > 0.

These are the source's sufficient conditions specialized to the hexagon.
They are also necessary for positivity of all sixteen intrinsic triangles
as oriented in the source, when l is not 0 or 1. To see this, write D =
l+2k(1-l), d=u-k, and let I_ijk denote the signed doubled intrinsic area
in the source's scaled coordinates. Exact identities are

    I_024=(1-2u)/4,
    I_043=(4k^2-2k+1)D/4,
    I_012=u(1-2u)D/(2l),
    I_167=kg/(l(1-l)),   I_174=dg/(l(1-l)),
    I_264=(1-2k)(4d^2-2d+1)/4,
    I_347=dF/(2(1-l)),
    F=(4k^2-2k+1)(l-1)^2+(1-4k)(l-1)+1.

The first three give u<1/2, D>0, and u/l>0. The next two give k
and d the same nonzero sign. If k<0, then u<k<0, l<0 and D<0, a
contradiction. Hence k,d,u,l>0; also k<1/2. Since F has positive
leading coefficient and discriminant -3, I_347>0 forces l<1.
Finally I_167>0 gives g>0. The checker establishes the converse (all
sixteen intrinsic areas positive) and all source edge-length identities
by exact rational arithmetic. Thus the proof is not restricted to the
two special parameter choices in the paper.

Every point of this open domain has an open-unit-cube parametrization:

    k=K/2,
    L=2k^2+(1/2-k)R, l=L/c,
    H=L+2k(c-L),
    u=k+T*(c-L)*(L-2k^2)/H,

where 0<K,R,T<1. Indeed g>0 gives lc>2k^2, and the upper bound
on u is U=k+(1-l)(lc-2k^2)/D. The denominators c,H are positive.
The exact checker pulls each needed polynomial factor back to this cube,
clears positive denominators, and proves its strict sign by nonnegative
Bernstein coefficients with at least one positive coefficient (or their
negatives). All coefficients are rational. This is a certificate, not
a numerical feasibility test.

## 2. Seven exhaustive order patterns

For sorted triples let A_ijk be the signed doubled projected area.
Fifty of the 56 areas have fixed nonzero signs on the whole open domain;
the checker verifies each one by the preceding coefficient test.
Only 023,123,234,235,236,237 can vary; each is a nonzero rational
function. At vertex 2 all six rays to 0,6,1,7,4,5 are in the right
halfplane, with strictly positive ordered pair determinants. Their
angular order is therefore exactly

    0,6,1,7,4,5.

In the generic case the six signs relative to ray 23 have at most one
change along this order, in either direction. A decreasing mixed
sequence would require A_023>0 and A_235<0. Put
E=1-2k-2(1-k)l and J=(1-4k)l+2k+2u-1. Exact identities give

    A_023=-k(2u-1)E/2,
    A_235=(-2k^2+2ku-u)J/2,
    J(U)=-2k(1-l)E/D.

If A_023>0, then E>0, so J(u)<J(U)<0, implying A_235>0.
The decreasing mixed sequence is impossible. Thus the seven cuts in the
six-ray order cover all generic parameters. In the sorted-triple order
023,123,234,235,236,237 they are

    ++++++  -+++++  -+++-+  --++-+  --++--  ---+--  ------.

## 3. All strictly convex flip descendants

The Type 3 source faces are
012 031 024 043 152 136 145 174 167 264 257 276 347 356 375 465.
For each of the seven sign patterns, a finite graph traversal checks
every edge with two incident faces, allows the flip only if the new edge
is absent and the two projected diagonals cross strictly, and repeats to
exhaust all reachable labeled face sets. A strictly convex projected flip
is in an unfolded isometry island: the two triangles lie on opposite
sides of their shared projected edge, so have the same folding orientation.
Using a possibly larger flip graph would also be safe for this exclusion.

All seven graphs have exactly three states; the only state with Type 5
degree sequence 55566777 is reached by 12 -> 05, 67 -> 12. Its faces are

    015 052 031 024 043 136 145 174
    126 264 257 127 347 356 375 465.

The relabeling (0,1,4,3,5,2,6,7) takes it to the repository's Type 5
face list. The verifier checks this exactly.

## 4. Height-sign obstructions

Assign arbitrary real heights z_i. For a sorted quadruple q, define the
linear form

    L_q = sum_i (-1)^i A_(q without q_i) z_(q_i).

The coefficients give the unique planar affine dependence up to scale,
because no three projected vertices are collinear. The sign of the
edge-minus-face height difference at a projected intersection endpoint
is the sign of L_q multiplied by the sign of its coefficient at a
vertex on the edge. This follows by normalizing the affine dependence
to positive barycentric coefficients on the edge. It holds both for a
vertex inside the projected triangle and for two crossing projected
edges.

For each disjoint edge and face, their projected intersection is either
empty or a nontrivial closed segment. Genericity excludes tangencies.
At its two endpoints an embedded lift requires both height differences
to be nonzero and of the same sign; otherwise the linear height difference
vanishes somewhere on the segment. Each such pair therefore gives a
signed equality between two nonzero bracket signs. The following
cycles (a sign after a bracket denotes the multiplier to the next one)
are checked directly from the planar area signs and the actual faces:

| Patterns | Negative cycle |
|---|---|
| ++++++, -+++++ | 0456+ 2456+ 2345+ 2457+ 4567- 3467+ 3567+ 3456+ 0456 |
| -+++-+, --++-+, --++-- | 2346- 2345+ 2456+ 0456+ 3456+ 3567+ 3467+ 2346 |
| ------ | 0126+ 0146+ 0156+ 0136- 0356+ 0135- 1235+ 1237+ 0237+ 0123+ 0236- 0126 |

Each cycle has sign product -1, contradicting the required nonzero
height differences. The checker builds the graph from vertex-in-triangle
and strict segment-crossing tests and finds these cycles; it never
enumerates numerical heights.

The remaining pattern ---+-- is not eliminated by a negative cycle.
Its sign propagation forces, up to an overall reversal,

    L_0124>0, -L_0126>0, -L_0235>0, -L_0346>0, L_1356>0.

Subtract an affine plane from the heights to set z0=z1=z2=0; A_012 is
strict, so this is possible, and every L_q is unchanged. The five
displayed forms then make a 5-by-4 matrix M acting on (z3,z4,z5,z6).
For j=0,...,4 set

    a_j = -(-1)^j det(M with row j deleted).

Laplace expansion (duplicate column) gives a^T M=0 identically.
The exact verifier factors each of the five minors, checks the signs
of its factors by the cube Bernstein argument (using E<0 from
A_023<0 in this pattern), and proves a_j>0 for every j. Thus a positive
weighted sum of the five required strict inequalities would be both
positive and zero. This excludes every parameter in the remaining
pattern, not merely a sampled member.

## 5. Nongeneric parameters and scope

Every rational area function in this argument is nonzero as a function,
so the points where all 56 areas are nonzero are dense in the open
parameter domain. If an embedding existed at a nongeneric point, retain
its heights and perturb the parameters slightly inside the domain.
A finite linear simplicial embedding is open in vertex coordinates:
its simplex ranks are strict and every pair of disjoint simplices has
positive distance. Intersections of simplices beyond their common face
would imply an intersection of disjoint subfaces, by canceling common
barycentric coefficients. These finitely many strict conditions survive
small perturbations. Any finite sequence of strictly convex flips likewise
persists, so the resulting generic point would contradict Sections 3--4.

This proves no Type 5 embedded vertical lift for the entire source fiber
and its strictly convex flip descendants at the hexagon, without assuming
genericity in the conclusion. It does not rule out other planar foldings,
other nonplanar Type 5 realizations, singular limiting triangulations not
obtained by strict flips, or nonlinear deformations starting from a
different boundary point.

## 6. Reproduce

    python3 research/type5_completion/verify_planar_flip.py

Requires SymPy. No LP, SMT solver, numerical tolerance, or sampled
parameter choice is used in the verifier. It checks edge-length identities,
the domain identities, all fixed signs, the seven-pattern cover, all
convex-flip descendants, six negative cycles and the five positive
cofactor weights. The symbolic sign checks and combinatorial arguments
are a research proof; no Lean compilation is claimed.

The next constructive approach must start from a different folding
pattern rather than tuning u,k,l or changing the flip order in this family.
The full hexagonal realization and elongated nonuniversality ledgers
are unchanged.
