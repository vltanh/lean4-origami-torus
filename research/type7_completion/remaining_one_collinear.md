# Ray 3: a collinear cap cannot have a noncollinear partner

## Result and scope

There is no sequence of actual canonical ray-3 realizations with
`y → ∞` for which exactly one of the two transverse cap limits is
collinear. Coincident vertices and arbitrarily disparate collapsing edge
lengths are included.

The proof combines a finite weak-sign classification, exact stress
inequalities, and a signed same-cap determinant. The finite steps are
implemented in `remaining_one_collinear.py` and `remaining_one_v.py`.
They use the necessary orientation and linking conditions justified in
`geometric_audit.md`, and the uniform metric bounds proved in
`relative_cap_bounds.md`.

This is a computer-assisted asymptotic research theorem. It gives no
numerical height threshold and is not yet a Lean theorem. In particular,
it does not exclude a limit in which both caps lie on the same line.

## 1. The exact limiting stress

Put `t=1/y²`, and use the cyclic caps

```
A=(0,1,4,5), B=(2,3,6,7).
```

For a short edge, write `h=-X>0` and `gamma=V/t`. The established bounds
give `|gamma|<(1/2+t)h`, spatial length squared `h²+t gamma²`, and
normalized axial increment `O(t h)`, with constants independent of the
edge length. Each cap's four `h` values sum to one. Thus its limiting
transverse edges have lengths exactly `h`, and their perimeter is one.
An entire cap cannot collapse to one point.

For A-edges `e_i` and B-edges `f_j`, with limiting lengths `h_i,k_j`, the
exact finite-`t` stress identity implies

\[
 F=2\sum_{i,j}M_{ij}(h_i k_j-e_i\cdot f_j)-P_A P_B=0,
 \qquad
 M=\begin{pmatrix}1&0&1&1\\1&0&0&0\\1&1&1&0\\0&0&1&0\end{pmatrix},
\]

where `P_A=sum h_i`, `P_B=sum k_j`. Both perimeters initially equal one.
The displayed homogeneous equation remains valid after independent
positive scaling of either cap. The archived-cocycle calculation is
checked in `verify_cap_limit.py` and `remaining_one_v.py`.

An exact phase-preserving marked symmetry exchanges the caps. It
therefore suffices to assume that A is collinear and B is noncollinear.
Choose transverse coordinates so that A's line is horizontal, and write
its scalar vertex positions as `a=(a0,a1,a4,a5)`. Write B's vertex
coordinates as `x=(x2,x3,x6,x7)` and `y=(y2,y3,y6,y7)`.

## 2. Complete finite classification

There are 74 nonconstant weak orders of four labelled scalar positions.
These include every coincidence pattern. Each of `a`, `x`, and `y` has
such an order: a constant x or y would make B collinear.

Let `beta` be the four signs of B's sorted three-point areas. The affine
cofactors of four planar points sum to zero. For a noncollinear
configuration they have both signs, leaving 50 possible ternary beta
patterns. No realizability of these sign patterns is assumed.

The full necessary ray-3 orientation system, the two horizontal
unlinkings, and long linking of magnitude two have 1,888 generic sign
completions. Their enumeration is exhaustive; the verifier exports the
base formula with all 1,888 completions blocked as a coverage CNF.
Only actual nonzero limiting brackets constrain these generic signs.
All zero brackets remain unrestricted.

For each A pair and B pair, the ordered limiting bracket has sign

\[
 \operatorname{sgn}[A_i,A_j,B_k,B_l]
 =-\operatorname{sgn}(a_j-a_i)\operatorname{sgn}(y_l-y_k).
\]

For a B triple and any A vertex, its bracket sign is minus its planar
area sign. These signs can be tested against all 1,888 models by exact
integer bitsets.

There are also necessary rank-three Grassmann–Plücker conditions on B
and the horizontal and vertical points at infinity. In homogeneous
coordinates `E=(1,0,0)`, `F=(0,1,0)`, `B_i=(x_i,y_i,1)`, their brackets
are

```
[E,F,B_i]=1, [E,B_i,B_j]=-(y_j-y_i),
[F,B_i,B_j]=x_j-x_i, [B_i,B_j,B_k]=the indicated beta sign.
```

The three summands of each exact Grassmann–Plücker zero sum either all
vanish or include both signs. This necessary test retains all zero
cases; it is not used as a sufficient realizability criterion.

The first bitset and one-infinity-point filter leaves 642 cells in
`(a-order,y-order,beta)`. Adding x's order and the second infinity point
leaves 4,786 cells. These are complete covers by necessary conditions.

### Exact stress inequalities on each cell

Write the scalar A-edge differences as `e_i` and the B horizontal
differences as `f_jx`. Since A is horizontal, `h_i=|e_i|`. Put

\[
 \delta_j=|f_j|-|f_{jx}|\geq0,
 \qquad
 \lambda_j=2\sum_iM_{ij}h_i-P_A.
\]

Then

\[
 F=F_0+\sum_j\lambda_j\delta_j,
 \quad
 F_0=2\sum_{i,j}M_{ij}(|e_i||f_{jx}|-e_i f_{jx})
       -P_A\sum_j|f_{jx}|.
\]

An edge has `delta_j>0` exactly when its vertical difference is nonzero.
In a fixed weak order, every absolute scalar edge difference is linear
in the positive consecutive gaps. Therefore `F0` is bilinear in A's
gaps and B's horizontal gaps. Its coefficients are exact integers,
obtained by substituting the step vector `1[rank>gap]` in each factor.
Each lambda is likewise linear in A's positive gaps.

The verifier excludes a cell when all these coefficients have one weak
sign and at least one strictly contributes. In a norm term the relevant
delta is strictly positive; in `F0` every product of gaps is strictly
positive. This checks whole cones of positions, not unit-gap samples.

The individual norm inequalities exclude 4,286 cells. In all remaining
500 cells, B has an opposite coincident pair. This follows from its two
zero area signs: if their common pair were distinct, both other vertices
would lie on the line through that pair, contradicting noncollinearity.
The x and y weak orders also confirm the coincidence.

If `B2=B6`, the two equal norm-excess pairs are edges `(23,36)` and
`(67,72)`. If `B3=B7`, they are `(23,72)` and `(36,67)`. Grouping the
corresponding lambda coefficients excludes another 160 cells. The
verifier checks each grouped coefficient on the full positive-gap cone.

All remaining 340 refined cells, representing 60 unrefined cells, have
three A vertices coincident and one tip. Their labels are exactly:

| A tip | B's coincident pair |
|---|---|
| 1 or 5 | 2,6 |
| 0 or 4 | 3,7 |

For every surviving cell the verifier finds an exact, cocycle-checked
phase-preserving marked symmetry taking it to

```
A0=A1=A4=0, A5=p;
B2=B6=0, B3=v, B7=q,
```

where `v,q` are nonzero and nonparallel. This is the canonical one-V
family. Since each cap has perimeter one,

```
|p|=1/2, |v|=chi>0, |q|=s>0, chi+s=1/2.
```

## 3. Directional limits with arbitrary edge scales

Let `a=r1-r0`, `b=r4-r1`, with intrinsic lengths `alpha,beta→0`.
Their normalized transverse directions are nonzero by the uniform
relative bounds. On a subsequence the two lengths are comparable or
one dominates the other. The exact marked symmetry `(0 4)(2 6)`, with
intrinsic horizontal reflection, exchanges the two roles while keeping
the limiting tips p and q. Thus only the comparable case and
`beta/alpha→0` need be checked.

If p and q are independent, fix the moving affine frame of actual
vertices `0,2,5,7`. Its normalized axial coordinates are

```
0=(0,0,0), 2=(0,0,1), 5=(1,0,0), 7=(0,1,1).
```

The limiting B vertex 3 is `(u,v,1)` with `u!=0`. The signs of all
nonzero constant bracket coefficients depend only on `sign(u)`,
`sign(v)`, and `sign(v-1)`. There are ten parameter cells: either sign
of u and the five intervals or points `v<0`, `v=0`, `0<v<1`, `v=1`,
`v>1`.

The verifier uses 23 constant bracket polynomials, 27 linear ones that
factor a collapsing A difference, and four quadratic ones that factor
both a and b. It also imposes necessary rank-two Grassmann–Plücker
signs for the six planar vectors `E,F,V,V-F,a,b`, retaining zero
determinants. Comparable directions obey the ternary sign-addition
table; in the dominant case `a+b` has a's limiting direction.

Of the 20 parameter/hierarchy cells, 19 are UNSAT. In the remaining
cell `u<0,v=0,beta/alpha→0`, an additional UNSAT certificate blocks the
single pattern

```
a_x>0, a_y=0, b_x=0, b_y>0.
```

Thus every possible survivor has precisely these coordinate signs. In
physical transverse coordinates this means

\[
 a/\alpha\longrightarrow 2p,\qquad
 b/\beta\longrightarrow q/s,\qquad
 v=-2\chi p.
\]

### Why every bracket link survives arbitrary scales

Each linear link is used only when its four-point set contains the
endpoints of its named difference `a=01`, `b=14`, or `A=04`. Reordering
the bracket and subtracting its first row gives exactly

\[
 \pm\det(r_j-r_i,\ r_k-r_i,\ r_l-r_i),
\]

with the named short difference as the first row. Divide by alpha,
beta, or `max(alpha,beta)` respectively. That row has a bounded
transverse limit and an axial component `O(t)`; the other two rows
converge to the indicated anchors. Thus its error is little-o of the
named scale. This holds even when deviations of B3 or B6 are much
larger than either collapsing A edge.

The four quadratic links are the ordered determinants

\[
 [0,1,4,j]=\det(a,b,r_j-r_0),\qquad j\in\{2,3,6,7\},
\]

with the permutation sign used by the solver. Dividing by alpha beta,
the planar leading term is `cross(a/alpha,b/beta)` because the last
row's height tends to one. Terms containing an axial component of a
or b are `O(t alpha beta)` before division. No comparison of alpha and
beta is used. For comparable edges, using their common maximum as
denominator gives the same conclusion. A vanishing leading coefficient
never constrains the actual bracket sign.

In particular, none of these implications normalizes the missing
displacement 26. Its convergence to zero is sufficient as part of a
bounded anchor row.

### The anchor-parallel branch

If q is parallel to p, the nonparallel B arms imply that p and v are
independent. Instead fix the actual anchors `0,2,5,3`. Vertex 7 has
limiting coordinates `(lambda,0,1)`, `lambda!=0`. The constant signs
depend only on the sign of lambda. The same 27 factored linear links,
four quadratic links, and rank-two signs for `E,F,lambda E-F,a,b`
give four UNSAT cells: two lambda signs and two A-edge hierarchies.
This covers the branch without a metric limit calculation.

## 4. Exact metric identities in the last cell

It remains to exclude the sole independent-anchor survivor. Write
`z=p·q`, so `|z|<s/2`. Let `L=|r2|`, and let `H_i` be the normalized
axial coordinate before the moving affine shear. Then
`2L²t→1/2`. Pass to a subsequence where the bounded intrinsic correction
`x2` converges; its value will cancel.

Put

\[
 C_0=-x_2+\tfrac14+2\gamma_2
     =2R(01,67)+2R(01,72).
\]

The two B edges in this sum tend to q and -q, both of length s. Hence
`C0/alpha→4s`. Since the edge 36 tends to `-v=2 chi p`, the directions
of a and 36 agree. The exact identity
`R(01,36)=alpha/2-gamma_a` therefore gives
`gamma_a/alpha→1/2`.

The collapsing A edges also imply `gamma4→0`, and `h50→1/2` implies
`x5→0`. The exact identity
`R(45,72)=h45/2-gamma45` gives

\[
 \gamma_2\longrightarrow (x_2-\tfrac14)/2,
 \qquad
 \gamma_5\longrightarrow\tfrac14-\tfrac{s}{2}-z.
\]

Polarization of the three prescribed distances to each anchor gives
the exact formulas

\[
\begin{aligned}
 2L^2 H_1&=-C_0+(1-2x_2)\alpha+\gamma_a+2t\gamma_2\gamma_a,\\
 2L^2 H_5&=x_5+\tfrac14+2x_5x_2+\gamma_5-2\gamma_2
                         +2t\gamma_5\gamma_2.
\end{aligned}
\]

Consequently

\[
 H_1/(t\alpha)\longrightarrow 3-8s-4x_2,
 \qquad
 H_5/t\longrightarrow\tfrac32-s-2z-2x_2.
\]

The symbolic verifier derives all these identities from the archived
cocycle rather than assuming them from the limiting picture.

## 5. A strict same-cap bracket closes the cell

Let `M` map the current transverse anchor differences p and q to E
and F. The moving affine shear is exactly

\[
 Z_i=H_i-H_5(MP_i)_x+(1-H_7)(MP_i)_y.
\]

Its coefficients satisfy `H5=O(t)`, `1-H7=O(t)`, and
`MP1/alpha→(2,0)`. Therefore the unknown limiting x2 cancels:

\[
 Z_1/(t\alpha)\longrightarrow 4z-6s<0.
\]

Write a and b in this moving three-dimensional frame. Its affine
transformations and inverses are uniformly bounded in normalized axial
coordinates. The relative short-edge estimate gives `b_z=O(t beta)`.
The directional cell gives `a_y/alpha→0` and `b_y/beta→1/s`.

There is the exact determinant identity

\[
 [0145]=\det(a,a+b,E)=a_yb_z-a_zb_y.
\]

It follows that

\[
 \frac{[0145]}{t\alpha\beta}
 \longrightarrow 6-\frac{4z}{s}>4>0.
\]

Thus the actual bracket is strictly positive eventually, at every
relative collapse rate. Every generic sign completion must satisfy
`chi0145=+1`. Adding this single unit to the surviving directional CNF
is UNSAT. This excludes the final cell and proves the theorem.

## Reproduction and independent replay

```sh
python3 research/type7_completion/remaining_one_collinear.py /tmp/type7-one-collinear
python3 research/type7_completion/remaining_one_v.py /tmp/type7-one-collinear
g++ -O3 -std=c++17 research/orientation_checkpoint/check_unsat.cpp -o /tmp/type7-one-collinear-checker
/tmp/type7-one-collinear-checker < /tmp/type7-one-collinear/independent_um1_vzero_hm1_metric.cnf
```

Replay each of the 26 emitted CNFs with the independent checker,
requiring explicit `UNSAT nodes ...` output. One CNF certifies coverage
of the 1,888 generic models. The other 25 consist of 19 directly excluded
independent-anchor cells, the exhaustive survivor-pattern check, its
metric-sign exclusion, and four parallel-anchor cells. The checker has
zero exit status for both SAT and UNSAT, so its text must be checked.

The reduction also writes the 340 surviving cells and their checked
canonical marked permutations to JSON. All numerical calculations in
the reduction and directional construction are exact integer or rational
arithmetic. Dependencies are repository data, SymPy, and shared libz3;
there are no scratch-script dependencies.
