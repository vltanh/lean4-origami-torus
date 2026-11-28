# Excluding all six flat C1 families by a normal stretch

For ray 1, no unbounded sequence of realizations has an interior C1
limit with both endpoint caps collinear. The
[closed classification](solver_remaining_c1_flat_limits.md) reduces
that boundary to six exact common-line families. The fourteen
independently checked Boolean obligations below exclude a nontrivial
normal stretch of every family, including all zero-edge endpoints.

Combined with the [regular-cap proof](solver_remaining_c1_turning.md)
and the [one-collinear-cap proof](solver_remaining_c1_collinear_rank.md),
this excludes **the entire interior C1 component for ray 1**.
Here interior means `0<alpha,beta<1`; no assumption is made about
individual edge weights, triangle areas, or relative collapse rates.
Boundary heights and the remaining C0 cases are separate problems.

## 1. A nontrivial bounded normal stretch

The classified limits have transverse coordinates on one line and
axial levels

\[
(0,\alpha/2,1/2,1/2,1/2,\beta/2,0,0).
\]

Use the bounded axis gauge with `P0=P1=0` and `P3` on the positive
horizontal axis. Its limiting horizontal coordinate is strictly
positive. In an ordinary family or the right special family,

\[
P_3=\frac{1-\alpha}{2\alpha}+d_2>0;
\]

in the left special family it is `1/2`. Thus this choice of transverse
axis is nonsingular throughout each stated interior limit.

Write each actual transverse point as `(X_i,Y_i)` and set

\[
\delta=\max_i|Y_i|.
\]

Every actual realization has `delta>0`: otherwise all its vertices
would lie in one spatial plane, contradicting the established K4
nondegeneracy necessity. The common-line limit gives `delta -> 0`.
After passage to a subsequence the stretched points converge to

\[
(P_i,N_i,z_i),\qquad
N_0=N_1=N_3=0,\qquad
\max_{i\in\{2,4,5,6,7\}}|N_i|=1.                 \tag{1}
\]

The transformation dividing the normal coordinate by `delta` and
the physical axial coordinate by `y` has positive determinant.
Therefore every nonzero limiting four-point determinant fixes its
actual sign for all sufficiently late sequence terms. The original
necessary generic topology formula supplies a compatible completion;
pass to a subsequence with one fixed completion. An actual zero
limiting determinant leaves that generic sign unrestricted.

No axial error is divided by `delta`. The stretched coordinates are
bounded, so determinant continuity applies directly. In particular,
the argument assumes no comparison between `delta`, `1/y^2`, a
vanishing edge, or a vanishing deficit.

## 2. Polynomial coordinates for the complete parameter cover

The companion imports the exact family coordinates from
`solver_remaining_c1_flat_limits.py`; the same function is used by
that package's full 29-row metric witness check.

For each ordinary family, let `i in {2,3}`, `j in {6,7}`,
`d_i=r`, and `d_j=1/2-r`, with all other deficits zero. The ordinary
parameter interval is closed: `0<=r<=1/2`.

Apply the following additional affine coordinate transformation to
the stretched points:

\[
(X,N,z)\longmapsto(2X-2z/\alpha,\ N,\ 2z).
\tag{2}
\]

Its determinant is exactly four. It preserves all determinant signs
and every normal coordinate. The transformed horizontal coordinates
are polynomials:

\[
\begin{aligned}
x_0&=0,&x_1&=-1,&x_2&=0,\\
x_3&=-1+2d_2,&x_4&=2(d_2-d_3),\\
x_5&=-1+2\beta(d_2-d_3)+2(1-\beta)(d_7-d_6),\\
x_6&=2(d_7-d_6),&x_7&=2d_7-1.
\end{aligned}
\tag{3}
\]

The axial coordinates become `(0,alpha,1,1,1,beta,0,0)`.
The right special family uses (2) and has horizontal coordinates
`(0,-1,0,-1,0,0,0,-1)`. For the left special family, use
`(X,N,z) -> (2X,N,2z)` instead, also of determinant four; its
horizontal coordinates are `(0,0,0,1,0,1,0,1)`.

Each ordinary interval is split into its open interior and its two
endpoints. Along with the two special families, this gives exactly
`4*3+2=14` cases. Both height parameters remain strictly between
zero and one in every case. No marked symmetry or omitted endpoint
is needed for this finite cover.

## 3. Linear determinant and projection identities

Let `Bijkl` denote an actual four-point determinant of the transformed
configuration. All its coordinates except the five normals in (1)
are fixed by the three scalar parameters. Consequently

\[
B_{ijkl}=\sum_{v\in\{2,4,5,6,7\}}c_{ijkl,v}N_v.
\tag{4}
\]

The companion expands all seventy determinants exactly and verifies
every coefficient in (4).

There is a useful additional family of linear identities. Write
`Aijk` for the signed double area of the projected points `(x_i,z_i)`:

\[
A_{ijk}=(x_j-x_i)(z_k-z_i)-(x_k-x_i)(z_j-z_i).
\]

For distinct `i,j,a,b,c`, direct expansion gives

\[
B_{ijab}A_{ijc}-B_{ijac}A_{ijb}+B_{ijbc}A_{ija}=0.
\tag{5}
\]

This is the projected Grassmann--Pluecker relation; here it is simply
a polynomial identity linear in the normals. The checker verifies
every one of the `28*20=560` indexed relations in all five independent
normal coordinates, for each of the six families. Ordered indices
retain their exact permutation parity.

The ordinary affine five-point determinant cocycles are also imposed.
No metric equation is imposed on the stretched points: an anisotropic
stretch need not preserve the metric.

## 4. Uniform coefficient signs without numerical sampling

Every coefficient used in (4) or (5) is multilinear in
`alpha`, `beta`, and `r`: its degree in each variable is at most one.
The checker first verifies this degree bound and then reconstructs
the polynomial from its exact values at the eight corners

\[
\alpha,\beta\in\{0,1\},\qquad r\in\{0,1/2\}.
\]

The interpolation weights are products of
`alpha,1-alpha`, `beta,1-beta`, and `2r,1-2r`. All are strictly
positive inside the open box. Thus if the corner values have one
weak sign and at least one is nonzero, that sign is strict throughout
the box. If every corner value is zero, the coefficient is identically
zero. The two endpoint strata substitute `r=0` or `r=1/2` first and
use the same argument in the two open height parameters.

If any coefficient in a relation changes sign, the entire relation
is omitted. This only weakens the necessary system. All retained
identities are replaced by the following necessary sign condition:
either every signed term is zero, or there are terms of both signs.
Their positive magnitudes remain free. This relaxation is why the
final uniform problem is Boolean rather than nonlinear real arithmetic.

## 5. Zero-safe Boolean source and contradiction

Each actual determinant and each normal coordinate has two trit bits:
one for positive, one for negative. At most one bit can hold; neither
means zero. An actual nonzero determinant fixes the corresponding
generic sign, while an actual zero does not constrain its completion.

The source retains the full necessary generic topology and linking
formula. It also retains the two strict axial separations: the upper
cap `234` is separated from the other vertices, and the lower cap
`067` is separated from the other vertices. These follow from
`0<alpha,beta<1`; they do not require a cap area to be positive.

The linear identities and affine cocycles give the trit constraints
described above. Finally, one clause asserts that at least one of the
five normal coordinates is nonzero, as required by (1). Every one of
the fourteen resulting CNFs is UNSAT and must pass the independent
RUP checker. Hence no family admits the nontrivial normal stretch
that an actual unbounded sequence would supply.

This contradiction excludes the six flat families as asymptotic
limits of realizations, even though they satisfy all the unstretched
limiting metric and active nonedge equations.

## Reproduction and scope

```sh
python research/type7_completion/solver_remaining_c1_flat_stretch.py /tmp/c1-flat-stretch
python research/type7_completion/solver_cnf_certificates.py /tmp/c1-flat-stretch-rup \
  --checker /tmp/type7-rup-check /tmp/c1-flat-stretch
python research/type7_completion/solver_cnf_certificates.py /tmp/c1-flat-stretch-rup \
  --checker /tmp/type7-rup-check --replay-only
```

The script checks all coordinate transformations, seventy linear
determinants and 560 projection identities per family, and every
retained coefficient sign by exact arithmetic. Its solver answers
are discovery results until the exported formulas independently
replay. No sampled parameter value or solver timeout is used as an
exclusion certificate.

Fresh exact generation took **5.056 seconds**; all fourteen CNFs
passed independent replay in **1.383 seconds** with ten distinct
proof packets. A separate peer generation and replay passed in
6.287 and 1.159 seconds. The formulas have 629 variables and
12,015--12,583 clauses. These are shared-workspace timings.

The result closes ray 1's C1 interior at the research-proof level.
It gives no numerical height threshold and no Lean theorem. Height
endpoints, remaining C0 limits, and the full ray-2 marking still need
separate arguments.
