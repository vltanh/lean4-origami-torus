# One spatial unknown for every original K4 branch

This reformulates **all 268 original branches of each remaining marking**.
It does not subdivide them and does not exclude any of them. The source
is the complete common sign cover used by `solver_remaining_axis.py`.
The branch indices and K4 patterns are unchanged.

The generated necessary system has fourteen intrinsic coordinates and
one spatial unknown. With variable `t=1/y²`, it has sixteen real variables.
The seed satisfies a quadratic equation with positive leading coefficient.
Every remaining metric equation and every actual coordinate-minor sign
test is affine in that seed, with coefficients represented by a shared
arithmetic DAG. This avoids expanding large multivariate polynomials.

The chart works at each fixed `y>=32` or throughout `0<t<=1/Y²`, `Y>=32`.
It retains all actual-zero boundaries. In particular it does not replace
finite-height constraints by their `t=0` limits.

## 1. A propagation star for each entire branch

Choose one vertex from each opposite pair `04,15,26,37` as an anchor
tetrahedron `A=(a0,a1,a2,a3)`. Its four partners are the leaves
`B=(b0,b1,b2,b3)`. All anchor edges, leaf edges, and anchor-to-leaf edges
other than `ai bi` belong to the Type 7 graph.

The sixteen four-cliques are noncoplanar. However, the three additional
four-sets needed to propagate directly from `b0` to the other leaves are
not cliques. They cannot be assumed nonzero just because a generic
completion has a sign for them.

For each original branch, `star_plan` chooses an anchor and a seed for
which those three four-sets occur in that branch's already-proved
**strict** set. All 268 branches admit such a star. There are seven ordered
anchor/seed choices, using only three unordered anchor sets. This is a
different coordinate choice on each original branch, not an additional
partition of its domain.

The output records the three strictness premises, the ordered anchor,
the original K4 pattern and the original branch index. The common cover
and its existing strictness and RUP verification remain required inputs.

## 2. The single missing-distance parameter

Let `Dij` denote squared spatial distances divided by `y²`. On every
graph edge they equal

\[
D_{ij}=t(x_j-x_i+m_{ij}+n_{ij}/2)^2+(v_j-v_i+n_{ij})^2.
\]

Define the anchor Gram matrix

\[
G_{ij}=\frac{D_{a_0a_i}+D_{a_0a_j}-D_{a_ia_j}}2,
\qquad i,j=1,2,3,
\]

and let `g=det G>0`, `H=adj G`. Positive definiteness is imposed by
Sylvester's three strict principal-minor conditions.

The seed is `z=D(a0,b0)`. In inner-product coordinates the seed leaf is

\[
U(z)=u+\frac z2\mathbf1,
\qquad u_i=\frac{D_{a_0a_i}-D_{a_ib_0}}2.
\]

Its four anchor distances hold precisely when

\[
F(z):=U(z)^THU(z)-gz=Az^2+Bz+C=0,
\]

where

\[
A=\tfrac14\mathbf1^TH\mathbf1>0,\quad
B=\mathbf1^THu-g,\quad C=u^THu.
\]

For another leaf `bk`, let `dk=D(a0,bk)`, and let `ak` be its
inner-product vector with its missing distance `D(ak,bk)` temporarily
set to zero. Thus its true vector is `ak-zk ek/2`.

Set

\[
R_k=(HU(z))_k,\qquad
N_k=2U(z)^THa_k-g\bigl(z+d_k-D_{b_0b_k}\bigr).
\]

The prescribed seed-to-leaf edge gives exactly

\[
z_k=N_k/R_k,\qquad
U_k=V_k/R_k,\qquad V_k=R_ka_k-\tfrac12N_ke_k.
\]

Here `Rk=g lambda_k(b0)`. The selected strict replacement four-set
therefore proves `Rk!=0` on the entire original branch. Its sign is
not guessed or fixed from a generic completion.

The three leaf norm equations and three remaining leaf-to-leaf edge
equations are

\[
V_k^THV_k-gd_kR_k^2=0,
\]

\[
2V_k^THV_l-g(d_k+d_l-D_{b_kb_l})R_kR_l=0.
\]

Together with `F=0`, these retain all 24 original edge lengths. All
missing distances remain positive and obey the original finite list
of necessary lattice-translate contraction inequalities. For example
`Nk/Rk<=L` is encoded as `Nk Rk-L Rk²<=0`, with no assumption about
the sign of `Rk`.

## 3. The branch selects one quadratic root

The seed's barycentric coordinate opposite `a0` is

\[
\lambda_0(b_0)=1-\mathbf1^THU(z)/g.
\]

Consequently

\[
F'(z)=2Az+B=-g\lambda_0(b_0).
\]

Both ordered brackets `[a0,a1,a2,a3]` and `[b0,a1,a2,a3]` are strict
K4 brackets. Their ratio has sign `lambda0(b0)`. Thus the branch itself
fixes the derivative sign and hence one of the two quadratic roots.
In particular its discriminant is strictly positive. The generator
records both ordered cliques and adds the corresponding redundant
strict derivative inequality.

## 4. Positive quadratic reduction

Arithmetic in `R[z]/(Az²+Bz+C)` is represented as

\[
\frac{p+qz}{A^e},\qquad e\ge0.
\]

The product rule follows from the exact identity

\[
A(p+qz)(r+sz)
=[Apr-Cqs]+[A(ps+qr)-Bqs]z+qsF(z).
\]

Every denominator suppressed from a sign or zero test is a power of
the strictly positive `A`. Addition aligns those powers; multiplication
uses the displayed identity. The six remaining metric equations become
affine equations in `z`. No division by an unknown coefficient of a
residual equation occurs.

The arithmetic DAG collects equal terms and exact rational coefficients,
including opposite terms. It distributes only rational scaling over sums;
it does not expand products of nonconstant sums. Thus the quotient relation
itself reduces to literal zero. Only nodes reachable from the emitted
constraints and minor definitions are written to the query.

## 5. Every actual minor and circuit is retained

Store each inner-product point homogeneously as `(Ni,di)`, with
`di=1` for anchors and the seed, and `di=Rk` for another leaf.
For a support `S` and coordinate axes of size `|S|-1`, take the
homogeneous determinant with its usual parity correction, then multiply
by `product(di : i in S)`. This equals the actual affine minor times

\[
\prod_{i\in S}d_i^2>0.
\]

Quadratic reduction then multiplies it only by a positive power of `A`.
Its sign and its exact zero set are unchanged. This covers all 84
one-dimensional, 168 two-dimensional and 70 three-dimensional minors.

The ordered anchor can have either orientation in the original
`[0123]>0` normalization. Reflecting the third inner-product coordinate
by its known ordered-anchor sign makes the coordinate map orientation
preserving. Lower-dimensional minors are computed in the resulting
coordinates, rather than assigned an incorrect common reflection sign.

The unchanged `solver_remaining_chambers.generate_query` supplies the
original strict K4 tests, the exact weak-sign decision diagram and every
remaining actual circuit test. Weak minors still allow both generic
continuations at zero. The metric rewrite introduces no new sign-model
filter or geometric subclass.

## Reproduction and scope

```
python research/type7_completion/branch_gram_verify.py \
  /tmp/type7-536-ray1/axis_chambers.json

python research/type7_completion/branch_gram_chart.py \
  /tmp/type7-536-ray1/axis_chambers.json /tmp/type7-gram-canonical-live \
  --mark 1 --y 32 --all-heights --branch 0
```

Omit `--branch` to emit all 268 unchanged branch IDs for that marking.
Repeat with `--mark 2` for the other 268.

The independent replay checks the universal adjugate, propagation,
quadratic-reduction and seed-side identities. It also checks all 268
strict-star and root-sign selections and compares the formulas directly
with exact rational spatial coordinates: 42 fixtures, 13,524 minor
identities (including 56 zero full minors), and 168 missing distances.
The verifier also checks that local canonicalization cancels the defining
seed quadratic in the quotient algebra.

For original ray 1 branch 0, the current emitted formulations have the
following sizes. Degree bounds assign degree one to each free variable
and propagate through the DAG without relying on polynomial cancellation.

| Height mode | Real unknowns | Emitted arithmetic nodes | Query bytes | Metric coefficient degree bound | Minor coefficient degree bound |
| --- | ---: | ---: | ---: | ---: | ---: |
| Fixed `y=32` | 15 | 12,585 | 731,697 | 24 | 66 |
| Whole tail `0<t<=1/1024` | 16 | 12,623 | 731,033 | 36 | 99 |

The seed coefficients `(A,B,C)` have degree bounds `(4,6,8)` at fixed
height and `(6,9,12)` over the whole tail. The reduced variable count
therefore comes with substantially higher polynomial degrees. The DAG
keeps these expressions factored; it does not establish that solving
them is faster. A bounded nonlinear solver pilot on the equivalent
unsimplified 16-variable whole-tail branch 0 returned `unknown` at
15 seconds.

These are formulation and verification measurements, not evidence of
infeasibility. The output manifest deliberately records no excluded
branches. A mathematical contradiction or independently verifiable
nonlinear certificate is still needed to close any original branch.

`branch_metric_root.py` supplies a further exact projection: the two
strict K4 brackets select the seed root, and a zero-safe polynomial
sign formula removes `z` from every comparison. That retains all the
original Boolean circuit conditions with fourteen intrinsic variables
at fixed height, or fifteen over the whole height tail. It does not
provide an infeasibility certificate either.
