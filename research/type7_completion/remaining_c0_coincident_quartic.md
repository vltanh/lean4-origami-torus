# Complete exclusion of the coincident-cap interior C0 stratum

There is no embedded ray-1 sequence with an interior C0 limit in which
`d1=d2=0` and the lower triangle 067 is regular. This proves the whole
upper-coincident stratum, including arbitrary relative rates at which
the finite upper cap and its diagonal collapse. The checked marked
reflection gives the corresponding lower-coincident stratum.

The negative lower-cap orientation was excluded by the
[negative-coincidence proof](exhaustive_c0_negative_coincidence.md).
The [positive extension](exhaustive_c0_collinear_positive.md) excludes
the positive orientation when `u>=v`. This note closes its remaining
region `0<u<v<1/2`.

Five exact integer polynomial identities, together with zero
implications from the fourteen [regular quartic
identities](solver_remaining_c0_quartic.md), force

\[
\boxed{C_{56}=0,\quad C_{57}\ge0,\quad[1567]\le0,
       \quad C_{27}<0.}                              \tag{1}
\]

These actual signs place `P5` on a short segment, contradicting its
exact metric radius. No common-axis hypothesis on `P4,P5,P6` is used.

## 1. The exact collapsed-cap source

Let `S=sum di=1/2` at normalized geometry. Because `d1=d2=0`, an
orientation-preserving transverse rotation gives

\[
P_0=P_1=P_3=0,\qquad P_2=(-S,0),\qquad
M=d_6+d_7=|P_6|>0,\qquad d_6,d_7>0.
\tag{2}
\]

The verifier substitutes (2) and `d1=d2=0` into all twelve source
equations and all seventy raw determinant polynomials from the regular
quartic package. Their bindings to the original C0 auxiliary equations,
including the product-scale syzygies, are replayed first. The three
upper-cap equations vanish identically after substitution.

The five stored identities have 1440, 1440, 1442, 1446, and 1442 terms.
Their maximum coefficient size is 284 bits. Replay expands every
coordinate monomial with integer arithmetic. No numerical rank or
projected polynomial quotient is used to accept an identity.

## 2. Nonnegative factors and zero implications

Each identity has the form

\[
\sum_k w_k E_k A_{i_kj_k}m_k(a,b,c)
+\sum_l v_l\,s_l\overline B_l G_l t_l=0,
\qquad a=2u,\ b=2(v-u),\ c=1-2v>0.                 \tag{3}
\]

Here the first sum consists of source metric equations multiplied by
planar cross products and height monomials. The coefficients `wk` are
arbitrary integers. In the second sum, every `vl` is a positive integer,
`sl` is a required bracket sign, `tl` is one of the positive heights,
and `Gl` is a nonnegative quadratic factor.

The factors are products of nonnegative deficits, squared norms,
squared norms of sums, and the four weak Lorentz norms from the regular
quartic proof. Their nonnegativity remains valid on the closed cap
faces: `T=(D,P6-P3)`, with `D=d0+M`, is future causal; the null vectors
`(r,Q4)` and `(s,-Q5)` have positive radii. The same decompositions
give nonnegative Lorentz norms for the three middle edges. In the
middle complement calculation the required inequality is weak, so
`d0=0` and a null `T` are allowed. No strict Lorentz norm is assumed.

The following factors are separately strictly positive on (2):

* products `d_i d_j` with `i,j` in `{6,7}`;
* the squared norms of `P2`, `P3-P2`, `P6`, `P7`, and `P7-P6`.

Suppose all the required weak actual signs `sl Bl>=0` hold. The first
sum in (3) vanishes and all terms of the second sum are nonnegative.
Every term therefore vanishes. Whenever `Gl>0`, that term implies
the actual equality `Bl=0`, even if `Bl` has no separately known
strict sign.

This is stronger than using an identity only when one residual is
already known to be strictly positive. It is also zero-safe. The
actual-trit clause encoding each zero implication is

\[
\bigvee_l (s_l B_l<0)\quad\lor\quad\neg(s_j B_j>0).
\tag{4}
\]

Under the required weak sign of `Bj`, its last disjunct means precisely
`Bj=0`. A zero bracket never counts as an opposite sign, and its free
generic completion is not constrained by asserting the zero.

For each of the fourteen inherited identities, use every strictly
positive factor supplied by the regular lower cap. Apply the same
procedure after the checked marked reflection, using the regular cap
in the transformed upper position. Both transformed heights stay in
`0<u'<v'<1/2`, so all height factors remain positive. The exact
reflection and weight-index checks are replayed by the companion.

These inherited identities supply 1570 zero implications. The five
new collapsed-cap identities supply another 159. Neither collection
requires a strict upper-cap angle, a nonzero diagonal 13, or a positive
lower bound for `d0`.

## 3. The complete actual-sign consequence

Start with `ActualModel('1_equals_3', +1, height_relations)`. It retains
the full necessary topology and linking formula, both strict height
cuts, actual trits, weak Grassmann--Pluecker rules, affine cocycles,
the exact coincidence of vertices 1 and 3, regular-lower-cap rank
clauses, and all 49 checked height relations.

Add the already proved necessities

\[
[2367]>0,\quad[1267]<0,\quad[0237]\ge0,
\qquad[2345]\le0,\quad[4567]\le0.
\]

Then add all 1729 implications (4). The conjunction of this source
with the negation of (1) is UNSAT. A single independently replayable
CNF/RUP certificate proves the whole conjunction, including the
strict assertion `C27<0`: its negation retains both zero and positive
possibilities. Thus (1) follows without selecting a generic sign for
any actual zero determinant.

## 4. The segment contradicts the radius

Since `C56=0` and `P6` has length `M>0`, write `P5=t P6`. Because
`C67>0`, the second conclusion of (1) gives `t>=0`. The exact
determinant identity is

\[
2[1567]=C_{57}-C_{56}-(1-2v)C_{67}
       =(t-(1-2v))C_{67}.
\]

Its nonpositive sign gives `t<=1-2v`. Hence

\[
|P_5-(1-2v)P_6|\le(1-2v)M.                          \tag{5}
\]

The core stress relation on (2) is

\[
d_0=\tfrac12 h_7+P_2\cdot P_7,
\qquad |P_2|=\tfrac12,\quad |P_7|=h_7>0.
\]

The strict sign `C27<0` makes these two vectors nonparallel, so strict
Cauchy--Schwarz gives `d0>0`. On the other hand the exact C0 radius is

\[
\begin{aligned}
Q_5&=P_5-(1-2v)P_6,\\
|Q_5|&=d_3+d_4+(1-2v)(d_0+M)>(1-2v)M,
\end{aligned}
\]

contradicting (5). This excludes the remaining positive-orientation,
`v>u` coincidence case. Together with the two previous cases stated
at the beginning, it closes the entire interior upper-coincident
stratum and its marked reflection.

## Reproduction and remaining scope

```sh
python research/type7_completion/remaining_c0_coincident_quartic.py /tmp/c0-coincident-quartic
python research/type7_completion/solver_cnf_certificates.py /tmp/c0-coincident-quartic-rup \
  --checker /tmp/type7-rup-check /tmp/c0-coincident-quartic
```

The JSON beside the verifier stores all five complete integer identities.
The producer expands those five and the fourteen inherited identities,
checks the reflection and segment formulas, constructs every zero
implication, and exports the single conjunction CNF. Independent RUP
acceptance is required before using its conclusion.

The other strict upper line order `d1=0<d2`, and the corresponding
lower order, remain separate. Degenerate height boundaries and a
complete ray-1, Type 7, or Lean theorem are not claimed here.
