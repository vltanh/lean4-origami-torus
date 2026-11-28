# Complete exclusion of the upper-b collinear C0 stratum

There is no unbounded embedded ray-1 sequence with an interior C0 limit
such that upper triangle 123 has order b (`d2=0<d1`) and lower triangle
067 is regular. The proof below closes the remaining positive-lower-cap
region `0<u<v<1/2`. The negative orientation and `u>=v` were already
excluded by the [collinear-cap package](exhaustive_c0_collinear.md) and
its [positive extension](exhaustive_c0_collinear_positive.md).

The marked reflection gives the corresponding complete lower-collinear
stratum. In particular both possible annulus nesting orders are covered;
the earlier [section obstruction](remaining_c0_upper_b_sections.md)
provides a separate geometric proof for one of them.

Three exact polynomial identities, together with 23 reusable implications
from the [regular quartic package](solver_remaining_c0_quartic.md), cover
the full necessary actual-sign source. The identities have respectively
2500, 2497, and 2492 terms. Their coefficients are integers, and replay
expands every coordinate monomial. The source cover has one separately
replayable RUP certificate.

## 1. An exact order-b gauge

Write `di=1/2-hi>=0`, `sum di=1/2`. Here

\[
d_2=0<d_1=L,\qquad M=d_6+d_7>0,
\qquad d_6,d_7>0.
\]

The upper cap side lengths are `h1=1/2-L`, `h2=1/2`, and `L`.
Choose a unit transverse direction `e` by `P2=-h1 e`. The collinear
order fixes

\[
P_0=P_1=0,\qquad P_2=-h_1e,\qquad P_3=Le.              \tag{1}
\]

All displayed lengths are positive because `L+M<=1/2` and `M>0`.
The transverse rotation imposing (1) can preserve orientation, so it
does not change any determinant sign.

The replay uses the twelve equations and common raw-bracket scaling
already bound to the complete C0 metric source in the regular quartic
package. In its homogeneous coordinates put `S=sum di`, and substitute

\[
P_2=(-(S-d_1),0),\qquad P_3=(d_1,0),\qquad d_2=0.       \tag{2}
\]

At the normalized geometry `S=1/2`, this is exactly (1). In particular
the first three upper-cap equations vanish identically after substitution.
The other cap, core, and middle equations retain their original sources.
No denominator is introduced and no equation is removed by a numerical
rank decision.

## 2. The quadratic factors remain nonnegative and are often strict

All factors in the stored identities are the same as in the regular
quartic proof: products of nonnegative deficits, squared norms, optional
squared norms of sums, and the four expressions

\[
\begin{gathered}
D^2-|P_6-P_3|^2,\qquad h_3^2-|P_4-P_3|^2,\\
h_4^2-|P_5-P_4|^2,\qquad h_5^2-|P_6-P_5|^2,
\qquad D=d_0+L+M.
\end{gathered}                                           \tag{3}
\]

Their weak nonnegativity was proved on closed cap faces in that package.
For the present strict order b, all four factors in (3) are actually
positive even though the upper cap is collinear.

First prove `|P6-P3|<D`. If `d0>0`, the triangle inequality gives
`|P6-P3|<=M+L<D`. If `d0=0`, the exact core relation

\[
d_0=h_1h_7+P_2\cdot P_7
\]

forces `P7` to be a positive multiple of `e`. Regularity of the lower
cap then makes `P6` nonparallel to `e`. Since `P3=Le` and `L>0`,
the triangle inequality is strict: `|P6-P3|<M+L=D`.

Thus `T=(D,P6-P3)` is future timelike for the bilinear form
`<(a,x),(b,y)>=ab-x dot y`. With the usual C0 vectors

\[
\begin{gathered}
Q_4=P_4-2uP_3-(1-2u)P_6,\quad
Q_5=P_5-2vP_3-(1-2v)P_6,\\
r=|Q_4|=d_4+d_5+2uD>0,\quad
s=|Q_5|=d_3+d_4+(1-2v)D>0,
\end{gathered}
\]

the vectors `(r,Q4)` and `(s,-Q5)` are nonzero future null vectors.
The exact decompositions from the regular quartic proof make the
remaining three expressions in (3) strictly positive, since
`1-2u`, `2v`, and `v-u` are positive.

The six cap-side norms used by the verifier are also positive:
`|P2|,|P3|,|P3-P2|,|P6|,|P7|,|P7-P6|`. Products of `d6,d7`
are strictly positive. Every bracket containing the whole lower cap
067 is nonzero because its fourth vertex has positive limiting
height. The weak-turn extension additionally supplies the strict
actual brackets `[1267]<0` and `[2367]>0`.

## 3. Three identities with separately justified strict residuals

Use the homogeneous positive height variables

\[
a=2u,\qquad b=2(v-u),\qquad c=1-2v.
\]

Each certificate has exactly the form of the regular quartic identities:

\[
\sum_k w_k E_k A_{i_kj_k}m_k(a,b,c)
 +\sum_l v_l\,s_l\overline B_l\,G_l\,t_l=0.             \tag{4}
\]

Here `Ek` is a source metric equation, `Aij` a planar cross product,
`wk` an integer of either sign, `vl` a positive integer, `Gl` one
of the nonnegative quadratic factors, and `tl` one of `a,b,c`.
The raw determinants have the common positive scaling checked by the
original source verifier. Every term has degree four in coordinates
and deficits and degree two in the height variables.

After the exact gauge substitution (2), full polynomial expansion proves
(4). On a geometry satisfying the certificate's required weak actual
signs, its first sum vanishes and every term of its second sum is
nonnegative. The following terms are separately strict:

| Identity | Strict factor combination, apart from its positive integer coefficient |
|---|---|
| 1 | `[0467] * (h5²-|P6-P5|²) * a` |
| 2 | `[0167] * d6*d7 * a`; also `[0567] * d7² * a` |
| 3 | `[2367] * |P6|² * b` |

All bracket signs in this table are positive in the chosen lower-cap
orientation. Section 2 proves the required strictness; none is inferred
from a free generic completion of an actual zero determinant. Therefore
each complete required sign set is impossible.

The largest integer coefficient has 648 bits. Replay uses exact integer
arithmetic throughout; floating-point discovery is not part of acceptance.

## 4. Complete actual-sign coverage

The source is the existing
`ActualModel('1_between_2_3', +1, height_relations)`. It retains the
full generic topology and linking formula, the two strict height cuts,
all actual positive/negative trits, affine cocycles, weak
Grassmann--Pluecker relations, the positive interpolation placing
vertex 1 between vertices 2 and 3, the regular lower-cap rank clauses,
and all 49 checked C0 height relations.

Its additional proved necessities are

\[
[2367]>0,\quad[1267]<0,\quad[0237]\ge0,
\qquad[2345]\le0,\quad[4567]\le0.
\]

For each old or new identity, add the disjunction saying that at least
one of its required weak actual signs fails. For a required
`sign * B >= 0`, this means the actual trit of the opposite strict
sign. A zero actual bracket never counts as a failure.

The earlier quartic package provides 23 direct or reflected identities
having a strict residual from the regular lower cap alone. Its full
polynomial replay is invoked before these implications are used. The
three new identities supply the remaining implications. The resulting
source is UNSAT; the independently checked RUP proof certifies that
no actual-sign or generic-completion branch has been omitted.

This proves the entire remaining `0<u<v<1/2` positive-lower-cap
upper-b stratum. Combining the already completed orientation and
height-order cases proves the theorem stated at the beginning.

## Reproduction and scope

```sh
python research/type7_completion/remaining_c0_upper_b_quartic.py /tmp/c0-upper-b-quartic
python research/type7_completion/solver_cnf_certificates.py /tmp/c0-upper-b-quartic-rup \
  --checker /tmp/type7-rup-check /tmp/c0-upper-b-quartic
```

The JSON beside the verifier contains all three complete integer
identities. Replay verifies their complete coordinate expansions,
all strict witnesses, the inherited polynomial identities and source
bindings, and generates the final source-cover CNF. That CNF requires
independent RUP acceptance.

The coincident upper order `d1=d2=0`, the other strict order
`d1=0<d2`, and degenerate height boundaries remain separate. No full
ray-1, Type 7, or Lean theorem is claimed here.
