# Excluding one collinear C1 endpoint cap

For ray 1 and `0<alpha,beta<1`, suppose exactly one endpoint triangle
234 or 067 is collinear. Such a limit is impossible, including the
coincident pair 2=4 or 0=6. The proof combines three new CNFs with
the five implications in [the collinear package](solver_remaining_c1_collinear.md)
and two checked marked symmetries. All eight CNFs require independent
RUP replay. Two collinear caps are treated separately by the
[flat-family classification and normal stretch](solver_remaining_c1_flat_stretch.md).

## 1. A nonvanishing pair in the projected plane

First suppose the upper cap 234 is collinear and the lower cap 067 is
noncollinear. Write `E=P2-P3`. The ray-1 deficit budget and lower-cap
regularity imply `h2>0`, hence `E!=0`. In the C1 height chart,

\[
2[0236]=-\operatorname{cross}(E,P_6),\quad
2[0237]=-\operatorname{cross}(E,P_7),\quad
2[2367]=-\operatorname{cross}(E,P_7-P_6).
\]

No pair of these three brackets can vanish simultaneously. Indeed the
last cross product is the difference of the first two, and

\[
\operatorname{cross}(E,P_6)P_7-
\operatorname{cross}(E,P_7)P_6+
\operatorname{cross}(P_6,P_7)E=0.
\]

Two zero factors would therefore imply `E=0`, since the lower cap has
nonzero area. The companion checks all four determinant identities
symbolically. Each necessary CNF clause permits either sign of either
nonzero bracket; it excludes only simultaneous zeros. It imposes no
strict sign on an otherwise vanishing actual bracket.

## 2. Two exact height identities

The same C1 chart gives

\[
[1237]+[0123]-(1-\alpha)[0237]=0,
\tag{H1}
\]

\[
\alpha[1467]-(1-\alpha)[0167]
-\alpha[0147]+\alpha[0146]=0.
\tag{H2}
\]

These identities use only `P0=P1=0` and the prescribed C1 heights;
they hold before either cap is assumed collinear. The companion
checks them by exact determinant expansion. Since `0<alpha<1`, every
displayed coefficient magnitude is positive. Each relation therefore
implies that its signed terms either are all zero or include both
signs. The actual-trit clauses encode this necessary condition with
no restriction on any generic completion of a zero bracket.

## 3. The negative lower-cap orientation

Use the actual-bracket/generic-completion source from the previous
package, change the five ordered lower-cap units to `[067j]<0`, and
add the three nonvanishing-pair clauses and (H1)–(H2). The resulting
formulas are independently checked UNSAT in all three cases:

| Upper order | Deficits |
|---|---|
| 4 strictly between 2 and 3 | `delta2=0`, `delta3>0` |
| 2 strictly between 3 and 4 | `delta3=0`, `delta2>0` |
| 2 equals 4, with 3 distinct | `delta2=delta3=0` |

There is no strict-anchor assumption in these three formulas. In
particular they retain actual `[0123]=0`.

The source retains the strict axial cuts, all affine cocycles, the
positive interpolation relation of the collinear point, and the weak
Grassmann–Pluecker relations. Actual zeros still leave generic signs
unrestricted. These are geometric exclusions of the specified
negative-cap formulas, not merely filters of sampled generic models.

## 4. Checked marked reflection

The reflection `p(i)=6-i (mod 8)` preserves the marked torus after
intrinsic inversion and its exact integer vertex gauge. The companion
checks that gauge for both markings and all 24 edges. Its cyclic
weights and C1 height parameters transform as

\[
h'_i=h_{5-i},\qquad (\alpha',\beta')=(\beta,\alpha).
\]

It preserves the two cap vertex sets, swaps the two strict upper
orders, preserves coincidence 2=4, and sends

\[
\delta'_1=\delta_4,\quad\delta'_4=\delta_1,\quad
\delta'_2=\delta_3,\quad\delta'_3=\delta_2.
\]

The new spatial axis is the old edge 65, whose limiting axial length
is `beta/2>0`. Reanchoring at this edge is valid for the fixed interior
limit. Its change of transverse coordinates is a common linear
isometry plus a height-dependent translation; on each cap all heights
are equal, so cap regularity, coincidence, and the strict line order
are preserved. The orientation signs used in the next section are
checked explicitly:

\[
[0'1'2'3']=[6543]=[3456],\qquad
[0'6'7'j']=[607p(j)]=-[067p(j)].
\tag{R}
\]

These equalities refer to relabeled raw brackets under an
orientation-preserving spatial isometry. Dividing by a common positive
normalization factor preserves their signs.

The original uniform choice `alpha>=1/4` is unnecessary after this
reanchoring. A fixed positive `beta` gives a bounded chart, and every
circle identity and turning argument used here requires only
`0<alpha',beta'<1`. Every division is by a strictly positive fixed
interior parameter.

## 5. The positive lower-cap orientation

For all three upper orders the preceding package's two-sign CNFs give
actual

\[
[0127]\le0,\qquad[4567]\le0.
\]

Split on the actual value of `[3456]`.

If `[3456]<=0`, all four weak orientation hypotheses of the
[turning argument](solver_remaining_c1_turning.md) hold. Its upper
angle is now `A=0`; the lower cap remains regular, so
`R=delta2+delta7>0` and `L=delta3+delta6>0`. The proof's strict gap
and final contradiction remain valid, as detailed in the preceding
collinear note. This branch includes `[3456]=0`, and also includes
coincident vertices 2=4.

If `[3456]>0`, apply the checked reflection. By (R), the new actual
anchor is strictly positive, so the orientation-preserving reanchoring
already has the required normalization. Every new ordered lower-cap
bracket is strictly negative, because the original lower cap is
regular and positively oriented. The upper cap is still collinear in
one of the three listed orders. Section 3 excludes the reflected
configuration. This use of a strict actual bracket is essential: a
positive generic completion of an actual zero would not justify the
same orientation argument.

Thus every upper-collinear/lower-regular C1 limit is excluded for
ray 1, including zero anchors and coincident upper vertices.

## 6. Swapping the endpoint caps

The checked rotation `p(i)=i+4 (mod 8)` exchanges the two cap vertex
sets. Its C1 parameters and weights are

\[
(\alpha',\beta')=(1-\beta,1-\alpha),\qquad h'_i=h_{i+4}.
\]

The new axis is old edge 45, with strictly positive limiting length
`(1-beta)/2`; its spatial axial direction is reversed. The companion
checks the full marked gauge, transformed intrinsic levels, transformed
spatial levels, and all local horizontal displacements. Cap
noncollinearity, collinearity, and coincidence are again preserved.
Thus a collinear lower cap and a noncollinear upper cap reduce to the
case already excluded.

## Reproduction and remaining cases

```sh
python research/type7_completion/solver_remaining_c1_collinear_rank.py /tmp/c1-collinear-rank
python research/type7_completion/solver_cnf_certificates.py /tmp/c1-collinear-rank-rup \
  --checker /tmp/type7-rup-check /tmp/c1-collinear-rank
python research/type7_completion/solver_cnf_certificates.py /tmp/c1-collinear-rank-rup \
  --checker /tmp/type7-rup-check --replay-only
```

The companion to the preceding package must also be generated and its
five CNFs replayed. This yields an asymptotic ray-1 research exclusion
for every interior C1 limit with exactly one collinear endpoint cap.
It supplies no finite height threshold and does not replace a Lean
proof. The separate [normal-stretch proof](solver_remaining_c1_flat_stretch.md)
now excludes the limits with both endpoint caps collinear as well.
