# A nested-section reduction for regular C0

Consider an unbounded embedded sequence of either remaining marking,
with a C0 limit having regular endpoint caps 123 and 067 and
`0<u,v<1/2`. Let `B` be the annulus with faces
`013,023,027,127,167,016`; let `A` be the complementary annulus containing
vertices 4 and 5.

The following are necessary conditions on such a sequence:

1. If `0<v<u<1/2` and `A` is the inner annulus, its finite generic
   completion has both `chi3467<0` and `chi2356<0`.
2. If `u=v`, then `A` cannot be the inner annulus.

These conclusions apply to ray 2 without a ray-1 deficit budget.
For the strict height order, they remove 296 of the 363 regular generic
completions compatible with the intermediate height cut. The remaining
67 consist of 43 completions with `B` inner and 24 with `A` inner and
both indicated signs negative. This is a reduction of regular C0, not
an exclusion of the entire component. The region `u<v`, height boundary,
and collinear caps are not covered by the strict-order conclusion.

The [companion](remaining_c0_nested_quadrilaterals.py) checks the metric
source, section formulas, finite turn identities, marked reflection,
and six Boolean obligations. Independent RUP replay of those obligations
is required. The geometric argument below is also required: a weak
limiting sign assignment alone does not supply finite nesting.

## 1. Closed metric input for both markings

Use the bounded-axis coordinates

\[
P_0=P_1=0,\qquad
z=(0,\tfrac12,\tfrac12,\tfrac12,u,v,0,0).
\]

Write `hi=-X(i,i+1)`, `di=1/2-hi`, and put

\[
\begin{gathered}
L=1-h_1-h_2=|P_3|,\quad M=1-h_6-h_7=|P_6|,\\
D=h_3+h_4+h_5-1,\quad \ell_u=1-2u,\quad\ell_v=1-2v,\\
Q_4=P_4-2uP_3-\ell_uP_6,\quad
Q_5=P_5-2vP_3-\ell_vP_6,\\
r=h_3-\ell_uD,\quad s=h_5-2vD,\quad F=P_7-P_6.
\end{gathered}
\]

The closed nearest bounds give `0<=hi<=1/2` and
`hi+h(i+1)>=1/2`. The regular caps have perimeter one; in particular
`0<h1,h2,h6,h7<1/2`, and `L,M>0`. Normalize the upper cap positively.
The regular-cap source excludes a negative lower cap, so

\[
\operatorname{cross}(P_2,P_3)>0,
\qquad \operatorname{cross}(P_6,P_7)>0.                 \tag{1}
\]

The necessary local metric identities include

\[
\begin{aligned}
|Q_4|^2&=r^2,& |Q_5|^2&=s^2,& Q_4\cdot Q_5&=-rs+d_4,\\
|F|^2&=h_6^2,&
F\cdot(vQ_4-uQ_5)&=h_6(vr+us)-u(h_6-d_5).
\end{aligned}                                                   \tag{2}
\]

The checker binds twelve polynomial row combinations to the full
29-row metric/product-scale system, including its five syzygies. It
also reconstructs both marked cocycles. No product scale is set to
zero and no height or deficit is cancelled from the source equations.
In particular, ray 2 has

\[
\sum_i h_i=\tfrac52,\qquad D=d_0+L+M-1;
\]

the ray-1 identity `D=d0+L+M` is not used here.

## 2. Finite nesting and source signs

Take arbitrarily small embedding-preserving generic perturbations of
the original sequence, preserving every normalized coordinate, metric
residual, and auxiliary limit at its required scale. Reanchor 01 and
flatten the lower cap plane by a height shear tending to zero, leaving
transverse coordinates unchanged. Its regular limiting projected
triangle makes this flattening legitimate. All other vertices remain
strictly above it.

Near that cap, the two annulus sections are disjoint simple curves
surrounding an interior point of the cap. They are nested. The upper
and lower neighbors of 4 and 5 are contiguous in their links in either
height order; the checker verifies both links against the original
faces. Their section cycles cannot split or join, so the nesting order
persists throughout the open interval between the caps. Take a
subsequence with fixed generic signs and nesting order.

Let `chi` denote these **finite generic** signs. The source gives

\[
\chi_{3456}<0,
\qquad \chi_{0156}>0\Longrightarrow\chi_{0157}<0.       \tag{3}
\]

Near vertex 0, the `A` corner is `(z/z5)P5`, with adjacent directions
`P6,P7`. The origin, a vertex of `B`, lies inside that corner precisely
when `-P5` lies in their positive cone. Since
`[015j]=z1 cross(P5,Pj)`, equations (1) and (3) imply

\[
\chi_{0156}>0\Longleftrightarrow B\text{ is inner},
\qquad
\chi_{0156}<0\Longleftrightarrow A\text{ is inner}.     \tag{4}
\]

For example, a negative `chi0156` puts the origin outside `A`, forcing
`A` to be inner because the interiors overlap near the lower cap.
The equivalence uses finite signs; the corresponding limiting
determinants may vanish.

Now assume `v<u`. A finite horizontal plane separates
`{1,2,3,4}` from `{0,5,6,7}`. Its five-point circuit clauses, together
with the regular-cap topology/linking source, imply

\[
\chi_{2345}<0,\qquad\chi_{4567}<0.                    \tag{5}
\]

The companion exports the violation of this conjunction as one UNSAT
CNF. This implication does not use the ray-1 metric turning lemma.

## 3. The lower critical quadrilateral

Set `a=v/u`, `q=1-a`, so `0<a,q<1`. At height `v`, the section of `A`
has cyclic vertices

\[
\left(P_5,\ C,\ D_6,\ D_7\right)
=\left(P_5,\ 2vP_3+\ell_vP_6,
       aP_4+qP_6,\ aP_4+qP_7\right).                  \tag{6}
\]

Its consecutive faces are `356,346,467,457`. The four edge vectors are

\[
-Q_5,\quad aQ_4,\quad qF,\quad -(Y+qF),
\qquad Y=aQ_4-Q_5.                                   \tag{7}
\]

The effective scalar parameters

\[
\rho=s=a(1-h_4-r)+qh_5,\quad
\sigma=1-s-ar=q(1-h_5)+ah_4,\quad
\tau=\sigma-qh_6=q(1-h_5-h_6)+ah_4
\]

satisfy, by (2),

\[
|Y|^2=\sigma^2-2qd_5,\quad
Y\cdot F+h_6\sigma=d_5,\quad
|Y+qF|^2=\tau^2,\quad
s+ar+qh_6+\tau=1.                                    \tag{8}
\]

All four side lengths in (7) are positive. Indeed `h3,h5>0` follow
from their nearest bounds with regular edges `h2,h6<1/2`, and

\[
r=2uh_3+\ell_u(1-h_4-h_5)\in(0,\tfrac12],\qquad
s=\ell_vh_5+2v(1-h_3-h_4)>0.
\]

Also `tau>0` because `h5<=1/2`, `h6<1/2`, and `q>0`.
Thus (6) has perimeter one, including all allowed zero individual
weights and all equalities in the nearest bounds.

The diagonal `Y` is nonzero. The checked zero-norm identity from the
[C1 section proof](remaining_c1_sections.md#3-nesting-and-the-inner-critical-quadrilateral),
with `(h0,h1,a)=(h5,h4,a)`, gives

\[
|Y|^2-(\tfrac12-d_5-d_4)^2
=[ad_5+qd_4](1-2d_5-2d_4)+[ad_5-qd_4]^2\ge0.
\]

If `Y=0`, equality forces `d5=q/2`, `d4=a/2`, `sigma=q`.
The dot equation in (8) would then force `h6=1/2`, a contradiction.

The same checked angle identity supplies a strict distinguished corner
at `P5`. If `phi,psi` are its two triangle angles divided by `Y`, then

\[
\cos\phi+\cos\psi=\frac{N}{2s\tau|Y|},
\]

where

\[
\begin{split}
N={}&2h_5q(\tfrac12-h_6)\bigl(q+2a(\tfrac12-r)\bigr)\\
   &+2h_4a(\tfrac12-r)\bigl(a+2q(\tfrac12-h_6)\bigr)\\
   &+2(h_5+h_4-\tfrac12)aq(r+h_6-2rh_6)>0.             \tag{9}
\end{split}
\]

The first term is strictly positive and the others are nonnegative.
The argument allows `r=1/2`, unlike a requirement that the effective
edge itself belong to a regular cap. Thus `phi+psi<pi`, with a strict
margin that persists in the finite sequence.

The other three finite turns in (6), computed before taking equal cap
heights, have signs

\[
-\chi_{3456},\qquad\chi_{3467},\qquad-\chi_{4567}.     \tag{10}
\]

The checker replays the exact formulas with arbitrary finite heights
`z3,z4,z5`; their positive factors are
`z5/(z3 z4)`, `(1-z5/z4)z5/(z3 z4)`, and
`(1-z5/z4)/z4`. By (3) and (5), the first and third turns are positive.
They put the two triangles on opposite sides of the diagonal, so (9)
bounds the actual interior angle at `P5`.

Consequently, **if `chi3467>0`, the finite critical quadrilateral is
strictly convex**. Its limit is a convex boundary of perimeter one.
This finite step retains possible zero limiting turns; assuming only
nonnegative turns of an arbitrary limiting polygon would not suffice.

## 4. Equal perimeter and tracking exclude the inner alternative

The direct section is

\[
B(t)=\bigl(0,\ 2tP_3,\ 2tP_2,
  2tP_2+(1-2t)P_7,\ (1-2t)P_7,\ (1-2t)P_6\bigr).      \tag{11}
\]

It has perimeter one for every `0<t<1/2`: its edge lengths sum to

\[
2t(L+h_1+h_2)+(1-2t)(M+h_6+h_7)=1.                   \tag{12}
\]

Suppose `A` is inner and `chi3467>0`. At height `v`, let `K` be the
convex limiting quadrilateral (6), and let `H` be the convex hull of
the limiting direct section. Finite nesting gives `K subset H`.
Convex perimeter monotonicity and (8), (12) give

\[
1=\operatorname{perim}K\le\operatorname{perim}H
\le\operatorname{length}B(v)=1.
\]

Strict monotonicity under proper inclusion forces `K=H`. Equality in
the polygonal triangle inequalities makes `B(v)` traverse the same
convex boundary without backtracking. It cannot be a segment because
its three upper-cap edges are nonzero and have nonparallel directions.
The common boundary is therefore a triangle or quadrilateral.
All four sides of (6) are nonzero, and `P5` is a genuine corner by
(9), so at least two of `C,D6,D7` are genuine corners.

Every edge of (11) is a positive height-dependent multiple of a fixed
cap edge. Convexity at `v` makes `B(t)` convex at every interior height:
its cyclic edge directions are unchanged. Its normal cones are fixed,
and its support function in each such cone is affine in `t`.

The following elementary tracking fact applies. Let an affine vertex
trajectory of the inner section be present on both sides of `v` and
be a genuine corner of the common boundary there. For each normal in
that corner's normal cone, the outer support value minus the inner
vertex's scalar projection is affine, nonnegative on both sides, and
zero at `v`. It vanishes identically. Two independent normals force
the inner trajectory to equal a single direct vertex trajectory.
The affine identity extends to both cap endpoints.

Finite containment supplies the needed nonnegative support differences.
After passage to the limit it still does: a limit of inner points
belongs to the limiting outer convex hull. This statement is valid
also at the critical height, by closure. No comparison between a
vanishing finite separation and an unknown rate of approach is used.

The common trajectories through the last three vertices of (6) are

\[
C(t)=2tP_3+(1-2t)P_6,\quad
D_6(t)=\frac t uP_4+(1-\frac t u)P_6,\quad
D_7(t)=\frac t uP_4+(1-\frac t u)P_7.                 \tag{13}
\]

The six direct trajectories, listed by lower and upper endpoint, are

\[
0\to0,\quad0\to P_3,\quad0\to P_2,\quad
P_7\to P_2,\quad P_7\to0,\quad P_6\to0.              \tag{14}
\]

None goes from `P6` to `P3`; regularity gives `P6!=P7,0` and `P3!=0`.
Therefore `C` cannot be a genuine corner. Both `D6,D7` must be genuine.
Only one direct trajectory starts at `P6`, so tracking `D6` gives

\[
P_4=\ell_uP_6.                                      \tag{15}
\]

The two trajectories starting at `P7` give, respectively,

\[
P_4=\ell_uP_7
\quad\text{or}\quad
P_4=2uP_2+\ell_uP_7.
\]

The first contradicts `P6!=P7`. The second, combined with (15), gives
`2uP2=-lu F`. But the two consecutive direct edges at `(1-2t)P7` are
`-2tP2` and `-(1-2t)F`, now nonzero opposite multiples of `F`.
They backtrack, contradicting the convex boundary conclusion.

Thus `A` cannot be inner when `chi3467>0`.

## 5. The upper quadrilateral and equal heights

The marked reflection `i -> 1-i mod 8`, with transverse reflection
and axial reversal, preserves both annuli and their nesting. It takes

\[
(u,v)\longmapsto(\tfrac12-v,\tfrac12-u),
\qquad \chi_{3467}\longmapsto\chi_{2356}.
\]

It preserves `v<u`, regular positive cap orientations, both markings,
all local metric equations, and the nearest bounds. The checker
replays its marked cocycle/gauge identities and annulus-face maps.
Applying the lower argument to the reflected sequence therefore
also excludes `A` inner when `chi2356>0`. This proves conclusion 1.

For `u=v`, the critical `A` section is the triangle

\[
(P_5,\ C=2uP_3+(1-2u)P_6,\ P_4).
\]

Equations (2) give its side lengths `s,r,h4`, with `r+s+h4=1`.
This holds also when `h4=0` or the triangle is collinear. The finite
sections converge to this same triangle whether their two intermediate
heights approach equality from above or below. A triangle, including
its degenerate segment convention, is a convex boundary of perimeter
one. If `A` were inner, the argument in Section 4 would force `B(u)`
to be the same convex boundary. The regular direct edges exclude a
segment, so `C` is a genuine triangle corner.

The trajectory `C(t)` is present in `A` on both sides of `u`. Tracking
would require a direct trajectory from `P6` to `P3`, absent from
(14). This contradiction proves conclusion 2. No sign of a limiting
mixed determinant, relative convergence rate, or nonzero `h4` is
assumed.

## Reproduction and precise residual scope

```sh
python research/type7_completion/remaining_c0_nested_quadrilaterals.py /tmp/c0-nested
python research/type7_completion/solver_cnf_certificates.py /tmp/c0-nested-rup \
  --checker /tmp/type7-rup-check /tmp/c0-nested
```

The six exported CNFs certify the
negative-cap exclusion, common turn, nesting implication, two height
turns, 363-word source coverage, and 67-word residual coverage. The
last coverage formula includes the two clauses proved geometrically
above; its replay alone is not a geometric exclusion proof.

For `0<v<u<1/2`, the surviving generic possibilities are:

| Inner annulus | `chi3467` | `chi2356` | Completions |
|---|---:|---:|---:|
| `B` | negative | negative | 16 |
| `B` | negative | positive | 11 |
| `B` | positive | negative | 11 |
| `B` | positive | positive | 5 |
| `A` | negative | negative | 24 |

All these are still necessary Boolean possibilities, not constructed
embeddings. In the remaining `A`-inner branch, each critical
quadrilateral has an unfavorable finite turn, so the convex
perimeter argument above cannot be applied without further geometry.
Every one of the 43 `B`-inner completions has `chi0136>0`,
`chi0237>0`, and `chi1267<0`. The companion checks the six direct
finite turns with unequal upper heights: their signs are
`chi0136,-chi0123,-chi0237,chi0127,chi1267,-chi0167`.
Thus the direct polygon has its unique reflex corner at the axis
vertex on edge 01, which also prevents a convex-inner argument.
Neither remaining nesting alternative is identified with C1 or
discarded by a ray-1 weight identity.
