# A regular cap excludes two complete open height edges

There is no unbounded embedded ray-1 sequence with a C0 limit satisfying

\[
u=1/2,\qquad 0<v<1/2,
\]

whose lower endpoint triangle 067 is noncollinear. The upper triangle
123 may be collinear, including a coincident pair. The marked cap swap
also excludes `v=0`, `0<u<1/2` whenever 123 is regular.

The case of two regular caps was proved in the
[earlier height-boundary theorem](remaining_c0_height_boundary.md).
The argument below completes the opposite collinear cap. It uses five
independently replayable actual-trit certificates and the existing angle
certificate on its **closed** parameter domain. It does not identify
generic completion signs with the signs of zero limiting determinants.

## 1. Equal-perimeter upper triangles

Write `di=1/2-hi>=0`, `sum di=1/2`, and `Pi` for transverse points,
with `P0=P1=0`. The upper four vertices have limiting height `1/2`,
vertex 5 has height `v`, and 067 has height zero. Put

\[
L=d_1+d_2,\qquad M=d_6+d_7.
\]

Regularity of 067 gives `d6,d7>0`, so `L<1/2` and `h1,h2>0`.
The closed source rows give `T34=0` and `(1-2v)T24=0`, retaining
the product-scale syzygy in the second equation. Hence triangle 234
has side lengths `h2,h3,d2+d3`, with perimeter one. Triangle 123
also has perimeter one.

Apply the finite-section argument from Section 6 of the earlier
height-boundary proof. Its nesting step uses only regularity of **067**:
flatten this cap by a vanishing normalized height shear; both annuli
give nested simple sections, and the single interior vertex event at 5
does not split their cycles. For a fixed height above 5, the two section
cycles have edge lists

\[
\begin{aligned}
B:&\quad01,03,02,27,17,16,\\
A:&\quad35,25,45,47,46,36.
\end{aligned}
\]

First pass to the sequence limit, then increase the section height to
`1/2`. The convex hulls become respectively triangles 123 and 234.
They are nested and have equal perimeter, where a segment's perimeter
is twice its length. Strict monotonicity of planar convex perimeter
therefore forces their convex hulls to coincide. This conclusion does
not require either upper triangle to be noncollinear.

The companion verifies all twelve source-face bindings and limiting
vertices, as well as the nine closed metric rows used here and below.

## 2. Four exhaustive collinear orders

Suppose 123 is collinear and choose a transverse unit vector `e` with
`P2=h1 e`. Its three lengths are `h1,h2,L`. Since `L<1/2`, the only
possibilities are `d1=0`, `d2=0`, or both. An edge of length zero or
the alternative equality `L=h1+h2=1/2` would contradict `M>0`.

If `d1=0<d2`, then `P3=d2 e` is strictly between `P1=0` and
`P2=e/2`. Equality of the upper hulls forces `P4=P1`. Thus
`h3=d2`, or `d2+d3=1/2`, again contradicting `M>0`.

In every remaining case `d2=0`, and the common hull fixes

\[
P_2=(1/2-d_1)e,\qquad P_3=-d_1e,\qquad
P_4=(1/2-d_1-d_3)e.
\tag{1}
\]

The last coefficient is strictly positive because

\[
1/2-d_1-d_3=d_0+d_4+d_5+M>0.
\]

There are exactly four cases:

| Case | Upper point order |
|---|---|
| `d1>0,d3>0` | `P3 < P1 < P4 < P2` along `e` |
| `d1>0,d3=0` | `P3 < P1 < P4=P2` |
| `d1=0,d3>0` | `P3=P1 < P4 < P2` |
| `d1=d3=0` | `P3=P1 < P4=P2` |

These are actual limiting affine relations. Their strictly positive
interpolation coefficients are checked from (1); no shrinking finite
length or cap area is divided by.

## 3. The endpoint-adapted sign source

Orient the transverse plane so `cross(P6,P7)>0`. The generic source
retains the full topology and absolute-linking clauses. It removes
only the arbitrary ambient-orientation unit `[0123]>0`; this unit
must not select the freely varying generic completion of the zero
upper area after the lower cap has fixed the ambient orientation.

The strict height cuts have high sets `{1,2,3,4}` and
`{1,2,3,4,5}`. The source does **not** reuse the interior cut
`{1,2,3}`. It adds all actual positive lower-cap brackets, the
interpolation or coincidence in the table, the affine cocycle and
weak Grassmann--Pluecker relations, and all 55 exact height relations.
Each nonzero coefficient has a fixed sign for `0<2v<1`, certified
by its two endpoint values. The lower-cap rank clause follows from

\[
(P_2\times P_6)P_7-(P_2\times P_7)P_6
 +(P_6\times P_7)P_2=0,
\]

since `P2!=0` and `P6,P7` are independent.

Five CNFs prove:

| Cases | Necessary conclusion |
|---|---|
| First row of the order table | Impossible |
| Second and third rows, one CNF each | `[0127]<=0` and `[1267]>=0` |
| Fourth row | `[0127]<=0` |
| Fourth row, after the strict metric turn below | `[3456]<=0` and `[4567]<=0` |

The first three rows are excluded once the metric turn is applied.
All actual zeros retain free generic completion signs.

## 4. The strict turn needs only the regular lower cap

Here `E=P3-P2=-e/2` and `F=P7-P6`. The exact core equation is

\[
d_0=h_1h_7+P_2\cdot P_7.
\tag{2}
\]

The angle argument of the
[strict turn theorem](exhaustive_c0_turning.md) extends directly to
`d2=0` with the lower cap regular. The upper tip angle is zero.
For clarity, write `si=2di`, let `B` be the lower tip angle at 7,
and let `phi` be the counterclockwise angle from `P2` to `-P7`.
The certified inequality `[0127]<=0` makes `0<=phi<=pi`. Equation
(2) gives

\[
\tan^2(\phi/2)=s_0/D_*,\qquad
D_*=s_3+s_4+s_5+s_6+s_1s_7>0.
\]

Put `U=s1+s6`, `V=s7`, `W=1-U-V=s0+s3+s4+s5`. The same
half-angle merging inequality applies with the zero upper angle, and

\[
D_*-UV=s_6(1-s_7)+s_3+s_4+s_5>0.
\]

If `W>0`, the tangent-product proof gives `B+phi<pi`; if `W=0`,
then `s0=0`, `phi=0`, and the regular lower triangle has `0<B<pi`.
Thus, in both cases, `0<B+phi<pi`. Its orientation gives

\[
[2367]>0,\qquad[1267]<0,\qquad[0237]\ge0.
\tag{3}
\]

Only the last inequality may be equality, when `phi=0`. These are
exactly the actual trit premises of the fifth CNF. In particular,
(3) contradicts `[1267]>=0` in rows two and three of the table.

## 5. The double coincidence and the closed angle certificate

Only `P1=P3=0`, `P2=P4=e/2` remains. Its actual `[2345]` is
zero. The fifth CNF and (3) give `[3456]<=0` and `[4567]<=0`.

Use the metric notation and proof of
[the height-order theorem](remaining_c0_height_order.md), now at

\[
k=\frac{1-2u}{1-2v}=0,\qquad l=\frac vu=2v\in(0,1).
\]

Every needed norm is positive, since `d6,d7>0` and the deficit
budget leaves strictly less than `1/2` in either middle pair. The
slack `b_*=d0+d1+d7` is strictly positive. The existing exact Gram
certificate is stated and checked for the **closed** square
`0<=k,l<=1`; its strict lower bound `(2b_*)^8` persists at `k=0`.
The norm identities, cosine bounds, and scalar continuity path also
remain valid there. Consequently its three-angle sum is still
strictly below `pi`.

The signs `[2345]=0`, `[4567]<=0`, and `[3456]<=0` give precisely
the clockwise path from `-E` to `-F` used in that proof. Equation
(3) puts the counterclockwise angle from `E` to `F` strictly between
zero and `pi`. A clockwise path between these directions must have
length greater than `pi`, contradicting the strict three-angle bound.
This excludes the last order.

## 6. Reflection, reproduction, and scope

The checked marked cap swap `p(i)=1-i mod8` sends
`(u,v)` to `(1/2-v,1/2-u)` and exchanges the caps. It carries the
proved edge to `v=0`, `0<u<1/2`, with regular upper triangle 123.
No relation between any degeneration rates was used.

```sh
python research/type7_completion/remaining_c0_one_regular_height.py /tmp/c0-one-regular-height
python research/type7_completion/solver_cnf_certificates.py /tmp/c0-one-regular-height-rup \
  --checker /tmp/type7-rup-check /tmp/c0-one-regular-height
```

The result includes the previously proved regular-cap cases on these
two edges. It leaves the other choices of the regular cap, the opposite
two height edges, both-collinear height boundaries, and corners separate.
It does not claim a complete ray-1 exclusion or a new Lean theorem.
