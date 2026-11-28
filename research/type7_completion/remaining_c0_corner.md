# Regular C0 at the four height corners

No unbounded embedded ray-1 sequence has a C0 limit with both cap
triangles 123 and 067 noncollinear and
`(u,v) in {0,1/2} x {0,1/2}`.

At `u=0,v=1/2`, the closed metric puts vertices 4 and 5 on existing
cap edges. Seven actual-trit certificates reduce the possibilities to one
coincidence. A section of the remaining limiting surface would then
be the sum of two positively oriented triangles with overlapping
interiors. Its winding number is two at an interior point, whereas
the finite sections are simple closed curves. All arguments retain
actual zero brackets and arbitrary relative collapse rates.
Two further certificates and nested unit-perimeter triangles exclude
`u=v=0` and its reflection. The fourth corner is already covered by
the complete two-block proof.

## 1. Two exact segment positions

The normalized heights are

\[
(0,1/2,1/2,1/2,0,1/2,0,0),\qquad P_0=P_1=0.
\]

Use `di=1/2-hi>=0`, with `sum(di)=1/2`. Regularity gives
`d1,d2,d6,d7>0`. Set

\[
E=P_3-P_2,\quad F=P_7-P_6,\quad
r=d_4+d_5,\quad s=d_3+d_4.
\]

The closed 29-row metric system gives

\[
T_{46}=T_{47}=T_{35}=T_{25}=0.
\]

The `47` and `25` rows retain their respective product-scale
syzygies. The exact projected lengths are therefore

\[
\begin{aligned}
|P_4-P_6|&=r,& |P_4-P_7|&=h_6-r,& |P_7-P_6|&=h_6,\\
|P_5-P_3|&=s,& |P_5-P_2|&=h_2-s,& |P_3-P_2|&=h_2.
\end{aligned}
\tag{1}
\]

Both differences on the right are strictly positive:

\[
h_6-r=d_0+d_1+d_2+d_3+d_7>0,\qquad
h_2-s=d_0+d_1+d_5+d_6+d_7>0.
\]

Equality in the two triangle inequalities proves

\[
P_4=P_6+(r/h_6)F,\qquad
P_5=P_3-(s/h_2)E,
\tag{2}
\]

with both fractions in `[0,1)`. Each point is either strictly inside
the indicated segment or equals its first endpoint. The opposite
endpoint cannot occur.

## 2. A complete source for all four segment cases

Normalize `C23=cross(P2,P3)>0`. The only strict height cut separates
`{1,2,3,5}` from `{0,4,6,7}`. The upper cap units are used only
against vertices `0,4,6,7`; the lower cap units are used only against
`1,2,3,5`. Both actual `[1235]` and `[0467]` are zero and leave
their generic signs free.

For each of the four choices in (2), the source includes all
necessary topology and linking clauses, actual positive/negative
trits, affine five-point cocycles, weak Grassmann–Pluecker relations,
and the exact positive interpolation or coincidence of each extra
vertex. All 55 nontrivial height identities are checked directly
against the seventy determinant expansions. The three rank clauses
for `P2,P3,E` against the independent lower cap vectors exclude only
paired zeros.

The seven independently replayable obligations prove:

| Cases | Actual conclusion |
|---|---|
| All four segment choices; negative lower orientation | Impossible |
| Both extra vertices strictly inside their segments; positive lower orientation | Impossible |
| `P5=P3`, with either allowed position of 4; positive lower orientation | `[0127]<0` and `[1367]<0` |

There are four, one, and two CNFs respectively. The last conjunction
uses strict actual trit bits; its negation includes zero values.

The marked reflection `p(i)=1-i mod8` preserves this height corner
and exchanges `r` with `s`. It exchanges the two positively oriented
regular caps after the checked axial/transverse reversal. Thus, if
only vertex 4 is coincident, reflect to put vertex 5 in coincidence.
The case of two coincidences is already present. Consequently it
suffices to consider

\[
P_5=P_3,\quad P_4=P_6+\lambda F,\quad0\le\lambda<1,
\quad C_{23},C_{67}>0,
\quad [0127],[1367]<0.
\tag{3}
\]

All cocycle and deficit transformations are checked exactly.

## 3. A lower edge enters the upper triangle

The closed core identity is

\[
d_0=h_1h_7+P_2\cdot P_7.
\]

Together with `[0127]<0`, the regular cap metrics, and the deficit
budget, it permits the analytic
[strict turning lemma](exhaustive_c0_turning.md). That argument uses
only the two caps and the core, so remains valid at this height
corner. It gives

\[
\operatorname{cross}(E,F)>0.
\]

The second strict bracket in (3) gives

\[
\operatorname{cross}(F,P_3)>0,
\qquad 2[1367]=\operatorname{cross}(P_3,F).
\]

It follows that `F` is strictly inside the positive cone spanned by
`-P3,-E`: the three relevant cross products are

\[
\operatorname{cross}(-P_3,-E)=C_{23}>0,\quad
\operatorname{cross}(-P_3,F)>0,\quad
\operatorname{cross}(F,-E)>0.
\tag{4}
\]

This cone is exactly the interior tangent cone at `P3` of the
positively oriented triangle with vertices `0,P2,P3`.

## 4. A section with winding number two

Fix any normalized section height `t` in `(0,1)`, corresponding to
physical normalized axial height `t/2`. For a sufficiently late
finite member, exactly the four vertices in the upper cut are above
this plane. The eight faces of the complementary C0 annulus cut it
in the cyclic edge order

\[
14,24,45,57,05,56,36,34.
\tag{5}
\]

Each consecutive pair belongs to an original source face; the
checker verifies all eight bindings. The finite polygon is a simple
closed curve because it lies on the embedded surface and these
segments form one cycle. Projection from the section plane to the
transverse plane is injective.

In the limit (3), put

\[
H=(1-t)P_4,\quad K=H+tP_3,
\qquad L_i=tP_3+(1-t)P_i\quad(i=0,6,7).
\]

The exact limiting vertex sequence is

\[
H,\quad H+tP_2,\quad K,\quad L_7,\quad L_0,
\quad L_6,\quad L_6,\quad K.
\tag{6}
\]

Moreover `K=L6+lambda*(L7-L6)`. Thus this closed curve is the
concatenation, with a possible subdivision of an edge, of the two
triangle boundaries

\[
\mathcal T_u=\operatorname{conv}\{H,H+tP_2,K\},
\qquad
\mathcal T_l=\operatorname{conv}\{L_6,L_7,L_0\}.
\tag{7}
\]

Both are nondegenerate and positively oriented: their signed double
areas are `t^2*C23` and `(1-t)^2*C67`. In the first triangle, the
interior tangent cone at `K` is generated by `-P3,-E`. By (4), a
short segment from `K` in direction `F` lies strictly inside this
triangle. Since `lambda<1`, the same short segment lies along the
lower triangle's edge towards `L7`. A sufficiently small displacement
from an interior point of that segment into the lower triangle
therefore belongs to the interiors of **both** triangles. This
argument includes `lambda=0`.

Choose such a point away from both boundaries. The winding number
of (6) about it is the sum of the two positive triangle winding
numbers, hence equals two. The ordered finite section vertices
converge to (6). Winding number is stable under a sufficiently small
uniform perturbation that avoids the chosen point, so every
sufficiently far finite section also has winding number two.
This is impossible for a simple closed polygon, whose winding number
off its boundary is zero or one in absolute value.

This contradiction excludes every case in (3), completing the
regular corner proof. No comparison between shrinking edges, cap
widths, and the inverse height was needed.

## 5. Both intermediate vertices at the lower height

At `u=v=0`, the closed source also gives

\[
T_{45}=T_{46}=T_{56}=0.
\]

Thus triangle 456 has side lengths `h4,h5,d4+d5` and perimeter one.
Triangle 067 has perimeter one and is regular by hypothesis.

Use the same direct six-face annulus and complementary ten-face
annulus as in the [height-boundary proof](remaining_c0_height_boundary.md).
This time flatten the upper regular cap 123 by a vanishing normalized
height shear. All other vertices stay strictly below that plane.
Near the upper cap, the two finite section polygons are simple,
disjoint, and nested. For any fixed normalized height `0<t<1`, all
five other vertices are below the section eventually. There is no
intermediate vertex event between that section and the upper cap,
so nesting persists down to that fixed height.

The section-edge cycles are

\[
B:\quad01,03,02,27,17,16,\qquad
A:\quad14,24,25,35,36,34.
\]

First pass to the sequence limit at fixed `t`, then let `t` decrease
to zero. The checker verifies that their limiting vertex lists are

\[
B:\quad(0,0,0,P_7,P_7,P_6),\qquad
A:\quad(P_4,P_4,P_5,P_5,P_6,P_4).
\tag{8}
\]

The nested finite curves have nested convex hulls. Passing to these
limits shows that one of triangles 067 and 456 contains the other.
Their equal perimeters force equality of the convex hulls by strict
convex-perimeter monotonicity. Because 067 is regular, the common
hull has three distinct extreme points. Both triangles already
contain `P6`, so exactly two matches remain:

\[
(P_4,P_5)=(0,P_7)\quad\text{or}\quad(P_7,0).
\tag{9}
\]

The second match is metrically impossible. It gives `h4=h7` and
`h5=|P6|=d6+d7`, or

\[
d_4=d_7,\qquad d_5=1/2-d_6-d_7.
\]

The deficit budget would therefore imply
`d0+d1+d2+d3+d7=0`, contradicting regularity.

For the first match, two additional actual-trit CNFs exclude both
orientations of the regular lower cap. Their source uses only the
strict height cut `{1,2,3}`, the cap units against vertices at the
opposite level, exact coincidences `P4=P0` and `P5=P7`, the 55
constant-coefficient height identities, rank clauses, and the full
necessary topology. Lower-level cap brackets remain actual zeros.
This closes `u=v=0`. The checked cap swap sends it to `u=v=1/2`.

## 6. The completed two-block corner

At `u=1/2,v=0`, the exact cyclic intrinsic vertical steps are

\[
(1/2,0,0,0,1/2,0,0,0).
\]

The companion computes them from the original marked cocycle. This
is precisely the phase covered by the
[complete ray-1 two-block exclusion](ray1_two_block_exclusion.md),
including all product scales and relative degeneration rates. No
additional cap assumption or numerical threshold is needed there.
Together, these arguments close all four regular height corners.

## Reproduction and scope

```sh
python research/type7_completion/remaining_c0_corner.py /tmp/c0-corner
python research/type7_completion/solver_cnf_certificates.py /tmp/c0-corner-rup \
  --checker /tmp/type7-rup-check /tmp/c0-corner
```

The checker verifies eleven closed metric rows with all product
scales retained, both segment positions and strict endpoint gaps,
the rank and determinant factors, 55 height identities, the marked
reflection, all eight section-face bindings, the exact two-triangle
section decomposition, and both orientation factors. The equal-height
corner adds nine source rows, twelve section-face bindings, and 24
endpoint identities. All nine CNFs must independently replay. The
nesting, convex-perimeter, triangle-overlap, and winding arguments
are the analytic proofs above.

Collinear endpoint caps are separate cases. This result gives no
explicit numerical height threshold.
