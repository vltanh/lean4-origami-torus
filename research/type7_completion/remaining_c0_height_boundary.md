# Regular C0 on the height boundary

No ray-1 C0 limit with both endpoint caps noncollinear has

\[
u\in\{0,1/2\},\quad0<v<1/2,
\qquad\text{or}\qquad
v\in\{0,1/2\},\quad0<u<1/2.
\]

This closes all four open edges of the height rectangle. It includes all
zero individual deficits compatible with the two regular caps. It
does not assert an exclusion at the four corners or when a cap is
collinear. The proof uses the closed metric system and actual bracket
trits; a determinant that vanishes at the height endpoint is never
assigned a strict generic sign.

## 1. The metric places vertex 4 on the lower cap edge

First take `u=0`, `0<v<1/2`. The normalized heights are

\[
(0,1/2,1/2,1/2,0,v,0,0),\qquad P_0=P_1=0.
\]

Write `di=1/2-hi>=0`, with `sum(di)=1/2`. Put

\[
L=d_1+d_2=|P_3|>0,\quad M=d_6+d_7=|P_6|>0,
\quad D=d_0+L+M\le1/2,\quad\ell_v=1-2v>0.
\]

Both cap triangles have perimeter one. Regularity gives
`d1,d2,d6,d7>0`. The closed source rows at this height give

\[
T_{46}=0,\qquad vT_{47}=0,\qquad T_{67}=0.
\]

The second row retains the fifth product-scale syzygy; the companion
checks all coefficients against the full 29-row system. Since `v>0`,
all three corresponding projected lengths equal their horizontal
lengths. Set `r=d4+d5`. They are

\[
|P_4-P_6|=r,\quad |P_4-P_7|=h_6-r,\quad |P_7-P_6|=h_6.
\tag{1}
\]

The second length is strictly positive because

\[
h_6-r=d_0+d_1+d_2+d_3+d_7>0.
\]

Equality in the triangle inequality therefore forces

\[
P_4=P_6+\frac{r}{h_6}(P_7-P_6),\qquad0\le r/h_6<1.
\tag{2}
\]

There are exactly two cases: `4` lies strictly between `6,7`, or
`P4=P6` when `r=0`. No lower bound on a positive `r` is used.

## 2. A source adapted to the height endpoint

Normalize `C23=cross(P2,P3)>0`. Every vertex outside 123 is strictly
below that cap, so its five ordered cap brackets are negative.
For the lower cap, only vertices `1,2,3,5` are strictly above it.
The actual bracket `[0467]` is zero. Its generic completion remains
free; the interior-C0 cap unit involving vertex 4 is not used.

For each case in (2), the source retains the full necessary topology
and linking formula, actual trits with zero-safe generic completions,
affine cocycles, weak Grassmann–Pluecker relations, and the exact
interpolation at vertex 4. Its two strict height cuts are
`{1,2,3}` and `{1,2,3,5}`. The checker directly expands all seventy
brackets in the fifteen anchors `[01ij]`. All 55 nontrivial relations
have coefficient signs fixed on `0<v<1/2`; endpoint evaluation checks
these signs exactly.

The regular lower cap supplies three rank clauses. For each nonzero
vector `P2,P3,P3-P2`, its cross products with the two independent
vectors `P6,P7` cannot both vanish. The companion verifies the exact
vector identities and every associated determinant factor.

Six exported CNFs establish the following, with one copy for each
case in (2):

| Stage | Actual conclusion |
|---|---|
| Negative lower-cap orientation | Impossible |
| Positive lower-cap orientation | `[0127]<0` |
| Positive lower cap and the strict metric turn | All signs in (3) below |

The core identity `d0=h1*h7+P2 dot P7` and the strictly negative
core bracket allow the analytic [strict turning argument](exhaustive_c0_turning.md).
That argument uses only the endpoint triangles, the core identity,
and the deficit budget. It is independent of the intermediate heights.
It supplies actual `[2367]>0`, `[0237]>0`, and `[1267]<0`, which are
the premises of the last two CNFs.

The resulting actual signs are

\[
\begin{gathered}
C_{36},C_{26},C_{35},C_{56}\le0,\\
[0356]\ge0,\quad[1356]\le0,\quad[0357]\ge0,\\
[1367]<0,\qquad[3567]<0.
\end{gathered}
\tag{3}
\]

Strict conclusions are encoded by negating the required actual trit
bit, so their zero violations are included in the UNSAT obligations.

## 3. The last vertex lies in a closed parallelogram

Let

\[
F=P_7-P_6,\qquad Q_5=P_5-2vP_3-\ell_vP_6,
\qquad s=|Q_5|=d_3+d_4+\ell_vD>0.
\tag{4}
\]

First assume `C36<0`, so `P3,P6` are independent. Write
`P5=aP3+bP6`. The four weak signs `C35,C56,[0356],[1356]` in (3),
together with

\[
2[0356]=\operatorname{cross}(P_5-2vP_3,P_6),\qquad
2[1356]=-\operatorname{cross}(P_3,P_5-\ell_vP_6),
\]

give `0<=a<=2v` and `0<=b<=lv`. Thus

\[
Q_5=-cP_3-dP_6,\qquad0\le c\le2v,\quad0\le d\le\ell_v.
\tag{5}
\]

The two strict signs in (3) give

\[
\operatorname{cross}(F,P_3)>0,\qquad
\operatorname{cross}(F,Q_5)>0,
\tag{6}
\]

because `2[1367]=cross(P3,F)` and
`2[3567]=cross(Q5,F)`. All factors are checked exactly.

Apply the [endpoint support bound](exhaustive_c0_endpoint_bound.md)
after exchanging the caps by the checked marked reflection. Its
transverse map is `R=diag(1,-1)`. The new upper and lower stems are
`U=R P6`, `V=R P3`; the new upper edge vector is `G=-R F`.
Both cap orientations remain positive, their core identity is the
same, and their strict turn is preserved. Put

\[
c_E'=\operatorname{cross}(G,V)=\operatorname{cross}(F,P_3)>0,
\qquad C'=\operatorname{cross}(U,V)=C_{36}<0.
\]

The support theorem therefore says

\[
R'=h_6(-C')/c_E'<D.
\tag{7}
\]

This invocation uses only the cap geometry, not an interior-height
assumption on the reflected configuration.

The strict norm argument from the
[closed cone proof](solver_remaining_c0_opposite_cones.md#2-nonparallel-cap-stems)
now contradicts (6). Here are its details in this setting.
Write `Q=R Q5=-dU-cV` and `A'=C67>0`. If
`cross(G,Q)>=0`, then `d*A'>=c*cE'`. Since `Q` is nonzero,
`d>0` and `theta=c*cE'/(d*A')` lies in `[0,1]`.
The identity `C'G=cE'U+A'V` yields

\[
-Q=d\left((1-\theta)U+\theta(C'/c_E')G\right).
\]

Both endpoint norms, `|U|=M` and `R'`, are strictly below `D`.
Consequently

\[
|Q_5|=|Q|<dD\le\ell_vD\le s,
\]

contradicting (4). Hence `cross(G,Q)<0`. But the reflection gives
`cross(G,Q)=cross(F,Q5)>0` by (6), completing this case. The
argument includes `theta=1` and zero cone coefficients.

## 4. Parallel stems, without dividing by their determinant

It remains to consider `C36=0`, the only other sign allowed by (3).
Choose `P3=(L,0)`. Since `C23>0`, the second coordinate of `P2`
is negative. The sign `C26<=0` then forces

\[
P_6=(-M,0),\qquad M>0.
\]

Positive lower orientation gives `P7_y<0`, and hence `F_y<0`.
The signs `C35<=0` and `[0356]>=0` force `P5_y=0`:
their exact expressions are `L*P5_y` and `M*P5_y/2`.
Thus `Q5` is horizontal. By (6), it points strictly right.
Finally

\[
2[0357]=(P_{5x}-2vL)P_{7y}\ge0
\]

implies `P5_x<=2vL`, so

\[
0<Q_{5x}=P_{5x}-2vL+\ell_vM\le\ell_vM.
\]

This contradicts `|Q5|=s>=lv*D>lv*M`, because `D=M+L+d0>M`.
All vanishing brackets retain their zero values throughout.

## 5. Reflection and scope

The marked cap swap `p(i)=1-i mod8` sends

\[
(u,v)\longmapsto(1/2-v,1/2-u).
\]

It maps the proved edge to `v=1/2`, `0<u<1/2`. The exact cocycle,
horizontal displacement, and height identities are checked. The new
axis is the reverse of edge 01, whose limiting length is positive,
so reanchoring is bounded. Both possible lower-cap orientations were
handled above; a spatial reflection to restore the anchor convention
does not lose a case.

This proves two edges. The other two admit the following shorter
section argument.

## 6. The upper-height edge and its reflection

Now take `u=1/2`, `0<v<1/2`, still with both caps regular. The closed
source gives `T34=0` and `(1-2v)T24=0`; the latter includes minus
the second product-scale syzygy. Thus `T24=0`. In addition to the
unit-perimeter triangle 123, triangle 234 has side lengths

\[
h_2,\quad h_3,\quad d_2+d_3,
\]

and perimeter one. It may initially be collinear.

Cut the source triangulation along 123 and 067. The direct annulus
`B` has six faces and no intermediate vertex; its complementary
annulus `A` has ten faces and contains vertices 4 and 5. These are
the [source-checked C0 annuli](solver_remaining_c0_sections.md).

For a sufficiently late finite embedding, make an arbitrarily fine
generic perturbation preserving every normalized coordinate, metric
residual, and auxiliary limit. Reanchor 01, then flatten the plane
through 067 by a shear of the normalized height coordinate. The
lower cap is regular, so the shear tends to zero. All other vertices
stay above it. Both annulus sections near that cap surround a fixed
interior point of its projected triangle, and hence are nested.
Their nesting order cannot change while the two section cycles stay
disjoint. Vertex 5 has contiguous upper and lower neighbors in its
link, so its single critical height does not split or join a cycle.

For each fixed height `t` with `v<t<1/2`, vertices `1,2,3,4` lie
above the section eventually, while vertex 5 lies below it. The
section edges are

\[
\begin{aligned}
B:&\quad01,03,02,27,17,16,\\
A:&\quad35,25,45,47,46,36.
\end{aligned}
\]

The checker binds each consecutive pair to its original face and
checks their endpoint limits. First pass to the sequence limit at
fixed `t`, then let `t` increase to `1/2`. The two polygonal curves
converge respectively to

\[
(P_1,P_3,P_2,P_2,P_1,P_1),\qquad
(P_3,P_2,P_4,P_4,P_4,P_3).
\tag{8}
\]

Nesting of the finite curves implies inclusion of their convex
hulls: the inner curve lies in the outer bounded Jordan region,
which lies in its convex hull. Convex hulls depend continuously on
these finite vertex lists. After taking both limits in the indicated
order, one of triangles 123 and 234 therefore contains the other.
The choice of inner annulus is fixed after taking a subsequence.

Both triangles have perimeter one, also when a triangle degenerates
to a segment with perimeter twice its length. Perimeter is strictly
increasing under proper inclusion of compact convex planar sets.
For example, its Cauchy support-function formula proves strictness:
proper inclusion makes the support difference positive on an open
arc of directions. Hence the two convex hulls in (8) must be equal.

Triangle 123 is noncollinear. Its three vertices are therefore the
three extreme points of this common hull. Triangle 234 already has
the two distinct vertices `P2,P3`; equality forces `P4=P1=0`.
But then

\[
h_3=|P_4-P_3|=|P_3|=d_1+d_2,
\qquad d_1+d_2+d_3=1/2.
\]

This contradicts the deficit budget, since the regular lower cap
has `d6,d7>0`. The checked cap swap gives the remaining edge
`v=0`, `0<u<1/2`.

The four corners and collinear cap boundaries remain outside this
note. This is an exclusion of limits of actual unbounded embedded
sequences, with no explicit numerical height.

## Reproduction

```sh
python research/type7_completion/remaining_c0_height_boundary.py /tmp/c0-height-boundary
python research/type7_completion/solver_cnf_certificates.py /tmp/c0-height-boundary-rup \
  --checker /tmp/type7-rup-check /tmp/c0-height-boundary
```

The source checker verifies the nine closed metric rows, the edge
lengths forcing (2), the radius and determinant formulas, all 55 height
relations, the rank identities, and the existing endpoint support
identities. The second argument adds eight closed metric rows,
twelve section-edge bindings, and the intermediate vertex link.
All six exported CNFs require independently accepted RUP proofs.
The support, norm, and nesting estimates are the analytic arguments above.
