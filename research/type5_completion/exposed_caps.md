# An exposed-cap obstruction for Type 5

## Result and scope

**Theorem.** Let seven points labelled `0,1,2,3,4,5,6` realize an embedded
linear simplicial complex containing the following ten triangles:

\[
031,\ 053,\ 045,\ 136,\ 164,\ 465,
\qquad 012,\ 024,\ 236,\ 256.
\]

Suppose `2` is strictly supported: a plane through `2` has all six other
vertices strictly on one side. Then the two nondegenerate triangles `014`
and `356` cannot both be **strictly exposed caps**. Here strict exposure
means that the plane of the cap has every vertex outside that cap,
including `2`, strictly on one side.

Consequently this obstruction applies to an embedded Type 5 realization
whenever both cap planes have that strict support property. It uses no
metric, curvature, flat-star, linking, or support assumption at any vertex
other than `2`. Vertex `7` and triangle `125` are unnecessary.

This is a conditional geometric obstruction. It does not establish that
both cap planes support every finite F1 realization. Proving that support
property, or controlling its failure, remains a separate task.

The same conclusion holds for **weakly** supporting cap planes when the
six cap vertices are not all coplanar; see Section 5.

## 1. Generic reduction and projective normalization

We may assume that no four of the seven vertices are coplanar. Indeed,
linear embeddings of a fixed finite simplicial complex are stable under
sufficiently small perturbations of its vertices. This can be checked
simplex by simplex; near a common face, use the corresponding transverse
cones, and away from common faces use positive separation. Strict support
at `2` and strict cap exposure are also open conditions. Thus a proposed
nongeneric counterexample could be perturbed to a generic one while
retaining all hypotheses. No metric is used in this theorem, so the
perturbation need not preserve edge lengths.

Translate `2` to the origin and choose affine coordinates in which the
other vertices have positive third coordinate `z`. The projective map

\[
 (x,y,z)\longmapsto (X,Y,Z)=(x/z,\ y/z,\ -1/z)
\]

sends `2` to downward vertical infinity. It preserves the embedded complex
away from `2`. Each edge `2v` becomes the downward ray from `v`, and each
triangle `2ij` becomes the downward vertical curtain under the segment
`ij`.

Both cap planes become upper supporting planes. For example, write an
original cap halfspace as

\[
 ax+by+cz+d\geq 0,
\]

where the cap is the zero set and all other vertices satisfy the strict
inequality. Because `2` is the origin, `d>0`. After the projective map this
inequality is

\[
 Z\leq (aX+bY+c)/d.
\]

Let lower-case point labels denote the horizontal projections of the six
finite vertices. Genericity ensures that no three projected points are
collinear. The projected closed cap triangles `014` and `356` are disjoint:
at a hypothetical common projected point, the lift on each cap would have
to lie strictly below the other cap's upper supporting plane.

Adding the two cap disks to the six side triangles gives an embedded
octahedral sphere `O`, whose face set is

\[
\mathcal O=\{014,356,031,053,045,136,164,465\}.
\]

Strict exposure makes this immediate: a cap plane meets any triangle of
the original complex precisely in the convex hull of their common cap
vertices. The two cap disks are disjoint. The abstract sphere has opposite
vertex pairs `06`, `15`, and `34`.

## 2. Two planar consequences of embedding

### 2.1 No vertex is inside a nonincident projected octahedral face

For each finite vertex `v`, the downward ray `2v` meets the capped sphere
only at `v`. Its intersections with original side faces are excluded by
embedding. Its intersections with the added caps are excluded by their
strict support planes.

If the projection of `v` were inside the projection of a nonincident face
`F` of `O`, the point of `F` above that projection would be strictly below
`v`: the cap containing `v` is an upper support plane, and `F` has at least
one vertex strictly below that plane. The downward ray would meet `F`.
Therefore

\[
 v\notin\operatorname{int}\triangle F
 \quad(v\notin F,\ F\in\mathcal O).
 \tag{V}
\]

Because there are no collinear triples, a nonincident vertex cannot lie
on the boundary of such a projected triangle either.

### 2.2 The four curtain side conditions

The curtains under `01`, `04`, `36`, and `56` are disjoint from `O` except
along their top edges. Each curtain without its top edge is connected and
unbounded, so it lies in the unbounded component of the complement of
`O`.

At an interior point of one of these edges, take a small transverse
section. One incident octahedral face is the upper cap; the other has its
third vertex strictly below that cap plane. The bounded side of the
sphere lies below the support plane. If the projections of these two
incident faces were on opposite sides of their common edge, the downward
vertical direction would enter the bounded side between them. The curtain
would then enter the interior of `O`, a contradiction. Hence the two
projected incident faces lie on the same side of their common edge.

Writing `p ~ q across ij` for points `p,q` on the same strict side of line
`ij`, we obtain

\[
 3\sim4\text{ across }01,\qquad
 5\sim1\text{ across }04,\qquad
 1\sim5\text{ across }36,\qquad
 4\sim3\text{ across }56.
 \tag{C}
\]

## 3. The planar convexity lemma

**Lemma.** Suppose six planar points `0,1,3,4,5,6` have no collinear
triples, their closed cap triangles `014` and `356` are disjoint, and
conditions `(V)` and `(C)` hold. They form a strictly convex hexagon. Up
to reversal, its cyclic order is

\[
 0,1,3,6,5,4
 \quad\text{or}\quad
 0,1,5,6,3,4.
 \tag{H}
\]

### 3.1 The two pole vertices are extreme

We first prove that `0` is extreme. Put the ray `01` at angle `0` and the
ray `04` at angle `theta`, with `0<theta<pi`. The first two conditions in
`(C)` put the rays to `3` and `5` at angles

\[
 0<\alpha<\pi,
 \qquad \theta-\pi<\beta<\theta.
\]

Consider the four positive cones spanned by the consecutive pairs in the
cycle

\[
 1\longrightarrow3\longrightarrow5\longrightarrow4\longrightarrow1.
\]

These four cones cover the positive cone of all four rays. Here is the
elementary angular check. The cones `13`, `54`, and `41` cover the entire
angle interval

\[
 [m,M],\qquad m=\min(0,\beta),\quad M=\max(\alpha,\theta).
\]

If `M-m<pi`, the two extreme rays are one of the pairs `13`, `35`, `54`,
or `41`, so one of the four cones contains that whole interval. If
`M-m>pi`, necessarily `beta<0` and `alpha>theta`; the positive cone `35`
covers the complementary circular arc from `alpha` to `beta+2pi`.
Together the four cones then cover every direction. Equality would give
a collinear triple and is excluded.

If `0` were not extreme, the opposite of the ray to `6` would belong to
the positive cone of the four equator rays. To see this, if `0` is outside
their convex hull, use a convex combination expressing `0` in the convex
hull after adding `6`; if `0` is inside their convex hull, that positive
cone is already the whole plane. The cone coverage therefore puts the
opposite of ray `06` in a cone spanned by one of `13`, `35`, `54`, `41`.
It follows that `0` lies inside one of the triangles

\[
 613,\quad635,\quad654,\quad641,
\]

contradicting `(V)`. The coefficients are strict because no three points
are collinear. Thus `0` is extreme.

The same argument at `6`, with cap rays `63`,`65` and equator cycle
`3,1,4,5`, proves that `6` is extreme.

### 3.2 A triangle-cover observation

For any triangle `abc` and any point `x`,

\[
 \triangle abc\subseteq
 \triangle xab\ \cup\ \triangle xbc\ \cup\ \triangle xca.
 \tag{F}
\]

For a point of the original triangle, extend the ray from `x` through
that point to its last exit from the triangle; the exit lies on one of
the three boundary edges. This proves `(F)`, whether `x` is inside or
outside the triangle.

### 3.3 An interior equator point would lie in all three pole triangles

Fix an equator point `i` in `{1,3,4,5}`. We claim that every triangle of
the other five points that could contain `i` has the form `06r`.

Four triangles are already excluded by `(V)`. A fifth is excluded by a
curtain side condition: for example, `1` cannot lie inside `034`, because
line `01` would then separate `3` and `4`. The remaining two exclusions
follow from `(F)`. The complete list is:

| Point `i` | Four exclusions from `(V)` | Direct curtain exclusion | First use of `(F)` | Second use of `(F)` |
|---|---|---|---|---|
| `1` | `035,045,356,456` | `034`, using line `01` | `345`, fanned from `0` into `034,035,045` | `346`, fanned from `5` into `345,356,456` |
| `4` | `013,035,136,356` | `015`, using line `04` | `135`, fanned from `0` into `013,015,035` | `156`, fanned from `3` into `135,136,356` |
| `3` | `014,045,146,456` | `156`, using line `36` | `145`, fanned from `6` into `146,156,456` | `015`, fanned from `4` into `014,045,145` |
| `5` | `013,014,136,146` | `346`, using line `56` | `134`, fanned from `6` into `136,146,346` | `034`, fanned from `1` into `013,014,134` |

If `i` is not extreme, it is inside a triangle of other points, hence
inside some `06r`. For any other equator point `s`, fan `06r` from `s`.
The triangles `0rs` and `6rs` are among the seven exclusions just proved.
Consequently `(F)` forces `i` inside `06s`. We have established

\[
 i\text{ not extreme}
 \quad\Longrightarrow\quad
 i\in\operatorname{int}\triangle06r
 \quad\text{for every equator point }r\ne i.
 \tag{P}
\]

### 3.4 The curtain signs exclude an interior equator point

Suppose an equator point `i` is interior. By `(P)`, all four equator
points lie on the same strict side of line `06`. Reflect the plane if
needed so this is the upper side. For each equator point `r`, let

- `a_r` be the angle from ray `06` to ray `0r`, measured into that halfplane;
- `b_r` be the angle from ray `60` to ray `6r`, also measured into that
  halfplane.

Both angles are between `0` and `pi`. The three halfplane tests for a
triangle give

\[
 q\in\operatorname{int}\triangle06r
 \quad\Longleftrightarrow\quad
 a_q<a_r\ \text{ and }\ b_q<b_r,
 \tag{A}
\]

for equator points on this same side of `06`. Thus `i` is the least
equator point in both angular orders.

The four curtain signs say

\[
\begin{aligned}
 &(a_3-a_1)(a_4-a_1)>0,\qquad
 (a_5-a_4)(a_1-a_4)>0,\\
 &(b_1-b_3)(b_5-b_3)>0,\qquad
 (b_4-b_5)(b_3-b_5)>0.
\end{aligned}
\tag{S}
\]

If `i=1`, its minimality and `(S)` give `a_5<a_4` and `b_5<b_4`.
Hence `5` is inside `064`, by `(A)`, so `5` is also interior. Applying
`(P)` to both points would give simultaneously

\[
 1\in\operatorname{int}\triangle065,
 \qquad
 5\in\operatorname{int}\triangle061,
\]

which contradicts `(A)`. The other cases use exactly the following
comparisons:

| Initially interior point | Consequence of its minimality and `(S)` | Forced interior point |
|---|---|---|
| `1` | `a_5<a_4`, `b_5<b_4` | `5` lies inside `064` |
| `4` | `a_3<a_1`, `b_3<b_1` | `3` lies inside `061` |
| `3` | `a_4<a_5`, `b_4<b_5` | `4` lies inside `065` |
| `5` | `a_1<a_3`, `b_1<b_3` | `1` lies inside `063` |

Each case forces the opposite equator partner to be interior and then
contradicts `(P)` and `(A)` in the same way. All four equator points are
therefore extreme. Together with Section 3.1, all six points are extreme.

### 3.5 The two cyclic orders

The disjoint cap triangles admit a strict separating line. Their vertices
therefore occupy two consecutive blocks in the convex hexagon's cyclic
order. Within the block `{0,1,4}`, the middle vertex must be `0`: if it
were `1`, line `04` would put `5` and `1` on opposite sides; if it were
`4`, line `01` would put `3` and `4` on opposite sides. Both alternatives
violate `(C)`. Similarly, `6` must be the middle vertex in the other
block. This gives exactly the two orders `(H)` and proves the planar
lemma.

## 4. Reversal of height order

In either cyclic order `(H)`, the two actual side triangles

\[
 T=035,\qquad U=146
\]

use alternating vertices of the convex hexagon. Their projected
intersection is a convex polygon that meets both base segments `14` and
`35` in nontrivial intervals. For example, both edges from `0` to `3,5`
cross `14`, and both edges from `6` to `1,4` cross `35`; these are the
usual interlacing-diagonal tests in a strictly convex hexagon.

Choose a projected point `p` in the relative interior of `14` and the
interior of the projection of `T`. The lift on `U` lies on the upper
support plane of cap `014`; the lift on `T` lies strictly below it. Thus

\[
 h_T(p)<h_U(p).
\]

Choose similarly `q` in the relative interior of `35` and the interior
of the projection of `U`. Cap `356` gives the opposite inequality,

\[
 h_T(q)>h_U(q).
\]

The two projected triangles are nondegenerate, so their heights are
affine functions on their projections. The segment from `p` to `q`
lies in their common projected region. The height difference changes
sign on this segment and must vanish somewhere. Hence the spatial
triangles `035` and `146` intersect. Their vertex sets are disjoint, so
this contradicts embedding and proves the theorem.

## 5. Weak support is also impossible when the caps are not coplanar

**Corollary.** Under the theorem's embedding and strict-support-at-`2`
hypotheses, suppose the six cap vertices are not all coplanar. Then the
two cap planes cannot both weakly support the seven vertices.

To prove this, choose outward unit normals `n_A,n_B` and offsets `c_A,c_B`
so that all vertices satisfy

\[
 n_A\cdot p\leq c_A,
 \qquad n_B\cdot p\leq c_B,
\]

with equality on the corresponding cap. If `n_A=n_B`, the cap vertices
give both `c_A\leq c_B` and `c_B\leq c_A`; the two planes coincide and
all six cap vertices are coplanar. Thus `n_A\ne n_B`.

Set

\[
 \delta=n_A-n_B,
 \qquad
 \delta\cdot n_A=1-n_A\cdot n_B>0,
 \qquad
 \delta\cdot n_B=n_A\cdot n_B-1<0.
\]

Translate the three vertices of cap `A=014` by `epsilon*delta`, translate
the three vertices of cap `B=356` by `-epsilon*delta`, and leave `2`
fixed. Each cap plane translates with its vertices and keeps its normal.
For the `A` plane, the new offset increases by
`epsilon*(delta dot n_A)`, while the `B` vertices decrease their scalar
products by the same positive amount. The fixed vertex `2` also becomes
strictly below the new `A` plane. The symmetric calculation at `B` gives
strict exposure there as well.

For sufficiently small positive `epsilon`, embedding and strict support
at `2` persist. The translated configuration would contradict the
theorem. This proves the corollary.

In an F1 realization, noncoplanarity of the six cap vertices follows,
for example, from the established strict tetrahedron `0135`. Therefore
at least one of the planes `014` and `356` has vertices strictly on both
sides. This conclusion applies to every F1 cell; it introduces no lower
bound on cap area or nearest-lift margin.

The projective normalization and height-order argument are inspired by
Richard Evan Schwartz, [*Notes on the Pup Tent*, Section 2.3](https://www.math.brown.edu/reschwar/MathNotes/puptent.pdf).
The planar convexity lemma above supplies the additional argument needed
for this ten-triangle subcomplex and is proved here without a
combinatorial enumeration or a solver certificate.
