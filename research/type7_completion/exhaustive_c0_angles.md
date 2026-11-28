# Eighteen angular chambers for the regular C0 limit

This is a small exact topological reduction for the remaining geometric
proof. It assumes that both projected endpoint triangles 123 and 067
are noncollinear, and that the two intermediate heights satisfy
$0<u,v<1/2$. It does not exclude a metric chamber.

The companion exhaustive_c0_angles.py projects the necessary generic
orientation system onto 15 anchor signs. It finds exactly 18 patterns.
It also proves all six additional unanimous non-cap signs. The three
UNSAT formulas were independently accepted by the RUP checker in
0.33 seconds. Exact witnesses below show why the anchor patterns alone
are insufficient, even when both projected caps are noncollinear.

## 1. Why the finite cap-unit cover is necessary

In canonical C0 the normalized point coordinates are

$$
 r_i=(P_i,z_i),\qquad
 z=(0,1/2,1/2,1/2,u,v,0,0),\qquad P_0=P_1=0.
$$

Choose the existing gauge $[0123]>0$. Noncollinearity of the upper
triangle then gives $\operatorname{cross}(P_2,P_3)>0$. Every other
vertex has height strictly below $1/2$, so

$$
 [123j]<0\qquad (j\notin\{1,2,3\}).
$$

The lower triangle 067 is noncollinear and every other vertex has
strictly positive height. Thus all five $[067j]$ have the common
sign of $\operatorname{cross}(P_6,P_7)$.

The producer adds these ten units to the shared ray-1/2 topology,
horizontal-unlinking and nonzero long-ring-linking formula. The case
with negative lower-cap orientation is UNSAT. The positive case
therefore has

$$
 \operatorname{cross}(P_2,P_3)>0,\qquad
 \operatorname{cross}(P_6,P_7)>0.                         \tag{1}
$$

The cap brackets have nonzero limits, so their signs agree with every
sufficiently late member of the original sequence. A sufficiently
small generic perturbation supplies the necessary completion of any
other zero brackets. This justifies using the finite generic formula
without imposing strictness on the remaining actual limit minors.

## 2. The projected variables

For $2\le i<j\le7$,

$$
 [01ij]=\tfrac12\operatorname{cross}(P_i,P_j).
$$

The ordering is

$$
 23,\ 24,\ 25,\ 26,\ 27,\ 34,\ 35,\ 36,\ 37,\ 45,\ 46,\ 47,\ 56,\ 57,\ 67.
$$

The JSON output contains all 18 words in this order. A plus sign means
the corresponding actual cross product is nonnegative; a minus sign
means it is nonpositive. Exact zero values are compatible with either
sign. The checker blocks all 18 projected patterns and proves the
remaining formula UNSAT, rather than relying on a sample of generic
models.

The hypotheses on $u,v$ and both cap areas are essential. At a height
endpoint a proposed cap unit can vanish, and at a collinear cap the
five signs need not agree. Such cases belong to the separate boundary
analysis.

The positive-cap formula has 669 generic sign completions. Its complete
list of unanimous signs outside the ten cap units is

$$
 [0127]\le0,\quad [0135]\le0,\quad [0146]\le0,\quad
 [0234]\ge0,\quad [1567]\le0,\quad [3456]\le0.          \tag{S}
$$

The first three already occur in every anchor pattern. A third CNF
proves all six signs necessary. For every other bracket, the JSON
contains complete Boolean assignments witnessing both signs; every
assignment is checked against every input clause. These SAT witnesses
and the UNSAT certificate establish completeness of the unanimous
sign list without trusting the model enumeration alone.

The three new signs have simple planar forms. Define

$$
 Q_4=P_4-2uP_3-(1-2u)P_6,\qquad
 Q_5=P_5-2vP_3-(1-2v)P_6.
$$

Exact symbolic determinant expansion gives

$$
 2[0234]=\operatorname{cross}(P_3-P_2,(1-2u)P_6+Q_4),
$$

$$
 -2[1567]=\operatorname{cross}(P_7-P_6,2vP_3+Q_5),
 \qquad -2[3456]=\operatorname{cross}(Q_4,Q_5).
$$

All three displayed cross products are therefore nonnegative. The
companion verifies these formulas with symbolic $u,v$ and arbitrary
projected coordinates.

## 3. A strict ray-1 metric inequality

Write $h_i=-X_{i,i+1}$ and $d_i=1/2-h_i$. In the ray-1 limit,

$$
 0\le h_i\le1/2,\qquad d_i\ge0,\qquad
 \sum_i h_i=7/2,\qquad\sum_i d_i=1/2.
$$

The six endpoint-triangle metric identities give

$$
 |P_2|=h_1,\quad |P_7|=h_7,\quad
 L:=|P_3|=d_1+d_2,\quad M:=|P_6|=d_6+d_7.
$$

The cyclic step-three lift and the total deficit imply

$$
 X_{36}=1-h_3-h_4-h_5=-(d_0+L+M).
$$

Consequently

$$
 T_{36}:=|P_6-P_3|^2-X_{36}^2
 \le (L+M)^2-(d_0+L+M)^2\le0.                         \tag{2}
$$

Under the regular-cap hypothesis this inequality is strict. Indeed
$L,M,h_1,h_7>0$. Equality in (2) forces $d_0=0$ and
$P_6=-(M/L)P_3$. The closed C0 cross stress
$T_{01}-T_{02}-T_{17}+T_{27}=0$ also gives

$$
 d_0=h_1h_7+P_2\cdot P_7.
$$

Equality therefore forces $P_7=-(h_7/h_1)P_2$. These two opposite
alignments imply

$$
 \operatorname{cross}(P_6,P_7)
 =-\frac{Mh_7}{Lh_1}\operatorname{cross}(P_2,P_3)<0,
$$

contradicting (1). Thus every regular ray-1 C0 limit satisfies
$T_{36}<0$, including possible half-length edges. The divisions in
this equality argument are justified only by the noncollinear caps;
no conclusion for degenerate caps is asserted here.

A contradiction to this strict inequality using the full necessary
topology would exclude the regular ray-1 C0 case. The 18 anchor
patterns alone do not suffice: Section 5 gives an exact regular
metric witness satisfying the first pattern. Both the cap regularity
and the additional topological signs must be retained.

## 4. An exact obstruction on the closed boundary

At $u=v=1/4$, choose $0<a<1/2$ and put

$$
 h=(1/2,1/2,1/2-a,1/2,1/2,1/2,1/2,a),
$$

$$
 P_i=(p_i,0),\qquad
 p=(0,0,1/2,a,1/2,0,1/2-a,-a).
$$

This family satisfies all 12 closed C0 metric stresses. The verifier
also gives explicit auxiliary values and checks all 24 original
limiting metric equations and all five product syzygies, with no
division or numerical solve. The nearest-lift bounds hold, and every
intrinsic oriented face area is strictly positive for $0<a<1/2$.
Nevertheless,

$$
 T_{36}=2a(2a-1)<0.
$$

Every projected cross product vanishes, so this family satisfies
all 18 angular patterns with their required weak interpretation.
Both projected endpoint caps are collinear. It is therefore a
counterexample to the proposed inequality on the closed metric and
angular relaxation, while it makes no claim about an actual
embedding or about the regular-cap case.

A certificate seeking to exclude regular caps can localize directly
by their area product. For example, proving
$-\operatorname{cross}(P_2,P_3)\operatorname{cross}(P_6,P_7)\ge0$
would contradict (1) and would vanish when either cap is collinear.
It is essential to include more than the anchor patterns in such a
search, as the next example shows.

## 5. An exact regular witness for the anchor relaxation

Again set $u=v=1/4$, and define

$$
 X=41/100,\quad Y=3\sqrt5/25,\quad R=43/200,\quad
 Z=\sqrt{14}/20,\quad L=1/10.
$$

Take the projected points

$$
 (P_0,\ldots,P_7)=
 (0,0,(X,-Y),(L,0),(R,-Z),(-R,-Z),(-L,0),(-X,-Y))
$$

and the horizontal lengths

$$
 h=(89/250,49/100,41/100,457/1000,43/100,
       457/1000,41/100,49/100).
$$

Their sum is $7/2$. The exact checker verifies all nearest-lift bounds,
strict positivity of every intrinsic oriented face area, all 12
closed C0 stresses, and all 29 original limiting metric and syzygy
rows with explicit auxiliary values. Both projected cap areas are

$$
 \operatorname{cross}(P_2,P_3)
 =\operatorname{cross}(P_6,P_7)=3\sqrt5/250>0,
$$

while $T_{36}=-1224/15625<0$. Every other anchor cross product is
strictly negative except $\operatorname{cross}(P_3,P_6)=0$.
Thus this regular metric witness satisfies the weak first pattern
`+-------------+`.

It fails the additional topological requirement in (S):

$$
 [3456]=43\sqrt{14}/4000>0.
$$

The anchor projection loses this constraint. Consequently neither
$T_{36}\ge0$ nor the proposed negative cap-area-product inequality
can follow from the closed metric equations and the 18 anchor
patterns alone, even under the regular-cap assumptions. The
strengthened system including (S) remains a geometric research
target. No actual embedding is asserted for this witness.

## 6. Bounded certificate pilot and its limit

A fixed-parameter discovery test set $u=v=1/4$ and tried three angular
patterns. The degree-two Farkas cone included the 12 exact C0 stresses,
15 signed cross products, all pair products of $h_i$ and $d_i$,
positive gauge products, and coordinate/edge squares. It found no
certificate of $T_{36}\ge0$. Each solve ended in under 0.1 seconds.
Adding the exact linear gauge $p_{3u}=1-h_1-h_2$ and all its linear
multiples also found no certificate for the first pattern.

A bounded follow-up included a full 19-by-19 quadratic
positive-semidefinite Gram matrix for the first pattern. CLARABEL
returned `infeasible_inaccurate` after 0.369 seconds. No certificate
was extracted, and that numerical status gives no geometric
conclusion.

The numerical statuses alone have no geometric implication. The
exact families in Sections 4 and 5 separately prove that the
unlocalized target and its cap-area localization are false on the
anchor-only relaxation. A meaningful next search must retain the
additional necessary signs in (S), or a stronger part of the full
generic topology. Any success would still require exact coefficient
replay, and a fixed-parameter result would not supply a uniform proof
in $u,v$.

## Reproduction

    python research/type7_completion/exhaustive_c0_angles.py /tmp/type7-c0-angles

The three emitted CNFs can be passed to the existing
solver_cnf_certificates.py producer and independent RUP checker.
The metric equations are the closed C0 basis in
solver_remaining_limit.py and its accompanying note.
