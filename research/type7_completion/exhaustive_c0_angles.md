# Eighteen angular chambers for the regular C0 limit

This is a small exact topological target for the remaining geometric
proof. It assumes that both projected endpoint triangles 123 and 067
are noncollinear, and that the two intermediate heights satisfy
$0<u,v<1/2$. It does not exclude a metric chamber.

The companion exhaustive_c0_angles.py projects the necessary generic
orientation system onto 15 anchor signs. It finds exactly 18 patterns.
The opposite-cap-orientation formula and the complete projection
coverage formula were independently accepted by the RUP checker.
Independent certificate production and RUP replay of these two CNFs
took 0.366 seconds in the shared workspace.

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

A proof that the metric equations and each angular chamber imply
$T_{36}\ge0$ would therefore exclude the entire regular ray-1 C0
case. That opposite inequality remains a research target.

## 4. Bounded certificate pilot and its limit

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

These are failures of the particular discovery searches. They supply
neither a feasible metric witness nor evidence that the target
inequality is false. A possible next step is a higher-degree identity
localized by a strictly positive cap area. Any success would still
require exact coefficient replay, and a fixed-parameter result would
not supply a uniform proof in $u,v$.

## Reproduction

    python research/type7_completion/exhaustive_c0_angles.py /tmp/type7-c0-angles

The two emitted CNFs can be passed to the existing
solver_cnf_certificates.py producer and independent RUP checker.
The metric equations are the closed C0 basis in
solver_remaining_limit.py and its accompanying note.
