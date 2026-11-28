# Positive mixed brackets when one C0 cap is collinear

For a ray-1 C0 limit with collinear upper cap 123 and positively oriented regular lower cap 067, all three upper orders satisfy

\[
[2345]\le0,\qquad[4567]\le0.
\tag{1}
\]

Consequently all three positive-other-cap orders are excluded when `0<v<=u<1/2`, by the existing metric height-order argument. This extends the [earlier boundary package](exhaustive_c0_collinear.md), which had proved the mixed signs only for the order with vertex 1 between 2 and 3.

This note retains the other height order and the negative-other-cap coincidence case as separate problems. It does not assert that every one-collinear C0 limit is excluded.

## 1. Four actual-trit certificates

The source is `exhaustive_c0_collinear.ActualModel`: full necessary topology and linking, both strict height cuts, actual trits with zero-safe generic completions, interpolation, rank clauses, weak Grassmann–Pluecker rules, and 49 exact height relations. The positive lower cap supplies the weak-turn extension already justified in the earlier note:

\[
[2367]>0,\qquad[1267]<0,\qquad[0237]\ge0.
\]

For each of the two remaining upper orders, the companion exports two CNFs:

| Upper order | First implication | Second implication |
|---|---|---|
| `d1=0<d2`, vertex 3 between 1 and 2 | Actual `[2345]<=0` | Actual `[4567]>0` implies the reflected cone and height signs |
| `d1=d2=0`, vertices 1 and 3 coincide | Actual `[2345]<=0` | Actual `[4567]>0` implies the same reflected signs |

The second implication retains fourteen weak actual conclusions: the twelve from the regular positive-cone package and the two height-order signs, transformed by the marked reflection `p(i)=1-i mod8`. Its negation is the disjunction of the actual trit bits with opposite signs. No conclusion is made strict merely because its generic completion is strict.

The third upper order, `d2=0<d1`, already has both conclusions in (1) by the earlier independently checked CNF.

## 2. Reflection of the remaining positive branch

Assume actual `[4567]>0` in one of the two rows above. The two height signs give

\[
[0456]\ge0,\quad[0457]\le0,\quad
[4567]+[0456]-[0457]=(v-u)C_{67}.
\]

Since `C67>0`, this forces `v>u`. Apply the checked marked reflection

\[
u'=1/2-v,\quad v'=1/2-u,\quad d_i'=d_{-i}.
\]

The transformed upper cap is regular with positive orientation, the actual positive branch is now `[2345]>0`, and `0<u'<v'<1/2`. All twelve weak cone conclusions hold by the second CNF. The transformed lower cap has either `d7'=0<d6'` or `d6'=d7'=0`. The reflection and all metric identities are exact on these closed cap boundaries.

Drop primes in the rest of the proof. The regular upper cap has `L>0,C23>0`. Write `M=d6+d7`, `D=d0+L+M`, and use `Q4,Q5,S,W` from the [cone reduction](exhaustive_c0_positive_cones.md). Its exact identity still gives

\[
\operatorname{cross}(E,Q_4)>0.
\tag{2}
\]

## 3. The lower cap has one zero deficit

If `d7=0<M`, the unit-perimeter lower cap is

\[
P_6=M\nu,\quad P_7=\nu/2,\quad F=(1/2-M)\nu.
\]

The strict turn gives `cross(E,P6)>0`. If `C36<0`, put

\[
R=\frac{h_2(-C_{36})}{\operatorname{cross}(E,P_6)}.
\]

This is exactly the `beta=0` endpoint in the [support-bound proof](exhaustive_c0_endpoint_bound.md). That proof uses only the regular upper triangle to give

\[
D=M+\mathcal F(R)>\min(R,1/2).
\]

Since `D<=1/2`, necessarily `R<D`. The cone proof then contradicts the exact radius `|Q4|=d4+d5+2uD`, just as in the regular case. No lower-cap regularity is needed in this argument. If `C36=0`, its zero-safe line argument gives `|Q4|<=2uL<2uD`, because `M>0`. Thus this boundary cannot support the positive branch.

## 4. The lower base collapses

Now `d6=d7=0`, hence `M=0` and `P6=0`. The reflected conditional signs give both `C34<=0` and `[1346]<=0`. Since `2[1346]=-C34` here, they force `P4` onto the line of `P3`. Write `P4=a P3`.

The two signs `[0234]>=0` and `[1246]<=0`, with `C23>0`, give

\[
0\le a\le2u,\qquad |Q_4|=(2u-a)L\le2uL.
\tag{3}
\]

But the exact metric radius is

\[
|Q_4|=d_4+d_5+2u(d_0+L)\ge2uL.
\]

Therefore equality is forced: `a=0` and `d0=d4=d5=0`. The deficit budget gives `d3=1/2-L`, and the other radius is

\[
s=|Q_5|=1/2-2vL>0,\qquad Q_4=-2uP_3.
\]

The exact dot identity `Q4 dot Q5=-|Q4||Q5|+d4` now gives `P3 dot Q5=L s`. Equality in Cauchy–Schwarz forces `Q5=(s/L)P3`. Consequently

\[
S=\ell_vQ_4-\ell_uQ_5
=-\left(2u\ell_v+\ell_u s/L\right)P_3,
\]

and the coefficient is strictly positive. Since `cross(E,P3)=-C23<0`, the exact bracket identity yields

\[
[2345]=-\tfrac12\operatorname{cross}(E,S)<0,
\]

contradicting the actual positive antecedent. This deals explicitly with the equality case that a strict radius estimate alone would miss.

## 5. Height-order consequence and scope

Combining the four new CNFs, the two metric endpoint arguments, and the earlier third-order CNF proves (1) for every collinear upper-cap order with positive regular lower cap.

For `u>=v`, the metric height-order proof now applies to all three orders. Its positive slack is `d0+d1+d7>0`, because the lower cap is regular. Its denominators `h2,h6` remain positive, and its norm and cosine factorizations allow `d1=0`, `d2=0`, or both. The weak-turn extension has upper angle `A=0` and still gives `0<B+phi<pi`. The same clockwise-path contradiction therefore excludes all three orders.

The marked reflection transfers this statement to the corresponding cases with regular upper cap and collinear lower cap, with the orientation fixed by the checked transformation. The negative-other-cap coincidence case and the `v>u` both-nonpositive region are not removed by this note.

## Reproduction

```sh
python research/type7_completion/exhaustive_c0_collinear_positive.py /tmp/c0-collinear-positive
python research/type7_completion/solver_cnf_certificates.py /tmp/c0-collinear-positive-rup \
  --checker /tmp/type7-rup-check /tmp/c0-collinear-positive
```

The producer replays the endpoint/source bindings and checks the exact collapsed-base metric identities. All four generated actual-trit CNFs require independent RUP acceptance.
