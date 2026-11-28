# Conditional signs and quantitative C0 height bounds

For a regular ray-1 C0 limit, the actual mixed brackets satisfy

\[
[2345]\le (v-u)_+\,\operatorname{cross}(P_2,P_3),\qquad
[4567]\le (v-u)_+\,\operatorname{cross}(P_6,P_7),
\tag{1}
\]

where `(v-u)_+=max(v-u,0)`. In particular, an actual positive value of
either mixed bracket requires `v>u`. This is a necessary geometric
bound; it does not by itself exclude the regular C0 component.

The premises are the regular cap orientation cover and the three
strict signs from [the C0 turning proof](exhaustive_c0_turning.md).
Both endpoint cap areas are strictly positive, `0<u,v<1/2`, and

\[
P_0=P_1=0,\qquad z=(0,1/2,1/2,1/2,u,v,0,0).
\]

## 1. Two conditional statements about complete generic signs

The shared necessary topology and linking formula, the ten cap signs,
and the three strict turning signs imply

\[
\begin{aligned}
\chi_{2345}=+&\Longrightarrow
  \chi_{1245}=+,\quad\chi_{1345}=-,\\
\chi_{4567}=+&\Longrightarrow
  \chi_{0456}=+,\quad\chi_{0457}=-.
\end{aligned}
\tag{2}
\]

The companion exports one CNF for each implication, containing the
entire source formula, its positive antecedent, and the negation of
the conjunction of its two conclusions. Independent RUP replay proves
both implications. No projection onto a subset of generic signs is
used, and no optimizer verdict is part of this proof.

The symbols `chi` refer to a sufficiently small generic perturbation.
Every nonzero actual limiting bracket forces its corresponding generic
sign, while an actual zero may have either completion sign. Consequently
an actual `[2345]>0` gives actual `[1245]>=0` and `[1345]<=0` by (2).
The analogous statement holds for actual `[4567]>0`. The conclusions
are weak, so no vanishing actual determinant is discarded.

## 2. Exact height identities

Direct expansion in the C0 coordinates gives

\[
[2345]+[1245]-[1345]
 +(u-v)\operatorname{cross}(P_2,P_3)=0,
\tag{3}
\]

\[
[4567]+[0456]-[0457]
 +(u-v)\operatorname{cross}(P_6,P_7)=0.
\tag{4}
\]

These are affine five-point cocycles with the cap brackets replaced by
their exact height factors. The companion checks both polynomial
identities, as well as

\[
2[0123]=\operatorname{cross}(P_2,P_3),\qquad
2[0167]=\operatorname{cross}(P_6,P_7).
\]

If `[2345]>0`, its two other terms in (3) are nonnegative by (2),
so `[2345]<=(v-u)cross(P2,P3)`. This forces `v>u`. If the actual
bracket is nonpositive, its bound in (1) is immediate. Equation (4)
gives the second bound in exactly the same way. This argument also
retains the equality cases `u=v` and zero mixed brackets.

## 3. A useful pair of oriented vectors when v is above u

For `v>u`, define

\[
E_2=P_3-P_2,\quad E_6=P_7-P_6,\qquad
S_0=(1-2v)P_4-(1-2u)P_5,\quad W_0=vP_4-uP_5.
\]

The exact determinant factors are

\[
\begin{aligned}
[2345]-(v-u)\operatorname{cross}(P_2,P_3)
  &=-\tfrac12\operatorname{cross}(E_2,S_0),\\
[4567]-(v-u)\operatorname{cross}(P_6,P_7)
  &=-\operatorname{cross}(W_0,E_6).
\end{aligned}
\]

Thus (1) supplies the necessary weak orientations

\[
\operatorname{cross}(E_2,S_0)\ge0,\qquad
\operatorname{cross}(W_0,E_6)\ge0.
\tag{5}
\]

These quantitative bounds may be used on the remaining `u<v` half.
On `v<=u`, (1) instead gives both actual mixed brackets nonpositive.
The separate [metric height-order argument](remaining_c0_height_order.md)
contradicts that pair throughout `0<v<=u<1/2`.

## Reproduction

```sh
python research/type7_completion/exhaustive_c0_height_order.py /tmp/c0-height-order
python research/type7_completion/solver_cnf_certificates.py /tmp/c0-height-order-rup \
  --checker /tmp/type7-rup-check /tmp/c0-height-order
python research/type7_completion/solver_cnf_certificates.py /tmp/c0-height-order-rup \
  --checker /tmp/type7-rup-check --replay-only
```

The previously certified cap and turning packages remain premises.
Both new CNFs must have independently accepted proofs before using
(1). The large discovery cone is unnecessary for replay: its fifty
six-term certificates reduced to the two identities (3) and (4).
