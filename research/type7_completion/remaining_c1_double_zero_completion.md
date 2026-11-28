# Completing the interior EF and endpoint-EE exclusions

This package excludes every scalar EF and endpoint-EE family left by
the [earlier double-zero exclusions](remaining_c1_double_zero_endpoints.md).
It uses the original normal determinants, two independently normalized
shrinking cap edges, and exact positive polynomial identities. The
proof covers complete open parameter boxes and all relative collapse
rates; it makes no sample-point assumption.

The companion verifies 39 polynomial identities from the adjacent
JSON data and exports 80 independently replayable UNSAT formulas.
Together with the earlier endpoint package, these exclude all EF
families and both EE endpoints. The [same-zero proof](remaining_c1_same_zero.md)
already excludes the open EE interval.

## 1. Complete scalar cover

Use `a=alpha`, `b=beta`, with `0<a,b<1`, and the exact families from
the [double-zero common-line reduction](remaining_c1_zero_common.md).
For EF, orient `U=P4-P3=1/2` and write

\[
\begin{aligned}
h&=(\tfrac12,\tfrac12,0,\tfrac12,\tfrac12-r,r,\tfrac12,0),\\
P_0=P_1=P_7&=0,\qquad P_2=P_3=\frac{\eta}{2a},\qquad
P_4=P_3+\tfrac12,\\
P_6&=\epsilon/2,\qquad
P_5=bP_3+(1-b)\epsilon/2+r.
\end{aligned}                                                     \tag{1}
\]

Here `eta,epsilon` independently equal +1 or -1. If `epsilon=+1`,
the circle identity forces `r=b/2`; if `epsilon=-1`, the whole
closed interval `0<=r<=1/2` remains. The earlier package excludes
`eta=-1,epsilon=+1`.

This package treats both eta choices with `epsilon=-1`, each split
into `r=0`, `0<r<1/2`, and `r=1/2`, and the remaining
`eta=+1,epsilon=+1` family. Thus it covers seven EF scalar strata.

At the left EE endpoint, orient `P6=P7=1/2`. The remaining opposite
upper direction gives

\[
\begin{aligned}
h&=(0,\tfrac12,0,\tfrac12,\tfrac12,\tfrac12,0,\tfrac12),\\
P&=(0,0,\tfrac12,\tfrac12,0,1-b/2,\tfrac12,\tfrac12).
\end{aligned}                                                     \tag{2}
\]

This is the eighth stratum. Section 5 maps the other opposite-direction
EE endpoint to (2). The two equal-direction EE endpoints are already
excluded by the earlier package. The companion checks the total weight
and all twelve closed projected stresses of the original metric source
for each specialized stratum.

## 2. Necessary macro zeros

Every P3 in (1), (2) is nonzero. Use the same finite axis choice and
positive normal-width stretch as in the
[single-zero scalar proof](remaining_c1_single_zero_scalar.md). The
limiting normal coordinates satisfy

\[
N_0=N_1=N_3=0,\qquad
\max_{i\in\{2,4,5,6,7\}}|N_i|=1.
\]

The exact positive-determinant scalar shear gives

\[
\begin{aligned}
x_{\rm EF}&=(0,-\eta,0,0,1,(1-b)\epsilon+2r,\epsilon,0),\\
x_{\rm EE}&=(0,0,1,1,0,2-b,1,1),
\end{aligned}
\]

and heights `z=(0,a,1,1,1,b,0,0)`. All seventy macro determinant
forms and all 560 projected identities are expanded from these
coordinates through the established source checker. Original actual
zeros leave their generic signs free.

One exported macro implication for each of the eight strata proves

\[
\begin{array}{ll}
\text{EF:}&N_2=N_7=0,\\
\text{EE:}&N_2=0,\quad D_{0167}=0.
\end{array}                                                       \tag{3}
\]

Here D is an actual macro determinant. For EE, its exact source row is

\[
D_{0167}=a(N_7-N_6).
\]

Since a>0, this proves the numerical equality `N7=N6`; mere agreement
of their signs would not suffice. The macro formula adds the disjunction
that one of the stated zeros fails, so its independently checked UNSAT
certificate proves both conditions simultaneously.

After (3), at least one of `N4,N5,N6` is nonzero. These three normals
are the only macro variables in the remaining polynomial identities.

## 3. Independent normalization of both short edges

The upper short edge is 23. The lower short edge is 07 for EF and
67 for EE. Both are covered by the
[relative short-edge lemma](remaining_c1_short_edges.md), including
its marked-symmetry transfer to the original bounded chart.

For either edge with physical horizontal length h, the transverse
edge divided by h has asymptotic unit length and its normalized axial
difference is `O(t h)`, with `t=1/y^2`. Once (3) holds, its edge in
the macro normal-stretched chart tends to zero. Normalize that edge
independently by `2h` when its stretched normal difference divided by
h is bounded; otherwise normalize by the magnitude of that difference.
The possible limiting directions are exactly

\[
(H,D,0),\qquad H\in\{-1,0,1\},\quad D\ne0
\ \text{if }H=0.                                 \tag{4}
\]

This is the same scale argument as in the earlier one-edge proof.
For bounded ratio, the physical normal component divided by h tends
to zero with the macro normal width, so the unit norm gives H=±1.
For unbounded ratio, H=0 and the normal component is nonzero. The
axial term vanishes because each normalization is at least a fixed
multiple of h. Passing to subsequences for both edges gives all nine
independent pairs `(H23,Hlower)` in {-1,0,1} squared.

Use the conventions

\[
r_2=r_3-e_p(H_{23},D_2,tq_2),\qquad
r_7=r_l+e_q(H_{\rm lower},D_7,tq_7),               \tag{5}
\]

where l=0 for EF and l=6 for EE. Both positive normalizing lengths
`ep,eq` tend to zero, independently. The q variables remain bounded.
The checker first expands each original determinant in (5), factors
ep if it contains 23, factors eq if it contains l7, and factors their
product if it contains both. It checks polynomial divisibility before
taking any limit. It then checks the factor t on the axial correction
and takes `t,ep,eq` to zero.

There are 29 such determinant forms: fifteen per edge, with one
shared determinant divided by the product. Each resulting form is
linear in

\[
(N_4,N_5,N_6,D_2,D_7).
\]

A nonzero divided limit binds to the same original generic sign as
its undivided determinant. The complete Boolean source keeps the
original generic embedding/linking constraints, both strict axial
cuts, all macro actual-zero possibilities, and only the individually
valid virtual coefficient-sign constraints. No affine identity is
asserted between determinants at different scales.

## 4. Exact positive polynomial identities

The remaining sign relaxation admits Boolean assignments that cannot
come from the linear determinant forms with their actual coefficients.
The adjacent JSON supplies exact polynomial identities that exclude
these assignments uniformly.

Let F_j be either a macro determinant or one of the 29 divided forms,
and let chi_j be its required original generic sign. Because actual
zero forms are permitted, the necessary statement is

\[
\chi_jF_j\ge0.
\]

Every certificate has the form

\[
\sum_{j,m}c_{jm}b_{d,m}(u)\,\chi_jF_j
+C(u)\,\sigma N_i=0,                              \tag{6}
\]

where `i in {4,5,6}`, `sigma in {-1,+1}`, and

\[
b_{d,k}(u)=\prod_\nu u_\nu^{k_\nu}(1-u_\nu)^{d-k_\nu},
\qquad 0\le k_\nu\le d.
\]

The unit parameters are a,b and, only on the open-r strata, 2r.
Thus every factor in every displayed basis product is strictly
positive. All `c_jm` are positive integers. The polynomial C is a
nonempty positive-integer combination of the same products at degree
d+1, so C is strictly positive as well. The source degrees are one
or two; no parameter subdivision or numerical estimate is used.

If all the generic signs in (6) hold and `sigma N_i>0`, the left
side is strictly positive, a contradiction. Therefore (6) gives a
necessary clause forbidding those generic signs together with that
strict normal trit. This argument remains valid when any number of
the determinant forms vanish.

The verifier rebuilds every F from the original coordinate source.
It rebuilds each basis product from its integer exponent tuple and
the known open unit parameters, and checks every stored coefficient
is a positive integer. It then verifies the zero polynomial in each
of the five normal-variable columns, using exact rational arithmetic.
It also requires at least one positive target term. No expanded
polynomial string, numerical linear-programming output, or proposed
Boolean clause is accepted as a source of truth; the clause is
constructed from the verified original bracket guards and target trit.

There are 39 identities across thirteen direction pairs, with 989
positive integer basis terms in total. The other 59 pairs close in
the necessary sign system without additional polynomial clauses.
All 72 virtual formulas require independent RUP replay, which also
verifies that the finite collection of guarded identities covers every
remaining Boolean assignment. Together with the eight macro implications,
this gives 80 independent obligations.

## 5. Opposite-direction EE endpoint symmetry

At the right EE endpoint `h0=1/2`, let the upper direction be
`epsilon=-1`, and use the original scalar coordinates from the
common-line source. The marked cap swap `i -> i+4` sends its heights
to `a'=1-b`, `b'=1-a`. Reanchor the actual long edge 45. Its limiting
normalized axial length is `(1-b)/2>0`, and its scalar slope is

\[
\lambda=\frac{P_5-P_4}{z_5-z_4}=-\frac{1+a}{a},
\qquad z=(0,a/2,1/2,1/2,1/2,b/2,0,0).
\]

The new scalar coordinates are

\[
P'_i=-\epsilon\bigl(P_{i+4}-P_4
                    -\lambda(z_{i+4}-z_4)\bigr).
\]

The companion checks all eight scalar-coordinate, eight height, and
eight weight identities against the left endpoint (2) with
`(a',b')=(1-b,1-a)`. It also checks that the permutation is one of
the marked symmetries for the remaining marking. Thus the right
opposite-direction endpoint maps to the excluded left endpoint.

The finite long-axis reanchoring and scalar-axis choice precede a
fresh normal-width normalization in the new chart. No comparison
between the old and new normal widths, or between either width and
a short-edge length, is assumed.

## 6. Replay and complete scope

```sh
python research/type7_completion/remaining_c1_double_zero_completion.py /tmp/type7-c1-double-complete
python research/type7_completion/solver_cnf_certificates.py /tmp/type7-c1-double-complete-rup \
  --checker /tmp/type7-rup-check /tmp/type7-c1-double-complete
```

The checker reads `remaining_c1_double_zero_completion.json` beside
its source. The data contains only integer exponents, positive integer
coefficients, source determinant references, signs, and target normals.
The producer uses exact SymPy polynomial arithmetic and Boolean SAT;
it does not call a numerical optimizer or an arithmetic SMT solver.

This completes EF and both EE endpoints when combined with the
earlier double-zero endpoint package. The open EE interval, all other
zero-edge orders, and the strict-positive-edge stratum have their
separate certificates. The present argument concerns interior a,b;
height endpoints require their separate boundary proofs.
