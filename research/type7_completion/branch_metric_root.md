# Removing the spatial root from every original K4 branch

`branch_metric_root.py` removes the last spatial variable from the
[Gram reconstruction](branch_gram_chart.py), while preserving the original
268 branch IDs for each marking. At a fixed height the resulting formula
has fourteen intrinsic real variables. With the whole height tail retained,
it has those fourteen variables and `t`, with `0<t<=1/Y²`.

This is an exact projection of a necessary system. It is **not a proof
that any branch is infeasible**, and it introduces no new geometric branch
classification. The prior common sign cover, strictness certificates, and
Gram reconstruction remain required premises.

## 1. The K4 signs select one root

Let the ordered anchor be `(a0,a1,a2,a3)` and let `b0` be the first leaf,
opposite `a0` in the graph. Write `G` for the positive definite anchor
Gram matrix, `H=adj(G)`, and `g=det(G)>0`. The unknown squared distance
`z=|a0-b0|²` occurs in the inner-product vector as

\[
U(z)=u_0+\tfrac z2\mathbf 1.
\]

Its norm equation is

\[
F(z)=U(z)^THU(z)-gz=Az^2+Bz+C=0,
\]

where

\[
A=\tfrac14\mathbf1^TH\mathbf1>0,\qquad
B=\mathbf1^THu_0-g,\qquad C=u_0^THu_0.
\]

The strict sign of `A` follows because `H=gG^{-1}` is positive definite.
The barycentric coordinate of `b0` opposite `a0` is

\[
\lambda_0=1-\mathbf1^THU(z)/g.
\]

Consequently the exact derivative identity is

\[
F'(z)=2Az+B=\mathbf1^THU(z)-g=-g\lambda_0.       \tag{1}
\]

Both the anchor and `(b0,a1,a2,a3)` are graph K4s. Their determinants
are nonzero, and affine multilinearity gives

\[
\lambda_0=
\frac{[b_0a_1a_2a_3]}{[a_0a_1a_2a_3]}.
\]

The branch's sixteen strict K4 signs therefore determine

\[
\sigma=\operatorname{sgn}F'(z)
=-\operatorname{sgn}[b_0a_1a_2a_3]\,
   \operatorname{sgn}[a_0a_1a_2a_3]\in\{-1,1\}.   \tag{2}
\]

The implementation obtains each ordered sign from the existing sorted
K4 sign and the permutation parity. It does not choose a root numerically.
Since

\[
(2Az+B)^2-(B^2-4AC)=4AF(z),
\]

the discriminant `Delta=B²-4AC` is strictly positive at every admissible
seed. The selected root is precisely

\[
z_\sigma=\frac{-B+\sigma\sqrt{\Delta}}{2A}.       \tag{3}
\]

## 2. One sign lemma, including every zero case

The Gram algebra represents each expression as

\[
\frac{b+az}{A^e},\qquad e\ge0.
\]

Its denominator is positive. Define polynomial quantities

\[
K=2Ab-aB,\qquad T=\sigma a,\qquad
R=4A(Ab^2-Bab+Ca^2).
\]

They satisfy the exact identities

\[
2A(b+az_\sigma)=K+T\sqrt\Delta,
\qquad R=K^2-a^2\Delta=K^2-T^2\Delta.           \tag{4}
\]

For `A>0` and `Delta>0`, the following Boolean polynomial conditions are
equivalent to the indicated signs:

\[
\begin{aligned}
b+az_\sigma>0\quad\Longleftrightarrow\quad&
\bigl(K>0\ \land\ (T\ge0\ \lor\ R>0)\bigr)\\
&\lor\ \bigl(T>0\ \land\ R<0\bigr),              \tag{5}\\[2mm]
b+az_\sigma\ge0\quad\Longleftrightarrow\quad&
\bigl(K\ge0\ \land\ (T\ge0\ \lor\ R\ge0)\bigr)\\
&\lor\ \bigl(T>0\ \land\ R\le0\bigr),           \tag{6}\\[2mm]
b+az_\sigma=0\quad\Longleftrightarrow\quad&
R=0\ \land\ KT\le0.                            \tag{7}
\end{aligned}
\]

To prove these formulas, put `S=T sqrt(Delta)`, so `S` and `T` have
the same sign. The factorization

\[
R=(K+S)(K-S)
\]

settles the only nontrivial possibilities. If `K>0>S`, then `K-S>0`
and `sign(K+S)=sign(R)`. If `K<0<S`, then `K-S<0` and
`sign(K+S)=-sign(R)`. Equal signs and zero axes are immediate. These
possibilities exhaust all real inputs. In particular, (7) includes
`K=T=0` and opposite-sign cancellation; no minor is assumed nonzero
unless the source already proves it.

The checker verifies the polynomial identities and all seventeen
feasible sign regimes of `(K,T,R)`. This is a symbolic sign-table check,
not sampling of values or a solver verdict. Negative comparisons apply
(5) or (6) to the negative expression; disequality negates (7).

The expression for `R` uses the quadratic-linear resultant. In emitted
sign tests the producer omits the positive factor `4A`, using
`Ab²-Bab+Ca²` directly. It also replaces `KT<=0` by
`(K>=0 and T<=0) or (K<=0 and T>=0)`. Both changes preserve every zero
case and reduce polynomial degree; neither establishes a solver speedup.
No radical appears in the generated formula.

## 3. Whole-query projection

The producer first generates the complete original Gram branch, including
its actual affine circuits. It then interprets every real definition in
the same exact quadratic algebra. For each atomic comparison it
subtracts the right side, discards only the positive power of `A`, and
applies (5), (6), or (7).

All original Boolean connectives, decision-diagram definitions, and
assertions are retained. This includes the overlapping weak sign tests
for actual zero minors, the propagation-denominator disequalities, every
retained actual circuit, all six metric residuals, and the nonedge
contraction comparisons. `A>0` and `Delta>0` are recorded explicitly.
The variable `zseed` is absent from the output.

Arithmetic definitions are emitted only when they are reachable from a
retained comparison or Boolean definition. This removes unused construction
nodes without dropping an assertion or changing its polynomial value.

For any admissible original assignment, (1)–(3) identify its root and
the replacement preserves every atomic truth value. Conversely, an
assignment satisfying the projected formula has the real root (3);
substituting it into the original definitions restores all original
assertions. This proves equivalence to the selected-root Gram formula.
The original K4 assertions already force that selection, so the rewrite
does not remove a second admissible mirror.

This argument is uniform in every intrinsic coordinate and positive
`t` in the retained height interval. No `t=0` specialization, positive
edge-size threshold, or further geometric case split is used.

## Reproduction

```sh
# Universal algebraic identities and the complete sign table:
python research/type7_completion/branch_metric_root.py

# One original branch, retaining the whole height tail:
python research/type7_completion/branch_metric_root.py \
  /tmp/type7-536-ray2/axis_chambers.json /tmp/type7-root-projection \
  --mark 2 --y 32 --all-heights --branch 0
```

Omit `--branch` to emit all 268 unchanged branch IDs for the selected
marking. Each output manifest binds the source manifest and complete
Gram query by SHA-256 and records the selected K4 root. Neither query
generation nor these identity checks decide polynomial feasibility.
