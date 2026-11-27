# Exact finite product certificates for chambers 28 and 36

The stored certificates exclude the complete weak metric systems for
canonical phase chambers **28 and 36**, for every **\(y\ge32\)**.  This
includes the target \(y=10^6\).  They use the same exact symmetries,
proved nonzero brackets, and raw metric comparison as the chamber
compiler.  No lower bound for an edge or bracket magnitude is imposed.

The verifier uses integer arithmetic for every cancellation.  Numerical
linear programming and an SMT search were used only to discover the
small certificates; neither is imported or trusted by the replay.
These two chamber exclusions are not a full Type 7 marking exclusion.

## Necessary product and maximum comparisons

Let \(B_q\ge0\) be the magnitude of a **raw affine four-point bracket**,
all expressed in one common coordinate frame.  Their weak signs are the
selected generic completion.  The compiler proves a subset strictly
positive by its cofactor and Grassmann–Plücker propagation.  Every use
of strictness below is checked against that set.

For \(B_q>0\), put \(\ell_q=\log_2 B_q\).  If a weak bracket is zero,
assign its auxiliary \(\ell_q\) any finite value.  The following
necessary formulas remain valid because every left-hand magnitude is
strictly positive and a maximizing right-hand term is then positive.

### 1. Grassmann–Plücker products

Every signed three-term identity has one product equal to the sum of
the other two nonnegative products.  For either smaller product,

\[
B_aB_b\le B_cB_d,
\qquad \ell_a+\ell_b-\ell_c-\ell_d\le0.
\]

The verifier checks the ordered bracket signs, the chosen dominant
product, and strict positivity of all four factors appearing in this
comparison.  The unused product may vanish.  All comparisons are weak;
the proof does not need a strict logarithmic inequality.

### 2. Relative metric comparisons

The already proved relative raw-bracket comparison gives

\[
B_a+B_b\le \frac{8}{y^2}(B_c+B_d)
\]

when the relevant pair has opposite weak signs.  Let \(B_r\) be a
maximizer of \(B_c,B_d\).  Every proved-positive left term then obeys

\[
B_l\le\frac{16}{y^2}B_r\le2^{-5}B_r
\quad(y\ge32),
\qquad \ell_l-\ell_r\le-5.
\]

The same maximizing right term works for both left terms.  Accordingly
this is a disjunction of two alternatives, each containing the bounds
for every proved-positive left term.  A zero right term cannot be the
chosen maximum.  The verifier reconstructs each source comparison from
the exact phase-preserving marked symmetry and its cap pair.

### 3. Affine five-point cocycles

The exact alternating sum of the five raw four-brackets is zero.  After
using the chamber's weak signs, the positive-side magnitudes sum to the
negative-side magnitudes.  For any proved-positive left term,

\[
B_l\le\sum_{r\in R}B_r
\le 2^{\lceil\log_2|R|\rceil}\max_{r\in R}B_r.
\]

Here \(R\) consists of all terms on the opposite side, and
\(1\le|R|\le4\).  Thus the necessary disjunction contains the alternatives

\[
\ell_l-\ell_r\le\lceil\log_2|R|\rceil,
\qquad r\in R.
\]

The constants are exactly 0, 1, or 2.  Again, some maximizing right term
is positive, so auxiliary values assigned to zero brackets do not
invalidate necessity.  No sum is replaced by a selected term without
including every possible maximizer.

## Exhaustive finite certificates

Each stored rule has one or more alternatives, and each alternative is
a conjunction of linear inequalities in the auxiliary logarithms.  All
single-alternative rules are available at the root.  Each internal
node of the certificate tree chooses an unused rule and includes
**every** alternative as a child.  A leaf uses only inequalities already
available along its path.

At every leaf, the verifier reconstructs a positive integer combination
of those inequalities.  The coefficient of each of the 70 variables
cancels exactly, while the right-hand constants sum to a strictly
negative integer.  This would require \(0<0\), a contradiction.  In
multiplicative form, it requires a positive product to be at most a
strictly smaller fixed multiple of itself.  No logarithm is evaluated
numerically.

| Chamber | Necessary rules | Tree nodes | Contradictory leaves |
| --- | ---: | ---: | ---: |
| 28 | 23 | 173 | 121 |
| 36 | 32 | 53 | 30 |

The verifier checks each rule's mathematical source, each tree split,
the availability of every referenced inequality, positivity and
integrality of every multiplier, exact cancellation, and the negative
constant.  The saved file contains only source labels and integer
certificates; it does not contain trusted solver statuses.

Run the standalone replay with:

```bash
python research/type7_completion/solver_metric_products.py
```

`verify(model, strict, symmetries)` is also available to the chamber
compiler and its independent manifest replay.  Strictness and symmetry
proofs retain the geometric premises documented in `geometric_audit.md`
and `solver_compilation.md`; the uniform raw comparison is established
in `solver_metric_certificates.md`.
