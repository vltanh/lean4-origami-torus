# Every unbounded ray-3 sequence has at least three vanishing short edges

**Theorem.** Along any sequence of actual canonical ray-3 realizations
with `y -> infinity`, the third-smallest of the eight positive short-edge
weights tends to zero:

\[
 h_{(3)}\longrightarrow0,
\qquad h_e=-X_e>0.
\]

Here `h_(1)<=...<=h_(8)` are the weights in increasing order.
Equivalently, no such unbounded sequence can keep six weights
bounded below by one positive number. The proof includes all possible
rates of transverse flattening. It uses the geometric necessity audit
and the preceding exact cap and blow-up certificates.

This theorem still does not exclude an unbounded sequence whose edges
shrink, provide a numerical height threshold, or close the full marking.
Its purpose is to identify the remaining boundary precisely. Sections
1–4 first prove `h_(1)->0`; sections 5 and 6 rule out exactly one or
two zero weights in a limiting configuration.

## 1. A bounded transverse blow-up must exist

Suppose instead that an unbounded subsequence has `h_e>=epsilon>0`
for every short edge. The uniform relative bounds make the transverse
coordinates bounded. Pass to a convergent subsequence. The exhaustive
cap proofs in `ROADMAP.md` imply that both cap limits lie on one common
line. Every limiting physical edge length equals its positive weight.

Use a verified phase-preserving marked symmetry and the longitudinal
axis `02`. Rotate the transverse plane so that `P1-P0` is positive
horizontal. The anchors satisfy `P0=P2=0`, and `|P1|` has a positive
limit. Write transverse coordinates `(X,Y)`, with the limiting common
line `Y=0`, and put `delta=max_i |Y_i|`.

For every actual placement `delta>0`. Otherwise all spatial vertices
would lie in the plane spanned by the longitudinal axis and the one
transverse line, contradicting the nonzero K4 bracket `0123`. Also
`delta -> 0`. The stretched points `(X_i,Y_i/delta)` are bounded, so
pass to a further convergent subsequence. At least one limiting Y
coordinate has magnitude one.

Normalized axial coordinates still converge to levels zero and one.
Since stretching does not decrease transverse norms, the relative axial
increment divided by any stretched edge norm is `O(1/y²)`. Thus the
necessary weak point and direction signs remain valid after stretching.
Every limiting horizontal edge difference remains nonzero under the
assumed positive weight bound.

The two stretched caps cannot both lie on the horizontal line: `P1`
fixes the A line horizontally, while some stretched Y coordinate is
nonzero. There are exactly three possibilities below.

## 2. Both stretched caps are noncollinear

The complete weak direction-order classification leaves aligned
trapezoids or the two V/V alignments. The V/V alignments contradict the
32 fixed point signs in `exhaustive_vv_geometry.md`, independently of
any metric.

If the common trapezoid bases have zero physical X component, their
weights are zero, already contradicting the assumed positive weights.
Otherwise the limiting metric is the seminorm `|dX|`, and the exact
stress equation is the quadratic `F0=0` of `common_line_trapezoids.md`.
All four bases have positive X lengths under the present assumption.
The complete zero-cone check permits at most two positive bases at a
zero. This is a contradiction.

## 3. Exactly one stretched cap is noncollinear

The positive weights make the other cap's line nonvertical. A shear
of the stretched Y coordinate makes that line horizontal without
changing the physical length seminorm `|dX|`.

The exhaustive degenerate-norm cover in `remaining_flat_blowup.md`
leaves exactly 24 cells with all eight weights positive. Checked marked
symmetries put all of them in its one-flat/one-trapezoid family. Its
uniform analytic proof combines an exact positive bracket combination
with a strictly negative cubic metric correction. Both terms have the
same sign for every ratio of the width to `1/y` or `1/y²`. It excludes
all 24 cells, a contradiction.

## 4. Both stretched caps are collinear on different lines

The A line is horizontal because it contains the nonzero horizontal
point P1. The B line is different, since otherwise every stretched Y
coordinate would be zero. It cannot be vertical: all its original X
edge differences are nonzero by assumption. Both lines pass through
their transverse anchors at zero.

Parametrize each line by its physical X coordinate. For two A vertices
and two B vertices, the nonzero limiting bracket sign is, up to the
fixed relabeling parity and one common orientation,

\[
-\operatorname{sgn}(a_j-a_i)\operatorname{sgn}(b_l-b_k).
\]

All other limiting brackets are zero and impose no sign. There are
74 nonconstant weak orders of four labelled scalar points per cap,
including every vertex coincidence. The finite verifier checks all
5,476 pairs against the complete 1,888 generic sign models and their
global reversals. Exactly 1,336 pairs pass.

The physical edge cost and dot product in this limit are
`h_i=|Delta a_i|`, `k_j=|Delta b_j|`, and
`e_i dot f_j=Delta a_i*Delta b_j`. Thus the homogeneous stress expression
is the `cos(theta)=+1` endpoint from `exhaustive_collinear_caps.py`.
Write every scalar displacement in terms of the strictly positive gaps
of its weak order. The exact stress polynomial is bilinear in the two
sets of gaps.

For 712 pairs all its coefficients have one weak sign with a nonzero
coefficient. Every gap product is positive, so the stress is strictly
nonzero, a contradiction. For the remaining 624 pairs the polynomial
vanishes identically. **Every one has two consecutive vertices of at
least one cap coincident in X.** That gives a zero short-edge weight,
contradicting the assumption in this case too.

All three stretched-limit possibilities are impossible. This proves
the first reduction. If the minimum weight failed to tend to zero in the original
sequence, it would have a subsequence with a common positive lower bound,
which the proof has just excluded.

## 5. Exactly one vanishing weight is also impossible

Suppose that the second-smallest weight is bounded below by epsilon
on an unbounded subsequence. Compactness and the first reduction give
a limiting configuration with exactly one zero weight. Pass to a
subsequence and use a verified phase symmetry to put a longest edge
at 01. Its weight is at least `1/4`, so the same construction fixes the
A line horizontally and gives a bounded nontrivial transverse blow-up.
This geometric normalization is separate from choosing a finite sign
representative; it imposes no additional restriction on that compiler.

There are again three possibilities:

- If both stretched caps are noncollinear, the zero-cone classification
  forces three physically coincident vertices in each cap. That gives
  at least four zero short weights, contradicting the hypothesis.
- If exactly one stretched cap is noncollinear, the complete mixed
  cover has exactly eighty cells with one zero physical weight. The
  [adjacent-collapse proof](remaining_adjacent_blowup.md) excludes the
  48 cells whose zero edge belongs to the collinear cap. The
  [partner-collapse proof](remaining_partner_blowup.md) excludes the
  other 32 cells using a signed length defect, a uniformly nonsingular
  modified metric Jacobian, and strictly negative volume coefficients.
- If both stretched caps are collinear, their lines are different and
  neither is vertical, since at least three physical edge weights in
  each cap are positive. Exactly sixteen of the 624 zero-stress order
  pairs have one zero short weight. The
  [two-line proof](remaining_two_line_blowup.md) excludes all sixteen by
  virtual-edge signs and a strictly signed moving-frame height.

These finite covers include every point coincidence allowed by their
weight counts. Their proofs normalize a collapsing edge before taking
limits or regularize its squared metric equation by a signed defect.
They impose no relative rate on that edge, the transverse width, and t.
Every possibility is excluded, proving `h_(2)->0`.

## 6. Exactly two vanishing weights are also impossible

Suppose instead that `h_(3)>=epsilon` on an unbounded subsequence.
The preceding theorem and compactness give exactly two zero weights
in the physical limit. Normalize a longest edge to 01 and form the
same bounded, nontrivial transverse blow-up. Each cap has perimeter
one and every edge weight is at most one half, so each cap retains at
least two positive weights. In particular, every collinear stretched
cap has a nonvertical line.

Two noncollinear stretched caps again require at least four zero
weights, which is impossible here. The two other cases have complete
finite covers:

| Stretched caps | Two-zero family | Cells or orders | Exclusion |
|---|---|---:|---|
| One collinear | Positive collinear cap, two zero partner weights | 24 | [Two signed defects](remaining_double_partner_blowup.md) |
| One collinear | Triple cluster, positive partner | 544 | [Complete cluster proof](remaining_cluster_blowup.md) |
| Both collinear | Triple cluster, positive partner | 288 | [Relative cap volume](remaining_two_line_triple.md) |
| Both collinear | Paired zero edges 14 and 36 | 32 | [Paired-edge extension](remaining_two_line_blowup.md) |
| Both collinear | Split pairs in one cap | 16 | [Second-order nonedge displacement](remaining_split_blowup.md) |
| Both collinear | Paired zero edges 14 and 67 | 16 | [Partner cap volume](exhaustive_two_single_blowup.md) |

The mixed cover contains exactly 568 two-zero cells and no cell with
one zero weight in each cap. The two-line cover contains exactly 352
two-zero orders. The checker verifies that its four rows above are
disjoint and cover all 352, using only the checked phase symmetries and
horizontal reflection. The component proofs check the canonical maps
and all additional directional implications.

The cluster proof retains all three relative scales of its two small
edges. Its 183 canonical directional cases have 153 direct Boolean
contradictions; the remaining cases are excluded by exact relative
cap volumes or regular metric charts with signed length defects.
The split-pair proof uses such a chart to force a negative horizontal
displacement of the nonedge 26. Its independently normalized direction
then contradicts the necessary signs. The last paired-edge proof uses
only the direction of edge 67: the exact cap determinant has the
opposite sign from its required weak sign.

All arguments allow unrelated rates of edge lengths, transverse width,
and t. Hence all possible two-zero blow-ups are excluded, and
`h_(3)->0` follows by the same subsequence argument.

## Reproduction and exact remaining scope

```sh
python3 research/type7_completion/common_line_edge_collapse.py /tmp/type7-edge-collapse
python3 research/type7_completion/remaining_flat_blowup.py /tmp/type7-flat-blowup
python3 research/type7_completion/remaining_adjacent_blowup.py /tmp/type7-adjacent-blowup
python3 research/type7_completion/remaining_partner_blowup.py /tmp/type7-partner-blowup
python3 research/type7_completion/remaining_two_line_blowup.py /tmp/type7-two-line-blowup
python3 research/type7_completion/remaining_double_partner_blowup.py /tmp/type7-double-partner
python3 research/type7_completion/remaining_two_line_triple.py /tmp/type7-two-line-triple
python3 research/type7_completion/remaining_cluster_blowup.py /tmp/type7-cluster-blowup
python3 research/type7_completion/remaining_split_blowup.py /tmp/type7-split
python3 research/type7_completion/exhaustive_two_single_blowup.py /tmp/type7-two-single
python3 research/type7_completion/common_line_trapezoids.py
python3 research/type7_completion/exhaustive_vv_geometry.py /tmp/type7-vv
```

The two-line check uses exact integer coefficients. Its optional
output contains all 624 zero-stress orders, the disjoint two-zero
partition, the mixed and two-line edge-count ledgers, and the same complete-model
coverage CNF used by the other cap proofs. The earlier independent
coverage replay, the two V/V unit-propagation contradictions, and the
mixed-family required-sign replay are the finite certificates underlying
the argument. The implicit-function step is an analytic research proof,
not a Lean kernel check.

The remaining common-line analysis must allow at least three vanishing
edge weights. The mixed cover has 320 three-zero cells and 300 four-zero
cells. The two-line cover has 176 three-zero orders and 80 four-zero
orders; two noncollinear stretched caps also remain possible only at
four zero weights. No cap can have three zero weights, since its
remaining edge would have weight one, exceeding one half.

Quantitatively, the second-largest weight in each cap is at least
`1/6`: otherwise its three smaller weights sum to less than one half,
while its largest is at most one half. Thus `h_(5)>=1/6`. Further
collapse reductions can therefore end after the four-zero boundary;
they cannot continue indefinitely. Neither this observation nor the
current third-smallest theorem supplies an explicit height bound.
All positive edge lengths must remain allowed in the finite system.
