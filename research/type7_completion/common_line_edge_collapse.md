# Every unbounded ray-3 sequence has a vanishing short edge

**Theorem.** Along any sequence of actual canonical ray-3 realizations
with `y -> infinity`, the minimum of the eight positive short-edge
weights tends to zero:

\[
\min_{e\in A\cup B} h_e\longrightarrow0,
\qquad h_e=-X_e>0.
\]

Equivalently, no such unbounded sequence can keep all eight weights
bounded below by one positive number. The proof includes all possible
rates of transverse flattening. It uses the geometric necessity audit
and the preceding exact cap and blow-up certificates.

This theorem still does not exclude an unbounded sequence whose edges
shrink, provide a numerical height threshold, or close the full marking.
Its purpose is to identify the remaining boundary precisely.

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
the theorem. If the minimum weight failed to tend to zero in the original
sequence, it would have a subsequence with a common positive lower bound,
which the proof has just excluded.

## Reproduction and exact remaining scope

```sh
python3 research/type7_completion/common_line_edge_collapse.py /tmp/type7-edge-collapse
python3 research/type7_completion/remaining_flat_blowup.py /tmp/type7-flat-blowup
python3 research/type7_completion/common_line_trapezoids.py
python3 research/type7_completion/exhaustive_vv_geometry.py /tmp/type7-vv
```

The new two-line check uses exact integer coefficients. Its optional
output contains all 624 zero-stress orders and the same complete-model
coverage CNF used by the other cap proofs. The earlier independent
coverage replay, the two V/V unit-propagation contradictions, and the
mixed-family required-sign replay are the finite certificates underlying
the argument. The implicit-function step is an analytic research proof,
not a Lean kernel check.

The remaining common-line analysis must allow at least one vanishing
edge weight. Such a boundary cannot be removed by imposing a minimum
edge length or a numerical separation tolerance in the finite system.
