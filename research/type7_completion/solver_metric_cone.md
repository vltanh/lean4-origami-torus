# Reproducible discovery of exact metric certificates

`solver_metric_cone.py` makes the faster quadratic search reproducible.
It constructs the exact 490-coordinate quotient, runs a bounded LP,
reconstructs candidate weights over the rationals, and exports a packet
only after an independent coordinate-identity check and a positive K4
residual check. The existing proof modules do not import this producer
or its LP dependencies.

## Run a bounded search

Use a chamber manifest generated and checked according to
`solver_compilation.md`. To reproduce two already excluded chambers:

```sh
python3 research/type7_completion/solver_metric_cone.py \
  /tmp/type7-chambers /tmp/type7-discovery \
  --case 48 --case 55 --seconds 10
```

Omitting `--case` tries only the manifest's remaining chambers. Each LP
call has a five-second default budget. `--seconds` changes that budget,
up to sixty seconds; it does not impose a floating tolerance on proof
verification. Exact algebraic reconstruction runs separately.

The source comparison coefficient defaults to `1/8`, valid for all
`y>=8`. A stronger comparison can be requested explicitly:

```sh
python3 research/type7_completion/solver_metric_cone.py \
  /tmp/type7-chambers /tmp/type7-thin-discovery \
  --case 0 --coefficient 1/1024 --seconds 5
```

The producer prints the exact required integer height. For `1/1024`
this is `y>=91`, since the geometric source coefficient is `8/y^2`.
Every exported packet retains its coefficient so that replay can recover
the valid range. A result must be used only in its proved height range.

NumPy, SciPy, and SymPy are required for discovery. The `--method` option
accepts `highs`, `highs-ds`, or `highs-ipm`. `--feasibility` seeks any
dual certificate without minimizing its weights. These choices affect
discovery only; all exports face the same exact proof checks.

## The required acceptance steps

The producer performs these steps for each selected chamber:

1. Reconstruct every signed metric-difference inequality from verified
   phase symmetries and multiply it by each nonnegative raw bracket.
2. Express all 2485 raw quadratic products in 490 exact quotient
   coordinates. The substitution has 19,411 nonzero integer entries;
   no cached discovery matrix is trusted or required.
3. Ask the bounded LP for nonnegative metric weights and a nonnegative
   residual with a positive coefficient on a proved-strict product.
4. Reconstruct the proposed rational weights. If direct rationalization
   is not exact, solve its active support over the rationals with the
   normalization equation. Reject negative weights or a nonzero exact
   remainder.
5. Form a universal identity in raw signed brackets. Expand it into
   ordinary three-by-three determinants in twenty-one formal coordinates.
   Every coordinate coefficient must be exactly zero.
6. Recompute the chamber residual and require a positive product of two
   actual K4 brackets. Check every claimed sign-model/symmetry reuse in
   the same exact manner.

The numerical support threshold is used only to suggest an active
linear system. It is not a proof tolerance. A candidate is rejected
unless the subsequent rational equations, positivity checks, and
independent coordinate expansion all pass.

For this producer's exports, the final strict term is always a K4
product. Every nonclique bracket may vanish. The full compiler's
propagated strictness set helps discover the certificate, but the
exported contradiction does not need an extra nonclique margin.

## Outputs and proof-only replay

The output directory contains an updated `discovery_summary.json` and
one `phase0_chamber_NNN_metric_certificate.json` for each successful
source case. A packet includes the complete integer certificate and
every independently checked reuse. It never modifies the repository's
accepted certificate data or compiler exclusions automatically.

To replay an exported packet without importing NumPy or SciPy:

```sh
python3 research/type7_completion/solver_metric_cone.py \
  /tmp/type7-chambers \
  --replay-candidate /tmp/type7-discovery/phase0_chamber_048_metric_certificate.json
```

Proof-only replay checks the universal coordinate identity, every metric
source, every phase permutation, the manifest model binding, the full
nonnegative residual, and a positive K4 product. The stored quotient
and the discovery LP are not involved.

A timeout, numerical failure, infeasible dual, or rejected support makes
no assertion about existence of a geometric realization. Only exported
and exactly replayed packets establish chamber exclusions. Complete
Boolean coverage still requires the separate RUP check, and a full
marking exclusion requires every remaining metric chamber to be handled.

## Recorded verification

A fresh process reproduced both test cases. Exact quotient construction
took 0.06 seconds. Case 48's LP took 0.84 seconds and produced two metric
products covering nineteen chambers. Case 55's LP took 0.73 seconds and
produced five metric products covering two chambers. Both exports passed
independent coordinate expansion and exhaustive phase-symmetry reuse.

A separate check exercised the active-basis reconstruction path on the
previous 225-variable case-55 candidate; rational reconstruction and
independent replay completed in 0.86 seconds. Proof-only import did not
load NumPy or SciPy. An intentionally altered integer identity
coefficient was rejected by coordinate expansion. These checks verify
both the performance mechanism and the exact acceptance boundary.
