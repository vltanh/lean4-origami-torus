# Compiling the bounded axis chart

`solver_remaining_axis.py` applies the checked common sign cover to the
uniform bounded chart in `exhaustive_remaining_axis.py`. It produces
**268 necessary quadratic branches per marking**, uniformly for
`y >= 32`. No seven-mask split is imposed.

The input is the complete 18,080-model manifest produced by
`solver_remaining_chambers.py`. The wrapper binds that file by SHA-256,
uses every model, and groups only by the sixteen strict K4 signs. The
268 groups retain all generic assignments compatible with their K4
pattern. They have 53–69 universally strict brackets, 3–50 remaining
actual circuit conditions, and 52–148 weak-safe decision-diagram nodes.
The common cover and its RUP proof remain required premises.

The geometric normalization is the independently proved axis gauge:
cyclically rotate the marking so the vertical increment on edge 01 is at
least `1/8`. The exact marking gauges in
`exhaustive_remaining_axis.md` justify this rotation. The wrapper does
not use the topology-only sixteen-element symmetry group to identify
metric cases. Its 268 branches cover the entire unfiltered common sign
set after the valid axis normalization.

Each branch preserves the full bounded-axis metric prefix: 38 real
variables, all 24 quadratic edge equations, six quadratic product-scale
equations, coordinate bounds, shortest lifts, intrinsic areas and all
nonedge contraction conditions. It replaces only the generic Boolean
and actual circuit suffix. All actual minors are those of the axis
coordinates `(P_u,P_v,z+tH)`. The positive axial scaling preserves
orientation and affine incidence.

The decision diagram uses nonstrict overlapping sign tests at every
minor that may vanish. The same zero-boundary argument as in
`solver_remaining_compilation.md` therefore applies. Every surviving
circuit is exactly the corresponding condition from the full axis query.

`solver_remaining_axis_verify.py` first replays the complete source
manifest and verifies the exact source hash. It independently reconstructs
all 268 groups, their strict and rank facts, their retained circuits,
and their full decoded model sets. When queries were emitted, it checks
the complete metric prefix, every minor definition, each diagram node,
every K4/strictness assertion, and the exact original retained circuit
formulas before parsing every query.

## Reproduction

After producing and replaying the common source cover as documented in
`solver_remaining_compilation.md`:

```sh
python3 research/type7_completion/solver_remaining_axis.py \
  /tmp/type7-remaining-compiled /tmp/type7-axis-compiled \
  --queries --mark 2
python3 research/type7_completion/solver_remaining_axis_verify.py \
  /tmp/type7-remaining-compiled /tmp/type7-axis-compiled
```

The observed wrapper run took **5.69 seconds**, including reconstruction
of the cover, the exact axis identity checks, and all 268 ray-2 queries
at `y=10^6`. The emitted queries range from **121,213 to 171,398 bytes**.
This wrapper makes no new SAT calls and requires no new coverage trace:
it partitions the already complete common model list without filtering.

### Bounded nonlinear diagnostic

One ray-2 query from the low, middle and high retained-circuit counts was
run at `y=10^6` with a **3,000 ms solver limit** each. Branch numbers are
zero-based indices in the generated sorted K4 cover.

| Branch | K4 sign pattern | Retained circuits | Diagram nodes | Result | Total call time |
|---:|---|---:|---:|---|---:|
| 1 | `+++++-++++--++++` | 3 | 53 | UNKNOWN: timeout | 3.96 s |
| 159 | `+-+-+-+++-+++-+-` | 18 | 54 | UNKNOWN: timeout | 4.25 s |
| 264 | `+---++-++-+-+++-` | 50 | 116 | UNKNOWN: timeout | 4.00 s |

Total call times include context creation, parsing and preprocessing.
The sample produced no decision, so the diagnostic stopped after these
three queries. It supplies no exclusion or realizability evidence.

The reduction does not itself exclude a marking. A nonlinear certificate
or a geometric argument is still required for the remaining branches.
