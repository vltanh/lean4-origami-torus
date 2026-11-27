# Fast, independently checked Boolean certificates

[`solver_cnf_certificates.py`](solver_cnf_certificates.py) turns generated
geometry CNFs into reusable proof packets. Z3 produces a trace; the existing
standalone [`solver_check_rup.cpp`](solver_check_rup.cpp) independently
checks every step by reverse unit propagation. A solver's `unsat` answer
alone is never accepted.

This avoids asking the small exhaustive DPLL checker to rediscover each
proof. On `fourzero_split_directions_p0.cnf`, with 19,311 original clauses:

| Operation | Measured seconds |
|---|---:|
| Earlier independent DPLL search, 104,965 nodes | 107.634 |
| Trace production | 0.274 |
| Independent RUP replay | 0.107 |
| Production and replay combined | 0.381 |

These are elapsed measurements in the shared research workspace, not a
controlled hardware benchmark. The earlier DPLL run used a three-worker
batch; the new batch used two workers. An earlier single-formula trial
also completed production and replay in 0.394 seconds. The same original
CNF was checked in every comparison.

All six split-cap direction/nonedge formulas and their shared coverage
formula independently replayed. The seven-formula batch took 15.435
seconds, mostly checking the common coverage trace. That trace has 67,473
RUP additions and is shared by many geometry packages. A later proof-only
replay of the entire batch also passed. The two vertical-V endpoint
formulas took 0.479 seconds together, including production and checking.

The subsequent complete mixed four-zero package has 96 formulas. All
independently checked in 21.377 seconds, including the common coverage
trace. Four formulas used the bounded clause-order retry described below.
The final two triangle-pair formulas also passed, in 0.863 seconds.

## Reproduce

Compile the checker with assertions enabled, then give the runner one or
more CNFs or directories containing CNFs:

```sh
g++ -O3 -std=c++17 research/type7_completion/solver_check_rup.cpp -o /tmp/type7-rup-check
python3 research/type7_completion/solver_cnf_certificates.py /tmp/type7-proofs \
  --checker /tmp/type7-rup-check /tmp/type7-fourzero-split /tmp/type7-four-cluster-v
python3 research/type7_completion/solver_cnf_certificates.py /tmp/type7-proofs \
  --checker /tmp/type7-rup-check --replay-only
```

Use `--jobs` to select one to eight worker processes, and `--seconds` for
each solver attempt and checker timeout, at most sixty seconds each.
Production requires the Z3 shared library, loaded directly through its C
API. Proof-only replay requires Python's standard library and the compiled
checker; it does not load Z3, SymPy, or a numerical optimization library.
Generated CNFs and proof traces stay outside the source tree.

## What is checked

The runner validates every DIMACS header, variable bound, clause terminator,
and clause count. It accepts comments and multiline clauses, then emits
one complete clause per line for the independent checker. It preserves
the source's literal and clause order for proof production: changing those
orders can change the solver's search and trace.

A separate canonical representation sorts clauses and their literals,
preserving multiplicities. Its SHA-256 digest identifies the formula.
Inputs with the same clause multiset share one proof, so a combined run
checks repeated coverage formulas only once. This equivalence is exact;
it does not use a heuristic simplifier or rename variables.

Each packet contains `input.cnf` and `proof.drat`. The manifest records
every original source hash, its packet identity, the exact packet CNF and
proof hashes, the checker executable hash, and the checker's explicit
result. Proof-only mode revalidates the formula identity and both file
hashes, then independently rechecks the complete proof. The manifest's
`verified` field is not itself evidence of unsatisfiability.

The checker starts with the original clauses, shifting variable numbers
to match the producer's guarded encoding. The guard is fixed true, so
the added guarded clauses impose no restriction on the original formula.
Even trace lines marked as solver inputs must already be present or pass
reverse unit propagation. Every other addition must pass the same check,
and the trace must derive the empty clause. Deletions cannot introduce a
contradiction.

SAT, UNKNOWN, a timeout, a failed hash, or a missing final contradiction
fails the run. Some solver traces use stronger DRAT transformations; those
are deliberately rejected by this smaller checker. If the source-order
trace contains a non-RUP step, production makes one bounded retry with
canonically ordered clauses and literals. The original CNF is unchanged;
the replacement trace is independently checked from its beginning.
The manifest records both attempts. If neither trace is accepted, the run
fails. Proof-only mode never searches or retries.

During validation, one clause-reordered trace was rejected while its
source-order trace passed. Four other formulas needed the canonical-order
retry. Thus neither ordering is universally better. Only the fully
accepted replacement trace is retained as a proof, and no checker rule
is relaxed to accommodate a producer.

Validation also confirmed that reordered/multiline equivalent inputs
share one proof, modified proofs are rejected, satisfiable inputs cannot
produce a verified packet, and malformed DIMACS is rejected. A fabricated
manifest with internally consistent hashes and a false empty-clause proof
was rejected by the independent checker itself.

## Scope

This is a performance and reproducibility improvement, not an additional
geometric exclusion. Each geometry generator must still justify that its
CNF is necessary, cover all intended shapes and relative scales, and
verify any metric identities used to add clauses. The runner verifies
the resulting finite Boolean contradiction without repeating its search.
It does not decide the remaining nonlinear metric systems or turn an
asymptotic research proof into a finite-height or Lean theorem.
