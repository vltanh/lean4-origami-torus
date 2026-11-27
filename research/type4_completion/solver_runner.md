# Sustained full-domain solver runs

The runner removes the **overall solver timeout** from the eight complete
quartic fixed-target inputs. It does not change the formulas or close a case.
The completion count remains **0/8** until a suitable exact certificate or
fully validated embedding is obtained.

## Reproduce

Use Linux, Python 3.9 or newer, SymPy for preparation, and a Z3 shared library
(`libz3.so`). The Z3 executable and Python `z3` package are not required.
Run from the repository root:

```sh
python3 research/type4_completion/solver_runner.py prepare /tmp/type4-unlimited
python3 research/type4_completion/solver_runner.py run /tmp/type4-unlimited \
  --jobs 2 --timeout-ms 0 --memory-mb 3072
```

Preparation regenerates all eight **full** domains, including strict-support
and mixed-face cuts. It records their SHA-256 hashes, the generator revision,
the hashes of its three source files, and a frozen copy of the worker code.
An existing preparation directory must be empty, so a new preparation cannot
overwrite previous evidence. The eight input hashes match those recorded in
[direct_metric.md](direct_metric.md).

The default queue is `ray2_2`, `ray2_1`, then `ray1_1` through `ray1_6`.
Two workers run concurrently. The other six await a free slot; they do not
receive CPU time while the first two remain active. Increase `--jobs` on a
machine with enough memory to give more cases simultaneous search time.

`--timeout-ms 0` explicitly sets Z3's timeout to zero and its resource-step
limit to zero. There is no supervisor wall-time cutoff. This differs from
`direct_metric.py --solve-ms 0`, which only generates an input and does not
invoke a solver. A positive `--timeout-ms` is available for diagnostics.

`--memory-mb 3072` caps each worker's **virtual address space** at 3 GiB using
Linux `RLIMIT_AS`. This is a memory limit, not a time limit or an estimate of
the memory required to solve a row. Their combined virtual address space is
therefore limited to 6 GiB, leaving room on the approximately
10 GB environment used for the initial run. `--memory-mb 0` disables this
guard; the operating system can still exhaust memory or kill a process.

## Evidence and monitoring

The run directory contains:

| File | Contents |
|---|---|
| `manifest.json` | Input hashes, formula counts, source revision/hashes and frozen worker hash |
| `inputs/*.smt2` | Exact complete inputs, with a final `check-sat` command |
| `runner.py` | Frozen worker implementation used by this preparation |
| `status.json` | Atomic latest supervisor/case states, timestamps, PIDs, CPU and memory use |
| `resources.jsonl` | Append-only snapshots, normally every 15 seconds |
| `<case>/attempt-0001/worker.log` | Worker output and native Z3 errors |
| `<case>/attempt-0001/result.json` | Solver version, settings, input hash, actual decision or interruption/error |
| `<case>/attempt-0001/statistics.json` | Z3 statistics after `check` returns |
| `<case>/attempt-0001/model.smt2` | SAT model, preserving exact algebraic `root-obj` values |

No other thread calls into a Z3 context while its `check` is running. During
the search the supervisor reads operating-system CPU/RSS information. Solver
statistics and models are extracted only after `check` returns. The decision
is saved before these exports, so an export failure does not erase it.

A solver-produced `UNKNOWN` includes its reason. A crash, memory-related
native exit, or interrupted worker has a separate process/error state and is
**not** relabeled `UNKNOWN` or `UNSAT`. A memory-related native exit may require
reading `worker.log`; a signal alone does not establish an out-of-memory cause.
Nothing in the monitor interprets elapsed time as progress toward a proof.

## Resume and stop

The same `run` command resumes unstarted cases and attempts that stopped
without a terminal record. It preserves completed attempt directories. To
retry previously recorded `UNKNOWN`, error or interrupted cases, use:

```sh
python3 research/type4_completion/solver_runner.py run /tmp/type4-unlimited \
  --jobs 2 --timeout-ms 0 --memory-mb 3072 --retry-incomplete
```

Every retry receives a new numbered attempt directory. Existing SAT/UNSAT
decisions are preserved and their input/worker provenance is checked. A file
lock prevents two supervisors from running the same directory simultaneously.
Input and worker hashes are checked before accepting cached results or
starting a worker. Ctrl-C or SIGTERM stops this supervisor's own children and
records interruptions.

**Resume restarts an interrupted solver from its input.** Z3's internal
search state is not checkpointed. Keeping these logs does not preserve all
search work after a machine restart. Run on a persistent machine or in a
managed terminal/session if computation must outlast an interactive workspace.
Removing a configured timeout does not guarantee that the hosting environment
will remain available indefinitely.

## Solver semantics and verification

The initial implementation uses `Z3_mk_solver_for_logic(..., "QF_NRA")`, matching
the earlier bounded attempts. Z3 4.13.3 selects a portfolio: it includes
internally timed trials and eventually an unrestricted `qfnra-nlsat` attempt.
Removing the total timeout does not remove those internal trial limits or
force one continuous NLSat search from the outset.

Proof generation remains disabled. This version's NLSat tactic explicitly
rejects proof generation; enabling `proof=true` can select a different
algorithm. An `UNSAT` string is useful research evidence but is not itself an
independently checked certificate or a Lean proof. A SAT model likewise needs
exact reconstruction and validation against the complete geometric problem.

The underlying fixed problem is polynomial real arithmetic, a decidable
theory. This justifies trying a longer exact search; it does not provide a
practical runtime bound or a completion guarantee for this implementation on
a finite machine.

Version-pinned implementation references:

- [Z3 timer: zero disables the overall timer](https://github.com/Z3Prover/z3/blob/z3-4.13.3/src/util/scoped_timer.cpp).
- [Z3 resource counter](https://github.com/Z3Prover/z3/blob/z3-4.13.3/src/util/rlimit.cpp).
- [QF_NRA portfolio](https://github.com/Z3Prover/z3/blob/z3-4.13.3/src/tactic/smtlogics/qfnra_tactic.cpp).
- [NLSat tactic and proof-generation restriction](https://github.com/Z3Prover/z3/blob/z3-4.13.3/src/nlsat/tactic/nlsat_tactic.cpp).
- [Original nonlinear real arithmetic algorithm](https://www.microsoft.com/en-us/research/publication/solving-non-linear-arithmetic/).

These operational changes add no Lean theorem. See the
[completion roadmap](ROADMAP.md) for the mathematical status.

## Initial run and runner checks

The no-timeout run began on 2026-11-27 at 20:01:39 UTC with Z3 4.13.3.0.
Both ray-2 cases entered the solver; the six ray-1 cases were queued. The
[initial observation](solver_run_20261127.json) records the input hashes,
settings, elapsed CPU/wall time and memory use at its stated timestamp.
It is a historical checkpoint, not a live status page or a solver result.

The integration check uses small independent fixtures, never the running
Type 4 jobs:

```sh
python3 research/type4_completion/solver_runner_check.py
```

It passed exact algebraic SAT model export, UNSAT, malformed-input errors,
an actual bounded timeout, an enforced address-space limit with no time
limit, input/provenance rejection, two-worker scheduling, crash and interrupt
classification, retries with preserved histories, and prevention of duplicate
workers after a supervisor crash.
