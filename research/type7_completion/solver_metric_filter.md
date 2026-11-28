# Reusing the finite metric exclusions in geometry searches

`solver_metric_filter.py` exports optional clauses for the existing
orientation and directional geometry formulas. It independently replays
the supplied chamber manifest with `solver_verify.py` before using any
exclusion. Every exported block records its certified representative,
proof method, one of the 16 checked phase symmetries, and global spatial
orientation. No new Boolean variables are introduced.

```sh
python3 research/type7_completion/solver_metric_filter.py \
  /tmp/type7-chambers /tmp/type7-filter --height 8
```

For the current 78-chamber certificate union, this produces 2,280 clauses
of length 70: 1,140 excluded normalized primary models and their global
negatives. Thus 748 of the 1,888 normalized models remain. The proof
chosen for every block is valid for every `y >= 8`; the two separate
product certificates requiring `y >= 32` have alternatives valid already
at `y >= 8` within the accepted quadratic corpus.

Each clause negates one complete sign assignment. Its justification is
the corresponding *weak-chamber* exclusion for actual spatial brackets.
It is therefore valid even when some actual brackets vanish: the generic
completion signs still satisfy the weak inequalities used by that proof.
The helper does not assert nonzero brackets in a limiting configuration.
Instead, after passing to a constant generic-completion subsequence, it
excludes completion patterns already impossible at every sufficiently
large finite height. Both global orientations are essential when the
directional formula removes the compiler's normalization `[0123] > 0`.

The filter is necessary information, not a complete geometric formula.
Callers must justify their directional or limiting constraints separately
and must retain the original topology clauses. A filtered `UNSAT` result
can be replayed by the existing Boolean proof checker after checking the
filter ledger; a `SAT` result is only a surviving necessary system.
Enumeration completeness still uses the existing RUP coverage proof.
Soundness of the individually blocked patterns does not depend on that
enumeration being complete.

An initial diagnostic appended the filter to the two outstanding
directional pilots. All 30 previously satisfiable mixed triple-A /
positive-B cell-hierarchy formulas remained satisfiable, as did the
coupled collapsed-edge `14/67` formula. No additional geometric cell is
claimed excluded by those trials.
