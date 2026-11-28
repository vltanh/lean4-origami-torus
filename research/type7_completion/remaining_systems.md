# Rays 1 and 2: complete necessary systems and a failed local shortcut

`remaining_full_metric.py` now generates all fourteen listed masks at the
common target `y=10^6`. Each has 18 real variables, 382 Boolean variables,
8,305 Boolean clauses, and 524 actual affine-circuit partition tests.
The inherited Gram equations retain all four unknown nonedge distances.
The actual nonclique brackets may vanish; their auxiliary generic signs
remain weak inequalities. All twelve disjoint shortest horizontal
triangle pairs are unlinked. Thus these queries include the embedding
and linking information omitted by `type7_focus/generate_remaining.py`.
No mask is declared infeasible.

Two checked reductions now make these systems smaller. The
[shared finite compiler](solver_remaining_compilation.md) covers all
18,080 generic assignments and gives 1,436 K4 branches per marking after
the seven gap-hull filters. Each branch retains only 3–50 actual circuit
tests, with every allowed zero minor preserved by a weak decision diagram.
Its face chart has 29 real variables and 21 quadratic metric equations.

For global asymptotic work, the [bounded axis chart](exhaustive_remaining_axis.md)
is valid for all `y>=32`, with no mask assumption. It has 38 bounded real
variables, 24 quadratic metric equations and six quadratic product-scale
equations. The [axis compiler](solver_remaining_axis.md) applies the full
common sign cover in 268 branches per marking. Independent replay checks
the reductions and emitted formulas. Neither reduction excludes a mask;
three sampled axis queries returned `UNKNOWN` at 3,000 ms each.

The [complete asymptotic cover](exhaustive_remaining_locus.md) further
gives six exact closed polygons and two canonical limit families, with
five universal product-scale identities and all intersections retained.
The [ray-1 two-block proof](remaining_ray1_mask04.md) forces that limit
onto a common transverse line. Its
[first stretch](remaining_ray1_mask04_blowup.md) leaves four symmetric
single-edge endpoints. The [exact metric reducer](solver_remaining_limit.md)
provides twelve projected identities per generic component and retains
the eleven-identity exceptional corners. At a canonical endpoint,
[uniform metric estimates](remaining_ray1_endpoint.md) and
[426 exact virtual-direction certificates](solver_remaining_virtual12.md)
leave three normalized deficit regimes, now all excluded in the
[complete two-block theorem](ray1_two_block_exclusion.md). The regular components have
[18-pattern](exhaustive_c0_angles.md) and
[14-pattern](exhaustive_c1_angles.md) angular covers with additional
necessary tetrahedron signs. Exact metric witnesses show why the first
cover's anchor signs alone are insufficient; its
[complete cells](exhaustive_c0_cells.md) retain all seventy sign
dependencies. Its [strict metric turn](exhaustive_c0_turning.md) reduces
669 generic models to 202, and the
[diagonal certificates](exhaustive_c0_diagonal.md) exclude every regular
equal-height C0 limit for ray 1. Their
[height-order extension](remaining_c0_height_order.md) now excludes
the entire regular half `0<v<=u<1/2`. A
[collinear boundary extension](exhaustive_c0_collinear.md) excludes
`d2=0<d1` with a regular lower cap and its cap-swapped counterpart
`d6=0<d7` in the same height region. The region `v>u` and other C0
boundary cases remain. The
[nonedge vector formulas](exhaustive_c0_nonedge_vectors.md) give exact
norm and dot bounds for `v>u`, although these selected nonedge bounds
already follow from the limiting circle identities. The
[turning-angle proof](solver_remaining_c1_turning.md) excludes regular
C1, and its [rank/height extension](solver_remaining_c1_collinear_rank.md)
excludes every interior C1 limit with exactly one collinear cap,
including coincident vertices. The
[remaining interior C1 boundary](solver_remaining_c1_flat_limits.md)
reduces to six explicit flat families. All satisfy the full 29-row
limiting system and all six active nonedge inequalities. Their
[normal-stretch exclusion](solver_remaining_c1_flat_stretch.md) now
closes every family, including all endpoints and relative rates;
**the entire interior C1 component is excluded for ray 1**.
The [closed regular-C1 turning constraint](exhaustive_c1_holonomy.md)
also supplies a necessary zero-total-turn condition for ray 2, with
all 264 closed sign branches certified. Other ray-1 limits and both
full markings remain open.

## Correct long-ring linking target

The alternating cycles `0246` and `1357` have period `(0,1)` in ray 1
and `(1,1)` in ray 2. Their linking is nonzero by the audited Type 7
alternating-ring theorem. Horizontal unlinking gives
`q(m,n)=B*m*n+C*n^2`, where `B=+1` or `-1`. Disjoint triangles of period
`(-1,1)` in ray 1, or `(0,1)` in ray 2, have linking `k` in `{-1,0,1}`.
In both markings the alternating-ring linking is `k+B`. Consequently
its magnitude is **one or two**. The generator retains both possibilities;
restricting it to magnitude one would be unjustified.

Every consecutive intrinsic triangle has period `(-1,0)`. Its three
oriented horizontal edge displacements lie strictly between `-1/2` and
`1/2` and sum to `-1`, so all three are negative. The full queries add
the eight resulting step-one sign inequalities.

The shared `linked_metric.generate(y, mark=3, mask='phase0')` entry point
preserves the previous ray-3 output byte for byte with its default
arguments. `remaining_full_metric.py` selects the other markings and
adds only their justified step-one signs.

## Local tetrahedron feasibility is insufficient

A tempting faster test uses only the sixteen K4 metrics. Set
`h_i=-X_(i,i+1)` and `b_i=V_(i,i+1)`, cyclically. Then
`sum h_i=7/2` in ray 1 and `5/2` in ray 2, while `sum b_i=1`.
Writing `t=1/y^2`, the intrinsic squared length of a step-one edge is
`h_i^2+b_i^2/t`. For steps two and three it is
`(1-sum h)^2+(sum b)^2/t` along the corresponding consecutive path.
The sixteen local tetrahedra can therefore be tested without any global
reconstruction variables; `remaining_local_metric.py` emits those
quartic necessary inequalities.

However, **both `ray1_04` and `ray2_04` pass every one of these strict
local tests**. Here are exact rational inputs at `t=10^-12`:

| Marking | Horizontal lengths `h`, repeated twice | Vertical steps `b`, repeated twice |
|---|---|---|
| Ray 1 | `(9/20+t/100, 2/5, 1/2-t/100, 2/5)` | `(1/2-3t/25, 11t/200, t/100, 11t/200)` |
| Ray 2 | `(47/100+t/100, 7/50, 1/2-t/100, 7/50)` | `(1/2-t/5, t/20, t/10, t/20)` |

`remaining_local_witness.py` reconstructs the vertex lifts using the
archived cocycles, checks all 24 strict nearest-edge conditions, verifies
all sixteen oriented face areas are positive and sum to two, and checks
positive definiteness of all sixteen K4 Gram matrices with exact rational
determinants. This verification does not use the quartic shortcut formulas.
It certifies sixteen individually realizable tetrahedra for each row;
it does **not** assert they fit together in one spatial realization.

Therefore the local-tetrahedron-only systems cannot exclude all seven
masks of either marking, even with exact arithmetic and unlimited solver
time. Retain global rank-three completion and embeddedness in further
searches. The short unconstrained local trials returned UNKNOWN for all
fourteen masks; the explicit witnesses establish feasibility for the
two `04` relaxations independently of those trials.

## Reproduction

```sh
python3 research/type7_completion/remaining_local_witness.py
python3 research/type7_completion/remaining_verify.py
python3 research/type7_completion/remaining_full_metric.py /tmp/type7-full-remaining
```

Generated queries belong outside the source tree. Parser success and the
local SAT certificates do not discharge any of the fourteen full systems.
