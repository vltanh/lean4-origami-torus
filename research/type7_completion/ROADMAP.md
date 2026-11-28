# Type 7: finish a whole marking

## Status after the reorientation — 28 November 2026

**Type 7 universality remains open.** The missing result is a mathematical
obstruction or construction, followed by its Lean proof. This update does
not close a marking. The earlier proof packages are retained in the
[proof inventory](PROOF_INVENTORY.md); their increasing subdivision counts
are not completion milestones.

Lean already proves Type 7 realizations for every reduced modulus
`0 <= x < 1/2`. The remaining boundary is `1/2 + i*y`, `y >= sqrt(3)/2`.

| Complete marking | Strongest recorded research result | Full-marking status |
|---|---|---|
| Ray 1 | Interior C1, regular C0 at all heights, both-collinear interior C0, and additional one-collinear cases excluded | Open: upper-a interior C0 and degenerate height boundaries remain |
| Ray 2 | Entire interior C1 excluded | Open: C0 and height boundaries remain |
| Ray 3 | No realization above some finite `Y3`, without a numerical threshold | Research proof recorded; Lean assembly open |
| Ray 4 | No realization when `y^2 >= 63/16` | Audited hand proof recorded; Lean assembly open |

The present audit inspected the necessity bridge and the global strategy;
it did not re-audit every earlier analytic case. Principal references are
the [geometric audit](geometric_audit.md),
[ray-3 theorem](ray3_boundedness.md), and
[complete interior ray-2 C1 theorem](remaining_ray2_c1_exclusion.md).

## The negative completion target

Prove **both** remaining markings absent above finite heights `Y1,Y2`.
Then choose one common height above `Y1,Y2,Y3,sqrt(63)/4`. The four-marking
cover proves that this one torus has no Type 7 realization. There is no
need to prove that the common height equals `10^6`.

An exclusion of one cap order, a limiting stratum, or a sign subchamber
does not discharge this target. No new subdivision is the default next
step. A proposed argument must state how it covers the whole marking,
including shrinking edges, zero nonclique determinants, endpoint heights,
and unrelated collapse rates.

Eventual nonexistence for ray 2 is **not an established premise**. A
certified spatial construction is a legitimate competing route. To prove
universality, that route must cover the entire missing sharp boundary;
one witness, or a construction only for large heights, does not suffice.

## One full finite-height formula per remaining marking

The [bounded axis generator](exhaustive_remaining_axis.py) now accepts
`--all-heights`. It leaves `t=1/y^2` variable and imposes exactly

\[
0<t\le 1/Y^2,\qquad Y\ge32.
\]

This is the original finite geometry throughout the whole height tail,
not the relaxed fiber at `t=0`. Each marking has one necessary formula:

- 39 real variables, including `t`;
- all 24 original metric equations and six product equations;
- all 524 actual affine-circuit tests and the weak generic-sign coupling;
- the full shortest-lift, face-orientation, nonedge and linking conditions.

There is no mask, C0/C1, cap-order, or height-order restriction. The
existing coordinate bounds hold uniformly for every `y>=32`; no
collapsing quantity receives an artificial positive lower bound.
Metric equations have total degree three, and actual minors degree at
most four. The 38-variable fixed-height mode is unchanged.

An independently checkable **UNSAT proof** for each whole-tail formula
would supply the missing `Y1,Y2` research bounds. A SAT assignment is only
a candidate at *some* height in the tail and requires exact reconstruction
and embedding verification. It does not establish realizability at
arbitrarily large heights. UNKNOWN and failed numerical searches decide
nothing.

Reproduce the source verification and generate both complete targets:

```sh
python research/type7_completion/verify_all_heights.py
python research/type7_completion/exhaustive_remaining_axis.py /tmp/type7-full \
  --all-heights --y 32
```

The source checker binds every emitted metric equation to the original
squared-distance equation as an identity in symbolic `t`, checks all
322 actual minor definitions, and compares the full specialized formulas
with six frozen pre-change fixed-height sources. A separate sparse-rational
peer check compared all 431 definitions and 9,359 original assertions
for both markings at `y=64`. These checks passed. They verify the encoding,
not infeasibility.

Two complete `Y=32` solver attempts, each with a 30,000 ms internal limit
and a 45-second external bound, both returned **UNKNOWN (timeout)**.
Neither marking is excluded. Repeating these calls with a larger time
limit is not a proof strategy by itself.

## What the global audit ruled out

The C1 equal-perimeter argument uses convexity of the finite inner
sections. Remaining C0 sections can be nonconvex, so that argument does
not extend merely by taking closures or retaining weak signs.

The exact [global-relaxation diagnostic](verify_global_relaxation_gap.py)
also exhibits a regular ray-2 C0 configuration satisfying all 29 limiting
metric/product rows, nearest-lift bounds, positive developed face areas,
all six common sign consequences, and consistent signed section-area
ordering at every interior height. Nevertheless, edge `03` crosses the
interior of face `617`, with exact positive barycentric coordinates.
Thus metric equations, common signs and area ordering cannot replace
actual nonintersection. This is a counterexample to a proposed shortcut,
not a realization or a Type 7 exclusion.

```sh
python research/type7_completion/verify_global_relaxation_gap.py
```

The existing trapezoid formulas also fail at the sharp boundary; see the
[all-chamber obstruction for that parametrization](../type7_closure/README.md).
Changing the lattice basis or applying a Dehn twist does not transfer a
ray-1 obstruction to ray 2 at the same metric.

## Acceptance gate

Advance the classification only with one of these complete results:

1. A proof excluding a whole remaining marking on a full height tail,
   with every degeneration and the geometric necessity bridge retained.
2. An exact construction that changes the global target, with its metric,
   embedding and range certified explicitly.

After the two remaining exclusions, assemble the common-height theorem
and the necessary geometric and certificate bridges in Lean. No new Lean
theorem, successful Lean build, or completed Type 7 proof is claimed here.
