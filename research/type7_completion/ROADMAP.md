# Type 7: roadmap to a complete classification

## Current result and next target

**Ray 3 is excluded at every sufficiently large height by a complete
research proof.** The [consolidated boundedness theorem](ray3_boundedness.md)
excludes every possible unbounded sequence, including all collapsing
edges, zero nonclique brackets, and unrelated degeneration rates. Its
last steps cover all 300 mixed four-zero cells and all sixteen
two-noncollinear zero-cone supports. The finite certificates and exact
metric identities independently replay.

For ray 1, the [entire two-block limit](ray1_two_block_exclusion.md)
and the [regular C1 component](solver_remaining_c1_turning.md) are now
excluded. The [C1 boundary extension](solver_remaining_c1_collinear_rank.md)
also excludes every interior limit with exactly one collinear cap,
including coincidence. The
[two-collinear-cap boundary](solver_remaining_c1_flat_limits.md) reduces
to six explicit flat families, including zero-edge endpoints. They
are compatible with all limiting metric equations and the six active
nonedge inequalities, but their
[nontrivial normal stretches](solver_remaining_c1_flat_stretch.md) are
now all excluded. This closes **the entire interior C1 component for
ray 1**, including every degeneracy and relative collapse rate.
The [regular C0 height-order region](remaining_c0_height_order.md)
`0<v<=u<1/2` is excluded by exact metric and sign arguments, extending
the earlier diagonal certificates. A
[collinear extension](exhaustive_c0_collinear.md) also excludes two strict
cap orders in this region, with the opposite cap regular. The two-block proof closes
all four symmetric endpoints, including every relative collapse rate.
Ray 1's other limit regions,
ray 2, and the Lean assembly remain open.

The proof gives a threshold `Y3` but no numerical value. It therefore
does not establish the separate target `tau* = 1/2 + 10^6 i`. The finite
ledger remains 78 of 132 ray-3 chambers excluded and zero of the fifteen
ray-1/2/3 full systems closed at that particular modulus.

**The next geometric targets are the complete ray-1 and ray-2 markings.**
Eventual exclusions for both would combine with the ray-3 bound and
ray-4's explicit bound at one common sufficiently large height. This
would prove nonuniversality without requiring a numerical value of that
height. The fourteen fixed-mask systems remain an alternative route if
their common height is also proved to exceed the ray-3 threshold.

This roadmap distinguishes research proofs, fixed-height exclusions,
and the final Lean classification. The new ray-3 theorem is a complete
eventual research exclusion; the Lean bridges remain open.

## 1. What completion means

The Lean theorem
[`Type7.open_strip_regular_realizes`](../../OrigamiTorus/Type7/WideLift.lean)
already constructs regular realizations for

\[
0\le x<\tfrac12,\qquad y^2\ge1-x^2.
\]

The remaining reduced boundary is the whole sharp ray
`x=1/2`, `y>=sqrt(3)/2`. There are two legitimate ways to finish.

**Negative route, currently proposed.** Prove that the one torus `tau*`
has no Type 7 realization, covering all four admissible marking classes.
In the existing formal language the intended conclusion is a theorem of
the form

```lean
¬ OrigamiTorus.Type7.Realizes 1
    ((1 / 2 : ℂ) + (1000000 : ℂ) * Complex.I)
```

This theorem would establish nonuniversality while preserving the known
existence results. Exclusions at different moduli cannot be combined to
prove it.

An equally sufficient negative route is to prove an eventual bound for
each of the four markings, then choose one common height above all four
bounds. This establishes the existence of a nonrealizable sharp modulus
without asserting that it equals `tau*`. Ray 3 now has such a research
bound; rays 1 and 2 remain open.

**Positive alternative.** Construct embedded, facewise isometric Type 7
realizations for every `1/2+i*y`, `y>=sqrt(3)/2`, and combine them with the
open strip and lattice reduction. A single sharp witness, even a regular
one, proves neither this coverage nor universality. A certified witness
at `tau*` would refute the proposed *negative target*, requiring a new
target or a constructive program.

The realization predicate is defined in
[`Type7/Tiling.lean`](../../OrigamiTorus/Type7/Tiling.lean): it includes
the lattice quotient, closed embedding, specified affine faces, and their
metric equality. Cone-angle equations or correct edge lengths alone are
not the requested conclusion.

## 2. Exact current ledger

The marking basis consists of the cycles `012` and `025`. The four
representatives below are read from
[`cases.json`](../linking_checkpoint/cases.json), and agree with the
four sharp-ray representatives in
[`WindingOrbits.lean`](../../OrigamiTorus/Winding/WindingOrbits.lean).

| Marking | Periods of `012`, `025` | Status at `tau*` |
|---|---|---|
| `t7_ray_1` | `(-1,0)`, `(-1,1)` | Seven open masks |
| `t7_ray_2` | `(-1,0)`, `(0,1)` | Seven open masks |
| `t7_ray_3` | `(-1,1)`, `(0,-1)` | One open canonical phase |
| `t7_ray_4` | `(-1,1)`, `(0,1)` | Excluded for `y^2>=63/16` by the audited hand proof; Lean assembly open |

For ray 3, the [eventual exclusion](ray3_boundedness.md) applies to both
localized phases above an unspecified `Y3`; its comparison with `10^6`
is not known. Thus the fixed-target table and the stronger asymptotic
result are consistent.

For rays 1 and 2, let `b_i` be the normalized vertical displacement of
the edge `i -> i+1`, cyclically modulo eight. A digit in a mask means
`|b_i|>=1/1000`; an absent digit means `|b_i|<1/1000`. Equality therefore
belongs to the large-step side. These are edge-index masks, not lists of
vertices to keep or discrete candidate placements.

| Mask | Exact ray-1 system ID | Exact ray-2 system ID | Status |
|---|---|---|---|
| `03` | `ray1_03` | `ray2_03` | Both open |
| `04` | `ray1_04` | `ray2_04` | Both open |
| `014` | `ray1_014` | `ray2_014` | Both open |
| `015` | `ray1_015` | `ray2_015` | Both open |
| `025` | `ray1_025` | `ray2_025` | Both open |
| `0125` | `ray1_0125` | `ray2_0125` | Both open |
| `0145` | `ray1_0145` | `ray2_0145` | Both open |

The fifteenth open ID is **`ray3_phase0`**. Its short rings are `0145`
and `2367`. The other endpoint phase, with short rings `0347` and `1256`,
is equivalent by the checked cyclic rotation. Thus it is not a sixteenth
independent system.

The seven-mask cover holds at every `y>=10^6`. Its metric proof forces
exactly two components of large edges in the cyclic distance-one-or-two
graph, separated by at least two small edges on each side. Each component
has signed vertical sum greater than `0.44`; suitable short-triangle
hulls are separated by more than `0.32*y`.

For ray 3, an exact variance identity gives distance less than `1/y^2`
from one of the two phase endpoints at every `y>=4`. In the canonical
phase, short-edge vertical displacements have magnitude less than
`7/(4*y^2)`, while the sixteen cross-edge displacements have magnitude
greater than `1/2-7/(4*y^2)`. The two short-ring hulls are strictly
separated for `y>=8`. These are finite-metric statements, not assumptions
about a nondegenerate limiting cap. See
[`remaining_markings.md`](../type7_focus/remaining_markings.md).

**Count: zero of these fifteen open systems is excluded.** Ray 4 is a
separate completed research exclusion, with the geometric qualifications
below; it is not one of the fifteen.

## 3. What is established for ray 4

The two alternating cycles `0246` and `1357` must have nonzero linking
in an embedded flat Type 7 realization. The
[`geometric necessity audit`](geometric_audit.md) supplies the hand proofs
of strict support, mixed-side faces, K4 nondegeneracy, coherent shortest
markings, and valid generic perturbation, using Schwartz's established
seven-vertex nonexistence and spherical hemisphere results. It also
audits the necessary orientation encoding and independently replays the
Boolean certificate. Unlinking would leave
sixteen necessary generic orientation models. They form two symmetry
orbits, and each representative contradicts a product of six exact
Grassmann–Plücker inequalities. The finite sign coverage and polynomial
contradictions have independently replayable certificates.

In ray 4 both alternating cycles have horizontal period `(1,0)`.
Nonzero horizontal linking gives extrinsic diameter less than one. The
Hamiltonian cycle `01234567` has period `(-3,4)`, of physical length
`sqrt(1+16*y^2)`, whereas its eight straight edges would have total length
less than eight. Hence

\[
y^2<63/16.
\]

This excludes ray 4 at and above `63/16`, including equality. The earlier
`35/4` threshold is superseded. The shorter interval is unnecessary for
the fixed-target negative proof; it would matter to an affirmative
construction claiming coverage of the entire boundary.

This retires the inherited research-level geometric qualification for
ray 4. The direct Lean bridge and kernel-checked certificate assembly
remain open; this is not yet a Lean exclusion theorem.

The required sources are
[`final_polynomial.md`](../type7_focus/final_polynomial.md) and
[`cycle_thresholds.md`](../linking_checkpoint/cycle_thresholds.md).
The common-line limit and second blow-up analyses are no longer gates
to this ray-4 exclusion. Repeating them will not close rays 1–3.

## 4. Ray 3: completed eventual proof and finite-height certificates

### The system that must be decided

The basic generator
[`generate_remaining.py`](../type7_focus/generate_remaining.py) has
14 intrinsic coordinates, after fixing one vertex, and four unknown
nonedge squared distances: **18 real variables**. A positive definite
anchor Gram matrix and its completion equations encode rank-three
Euclidean realization. Strict nearest lifts and consistent intrinsic
face orientations with total double area `+2` or `-2` encode the marked
intrinsic triangulation. K4 determinants stay strict.

For ray 3 use
[`linked_metric.py`](../type7_closure/linked_metric.py), which additionally
retains:

- the actual degeneracy-complete intersection tests: 524 minimal affine
  circuit partitions, with positive distances covering the remaining
  28 vertex-pair tests;
- the necessary generic orientation completion and short-ring unlinking;
- **`|lk(0246,1357)|=2`** for the long rings.

Its current counts are 18 real variables, 312 Boolean variables, and
8,075 Boolean clauses, in addition to the real metric/circuit assertions.
The long-ring requirement follows from horizontal unlinking, the
discriminant-one linking form, and the disjoint-triangle linking bounds:
`q(m,n)=B*m*n+C*n^2`, `B=+/-1`, `C=0` or `B`, so
`|q(1,-2)|=2`.

Actual nonclique minors may vanish. Their auxiliary generic signs impose
weak real inequalities, while the full circuit conditions apply to the
actual coordinates. Replacing this arrangement by strict signs on all
70 minors would discard possible embeddings. Likewise, divisions in a
reconstruction must either have a proved nonzero denominator or retain
the zero-denominator branch.

### Mathematical target and useful route

The target is a theorem that these marked metric conditions and the
required linking force a prohibited simplex intersection, or another
contradiction to embedding. It must cover the *whole* localized phase.
The exact two-cap theorem is a useful starting point, but supplies only
the following necessary condition at `tau*`:

> At least one of eight projected cap-triangle areas or sixteen projected
> cross products of ring-edge pairs has magnitude at most `4*10^-10`.

This 24-way union includes zero. The new
[`relative cap bounds`](relative_cap_bounds.md) sharpen it uniformly,
including arbitrarily short cap edges. For every oriented short-ring
edge put `h_e=-X_e` and `gamma_e=y^2*V_e`. At every `y>=8` the proof gives

\[
0<h_e<\tfrac12,\qquad
|\gamma_e|<(\tfrac12+y^{-2})h_e,\qquad
\tfrac34h_e<|P E_e|<\tfrac{33}{32}h_e.
\]

The first estimate follows from eight exact cross-ring stress identities,
Cauchy's inequality, face orientation, and a maximum-slope bootstrap
using the stress row and column sums. An endpoint nearest-lift comparison
then proves `|axial(E_e)|<5*h_e/y`. No minimum edge length is assumed.
The earlier cap-order proof therefore strengthens to a relative union:
for at least one of the same 24 consecutive/cross-ring edge comparisons,

\[
|\det(P E_e,P E_f)|\le36h_eh_f/y^2,\qquad
|\sin\angle(P E_e,P E_f)|<64/y^2.
\]

At `tau*` the sine is less than `6.4*10^-11`. The remaining difficulty is
thus almost parallel or antiparallel projected **directions**, including
exactly parallel directions, rather than a small area explained only by
a vanishing edge. The entire angular region remains open. These estimates
do not assert that either cap is planar or that a K4 determinant has a
uniform positive lower bound.

The necessary union is now encoded by
[`projected_metric.py`](projected_metric.py) in the full system using
the correct metric coordinates. The numerical
threshold is for physical transverse coordinates about edge `02`, not
for arbitrary inner-product coordinates. If `e=r2-r0`, and `a,b` are
the relevant physical edge vectors, then

\[
\det(Pa,Pb)^2=
\frac{\det\operatorname{Gram}(e,a,b)}{\lVert e\rVert^2},
\]

where `P` is orthogonal projection perpendicular to `e`. The denominator
is positive. This converts the magnitude bound to a rational polynomial
inequality without introducing an assumed sign or dividing by a cap
area. The generator scales squared distances by `1/y^2`, so that scale
must also be restored before applying the bound. If `Q` is the
three-vector Gram determinant computed from those scaled inner products,
the exact polynomial condition is

\[
y^8 Q\le160000\,D_{02}.
\]

The generator also includes the stronger relative union
`y^8*Q <= 1296*D02*h_e^2*h_f^2` and the proved linear relative-slope
inequalities. Cap-triangle weights are taken from its two consecutive
ring edges, including when the original determinant uses a diagonal.
Both unions retain zero and use the already imposed `D02>0`. No assumed
lower bound for a cap area is added. The independent exact verifier checks the
projection identity and physical scaling, evaluates every emitted term
on rational configurations with a non-coordinate longitudinal axis, and
parses the full query. There are still 18 real variables, 312 Booleans,
8,075 Boolean clauses, and 524 circuit partitions; the augmented query
has 9,126 assertions. Before the relative inequalities were added, a
single 10,000 ms trial of the absolute-union system at `y=10^6` returned
solver-reported `UNKNOWN (timeout)`. **No system is excluded by this
implementation or trial.**

An alternative [`direct_metric.py`](direct_metric.py) chart now uses
physical transverse coordinates and rescaled cap heights: 27 real
variables and 19 metric equations of degree at most four. Four heights
are eliminated by exact anchor-distance subtraction. It preserves all
312 Booleans, 8,075 Boolean clauses, and 524 degeneracy-complete circuit
partitions, with the relative union and edge bounds above. The chart
normalization divides by no cap determinant or unknown edge length.
Exact reconstruction and all 322 emitted incidence minors are checked
against independent rational physical coordinates. Its 9,140-assertion
query at `tau*` returned `UNKNOWN (timeout)` in one 30,000 ms trial.

The alternative [face-023 chart](remaining_null_chart.md) reduces the
metric degree to **21 quadratic equations in 29 real variables**. Three
are exact differences of anchor distances. It also removes 24 implied
phase tests, cancels eight strictly positive incidence factors, and turns
six relative-area alternatives into linear inequalities. All actual zero
boundaries remain represented. An independent checker verifies the
physical metric, all 322 incidence minors, the factor identities, and the
two-arc nonedge reduction. This is a more tractable exact formulation;
it does not by itself exclude a chamber.

The [finite chamber compiler](solver_compilation.md) removes the repeated
Boolean search. Exact enumeration and an independently checked RUP trace
cover 1,888 generic sign completions. Blocking verified symmetry orbits
reduces the producer to 133 SAT checks and cuts measured enumeration time
from 7.61 to 1.83 seconds, with the same complete model set. The 16 marked
symmetries preserving the canonical phase give **132 metric chambers**.
Cofactor and Grassmann–Plücker implications prove 64–69 brackets nonzero,
leaving only **2–16** of the original 524 actual circuit tests per chamber.
Unproved nonclique zero boundaries remain, and the nonedge inequalities
reduce from 252 to eight.

Seventy-eight complete weak chambers are now excluded. Exact final
polynomials close **23 and 131**; a uniform metric volume comparison and
one affine identity close **129 and 130**. General raw-volume difference
certificates close **88, 91, 93, 95, 96, 97, 98, 99, and 100** by exact
weighted sums of metric inequalities and affine identities. All metric
certificates hold for every `y>=8`. Seventeen further chambers have
exact quadratic certificates, combining metric inequalities multiplied
by nonnegative raw brackets with affine cocycle products and GP identities.
Nine reference certificates are reused by exact coefficient checks under
marked symmetries. Independent finite product trees also cover two of
these cases for `y>=32`, with every branch and zero boundary checked.
The [smaller polynomial quotient](solver_metric_quotient.md) adds
forty-eight more exclusions. It reduces 2,485 raw quadratic products to
490 exact coordinates, cutting a matched discovery run from 22.01 to
1.34 seconds. Twenty-five stored universal identities cover 72 chambers
including overlaps. The independent replay expands them directly in
twenty-one point coordinates, checks integer cancellation, and proves
a positive K4 product; it trusts neither the discovery quotient nor LP
tolerances. Thus **54 of 132 metric chambers remain**. The manifest
records every proof and exports no query for an excluded case.
The [discovery producer](solver_metric_cone.md) makes this search
reproducible with bounded LP calls, exact active-basis reconstruction,
and mandatory independent replay before exporting a certificate packet.
The independent verifier binds the coverage CNF to the manifest and
replays all strictness witnesses, circuit omissions, and chamber
certificates. Representative nonlinear queries still returned `UNKNOWN`
at 3,000 ms. These chamber exclusions do not close the full marking
or change the fifteen-system ledger.

The [Boolean certificate runner](solver_cnf_certificates.md) makes the
directional proof workload substantially cheaper. It produces reusable
traces, deduplicates identical CNFs, and requires the existing independent
RUP checker to accept every step. A difficult 19,311-clause case fell from
107.634 seconds of independent exhaustive search to 0.381 seconds for
trace production plus independent replay in the measured workspace runs.
All seven split-cap formulas and both vertical-V endpoint formulas passed.
Proof-only replay needs no Z3 or numerical library; timeouts and rejected
traces are failures, never exclusions.

The [nonparallel-corner theorem](relative_cap_bounds.md#5-a-certified-exclusion-of-the-tested-nonparallel-two-stick-corner)
now excludes one complete asymptotic construction family: clusters
`014` and `236`, with tips `5` and `7` limiting to nonparallel transverse
directions, cannot occur along `y -> infinity` if the four collapsing
edges `01,14,23,36` remain comparable. The proof fixes the moving anchor
tetrahedron before taking the common edge scale, so that scale can be
arbitrarily smaller than `1/y^2`. Its 433-variable, 8,543-clause necessary
sign formula independently replays as **`UNSAT nodes 6137`**. This is a
checked exclusion of that family, not a fixed-`tau*` exclusion. Different
collapse rates and other cap limits remain; the fifteen-system ledger
is unchanged.

The [arbitrary-rate extension](exhaustive_nonparallel_corner.md) now
removes that comparability assumption for the same labeled nonparallel
two-stick limit. Its simplified proof needs only three Boolean certificates and one
strict signed-volume estimate. The B-cap edge scales are independent
in a necessary relaxation; in the sole remaining directional case,
`[0145]/(t*alpha*beta)` has a strictly positive limit. This contradicts
the embedding signs, uniformly at all relative collapse rates. The
proof no longer needs the former missing-edge `26` argument. It still
supplies no finite-height threshold and is not a whole ray-3 exclusion.

The [global cap-limit theorem](cap_limit.md), including its normalized
zero-base extension, and the [exhaustive cap-shape classification](exhaustive_cap_shapes.md)
prove that every unbounded ray-3 sequence has at least one cap lying
entirely on a line. The classification covers all 121 pairs of
noncollinear four-point shape classes, including coincident vertices.
The surviving trapezoids contradict an exact stress inequality; the
exceptional pair of out-and-back caps also contradicts that identity.

If both limiting caps are collinear, their lines must coincide. The
[exhaustive collinear-cap proof](exhaustive_collinear_caps.md) checks all
5,476 weak vertex-order pairs: 4,140 fail necessary orientation signs,
1,176 contradict the stress identity, and the remaining 160 reduce by
verified marked symmetries to two families. The arbitrary-rate corner
proof and twelve independently replayed Boolean certificates exclude
those families when their lines are nonparallel.

The [one-collinear-cap proof](remaining_one_collinear.md) excludes the
remaining mixed case. It covers 4,786 refined weak-order cells, uses
exact stress inequalities to reduce them to one cluster/out-and-back
family, and closes that family with 25 independent Boolean certificates
and a strict same-cap volume sign. All edge collapse rates are included.
The full 1,888-model coverage also has an independent replay.

Together these results prove: **every unbounded ray-3 sequence has both
limiting caps on one common line.** Common-line limits are now the
remaining asymptotic geometric gate. These results still give no finite
height threshold and do not exclude `ray3_phase0` at `tau*`.

The first common-line blow-up reductions are also exact. The
[full point-sign V/V proof](exhaustive_vv_geometry.md) excludes both
out-and-back alignments by unit propagation, even after an arbitrary
anisotropic stretch. A stress identity excludes trapezoids whose bases
have zero physical horizontal component. For the other base direction,
the [complete zero-cone check](common_line_trapezoids.md) proves that two
noncollinear stretched caps require a triple cluster and one tip in each
original physical cap.

The [positive-weight mixed blow-up proof](remaining_flat_blowup.md)
excludes all 24 one-flat/one-trapezoid cells with positive limiting edge
weights. It uses an exact planar metric family, a nonsingular 21-variable
Jacobian, and a positive bracket combination whose linear and cubic
metric terms are both strictly negative. This covers every ratio of
normal width to `1/y` or `1/y^2`.

The [global edge-collapse theorem](common_line_edge_collapse.md)
assembles all stretched-limit cases. The missing two-collinear case has
an exact 5,476-order cover; its 624 zero-stress survivors all have a zero
physical edge. Consequently **the minimum short-edge weight tends to
zero in every unbounded ray-3 sequence**. The remaining asymptotic
boundary necessarily contains a vanishing edge. No finite height
threshold follows yet, and all actual positive edge lengths must remain
allowed in the fixed-modulus system.

The [one-collapsed-edge mixed proof](remaining_adjacent_blowup.md)
excludes a further 48 common-line blow-up cells. The collinear cap has
exactly one collapsed edge and its noncollinear partner has four positive
physical weights. Necessary signs first compare the collapsed edge's
physical and stretched scales; a moving-frame height then forces the
wrong sign for its same-cap volume. Both steps allow arbitrary edge,
width, and height rates. The other 16 adjacent-collision cells have two
additional zero partner weights and remain outside this theorem.

The [two-line one-edge proof](remaining_two_line_blowup.md) excludes
all sixteen zero-stress order pairs with two collinear stretched caps
and exactly one zero physical edge. Its virtual-edge signs force a
direction and scale comparison; the uniquely determined metric heights
then contradict the same-cap bracket sign. The other 608 zero-stress
two-line orders have at least two zero short weights.

The [partner-collapse proof](remaining_partner_blowup.md) closes the
other 32 mixed cells with exactly one zero weight. Replacing the
collapsed edge's squared metric equation by a signed length defect
restores a nonsingular Jacobian. Exact defect bounds and negative
linear/cubic coefficients exclude every relative collapse rate.
Together, the complete one-zero covers strengthen the global theorem:
**the second-smallest short-edge weight tends to zero in every unbounded
ray-3 sequence**. The remaining boundary has at least two vanishing
short edges; a finite-height exclusion is still required.

The complete two-zero cover is also excluded. The
[double-partner proof](remaining_double_partner_blowup.md) covers all
24 mixed cells with four positive weights in the collinear cap and
two zero partner weights. A pair of signed length defects restores
a nonsingular metric Jacobian. When the cubic coefficient vanishes,
the exact edge metric supplies a stronger positive defect that still
forces a strictly negative bracket combination.

For two collinear stretched caps, the
[triple-cluster proof](remaining_two_line_triple.md) covers 288 orders
with a triple cluster and a positive-weight partner. Twenty-eight
independently replayed directional certificates leave one branch;
relative stress identities give moving height `-4*t*alpha` to leading
order and a prohibited same-cap volume sign. The earlier
[two-line proof](remaining_two_line_blowup.md#5-the-same-proof-excludes-32-paired-zero-orders)
also extends to 32 orders with collapsed edges 14 and 36. The
[split-pair proof](remaining_split_blowup.md) excludes sixteen more
orders by forcing a second-order negative displacement of the nonedge
26 and checking its independently normalized direction. The final
[paired-edge proof](exhaustive_two_single_blowup.md) excludes sixteen
orders with collapsed edges 14 and 67: the forced direction of 67
gives the wrong sign for its cap volume. These four families partition
all 352 two-line orders with exactly two zero weights.

The [complete mixed cluster proof](remaining_cluster_blowup.md) covers
the remaining 544 mixed two-zero cells. Its 61 canonical shapes and
three small-edge ratios give 183 cases. Necessary weak signs exclude
153 directly. Relative volume identities and two regularized metric
charts exclude the other thirty, including the zero limiting slope
boundary in the exceptional trapezoid. All 169 exported CNFs and all
symbolic metric identities have independent replays.

Consequently the global theorem now says **the third-smallest short-edge
weight tends to zero in every unbounded ray-3 sequence**. The complete
count checker verifies both the 568 mixed two-zero cells and the
disjoint 352-order two-line cover. The remaining common-line boundaries
have three or four zero weights. Every cap retains two positive weights,
and in fact the fifth-smallest of all eight weights is at least `1/6`.
This strengthens the asymptotic reduction; it does not yet close a
finite chamber or the full marking at the common target modulus.

The next layer now has a complete
[three-zero two-line exclusion](exhaustive_three_zero_blowup.md).
All 176 orders map to five triple-cluster families of 32 and one
split-pair family of sixteen. Sixteen direction certificates retain
every relative scale of the three small edges. The surviving cases
contradict exact cap-height limits `-4`, `+4`, or the positive B-cap
coefficient `u*(1-2u)`. All seventeen exported CNFs, including model
coverage, independently replay.

The mixed three-zero cover is now complete as well. The
[triple-cluster endpoint proof](remaining_three_cluster_blowup.md)
excludes all 304 cells with two zero collinear-cap weights and one
zero partner weight. A third independently normalized edge handles
coincident endpoints; six uniformly regularized metric charts handle
the remaining cases. Its 103 CNFs and symbolic identities independently
replay. An exact expanded reference family removes a defect whose
first-order coefficient vanishes, instead of discarding higher-order
terms. The [adjacent-collision proof](remaining_three_adjacent_blowup.md)
excludes the other sixteen mixed cells. Actual mixed-bracket inequalities
bound the A collision relative to the B cluster; the negative A-cap
sign then forces a positive B-cap determinant, contradicting its
required sign. Its new cap-sign implication replays in three nodes.

These complete covers strengthen the global result to **the fourth-smallest
short-edge weight tends to zero in every unbounded ray-3 sequence**.
Each limiting cap has exactly two zero weights and two weights equal
to one half. The fifth-smallest remains uniformly at least `1/6`.

All eighty two-line four-zero orders are also excluded. The
[two-triple-cluster proof](remaining_fourzero_blowup.md) covers 48 by
exact relative-height implications and 27 independent Boolean replays.
The [triple/split proof](remaining_fourzero_split.md) covers 32 by a
uniform comparison with an exact all-t metric family and a forced
second-order displacement of the nonedge 04. Its six finite formulas
independently replay. This completes every two-line order in the
624-order cover, including all edge coincidences.

The [complete mixed four-zero proof](exhaustive_four_cluster_blowup.md)
now excludes all 300 remaining mixed cells. Its 35 canonical shapes and
three edge-scale hierarchies give 73 direct contradictions, twelve more
virtual-edge contradictions, and twenty metric endpoint cases. Both V
endpoints and all four trapezoid corners have uniform analytic proofs,
including the exceptional zero-horizontal-projection branch. All 96
CNFs have independently checked RUP traces; the complete batch took
21.377 seconds, with four independently checked producer-order retries.

Finally, the [triangle-pair proof](remaining_two_triangles_blowup.md)
excludes all sixteen two-noncollinear zero-cone supports. The four shape
patterns map to one positive-height-ratio family. An exact all-t reference
and seven vanishing first derivatives give a uniform small-weight
identity. The required sign of one bracket then forces a positive sum
of those weights to be negligible compared with their maximum, a
contradiction. Both final CNFs and all exact identities replayed.

These results exhaust every nontrivial first normal blow-up. Therefore
**no unbounded ray-3 sequence exists**, and there is a common eventual
height bound for the entire marking. The
[consolidated proof](ray3_boundedness.md) records the complete partition
and the compactness-to-boundedness argument. The bound is not numerical;
the fixed target and Lean assembly remain separate gates.

The graph also admits at most two reconstruction candidates for fixed
intrinsic data, and the archived orientation argument strengthens this
to uniqueness from the 24 edge lengths under its stated premises.
These results can eliminate redundant mirror searches. They do not
reduce the continuous intrinsic domain to finitely many placements.

### Why this gate is hard, and what not to repeat

[`verify_metric3_uniform.py`](../type7_focus/verify_metric3_uniform.py)
certifies exact metric solutions for **every `y>=10^6`**. They satisfy
strict nearest lifts, oriented degree-one intrinsic faces, nonedge
contractions, all 70 nonzero brackets, strict local support, and mixed-side
tests. They nevertheless have twenty edge-face crossings and long-ring
linking zero. Therefore none of those metric/local-support conditions
alone can yield the required contradiction. The full embedding or
mandatory-linking information is indispensable.

Conversely, exact integer witnesses satisfy the orientation, all 691
disjoint-cycle linking checks, and qualitative separated-hull conditions
for the remaining markings. They are nonflat. Thus the successful
ray-4 final-polynomial method cannot simply be repeated after dropping
the metric.

The full ray-3 queries at `y=4` and `y=10^6` requested 300,000 ms from
libz3 but returned no result before external interruption. No SAT,
UNSAT, or solver-reported UNKNOWN outcome was obtained. A repeat must
introduce a justified new estimate, a certified domain reduction, or a
different proof-producing method; increasing the same timeout is not
the next milestone. A result at `y=4` is diagnostic only for this
`tau*` program unless the other markings are also covered at that modulus.

## 5. Remaining geometric gates: complete rays 1 and 2

The current route seeks eventual exclusions for both complete markings.
They would combine with the ray-3 and ray-4 bounds at one common height;
no comparison between `Y3` and `10^6` is needed. The fourteen finite-mask
systems at `tau*` remain an alternative route, with that comparison an
additional gate if they are used to finish the negative classification.

The [shared finite compiler](solver_remaining_compilation.md) now checks
all 18,080 necessary generic sign assignments. A finite-domain Boolean
backend reduces matched enumeration time from 121.338 to 3.951 seconds.
An independent RUP trace proves completeness; the separate verifier
replays 56,056 strictness deductions and every omitted actual circuit.
The finite gap-hull filters give 1,436 K4 branches per marking, each with
3–50 actual circuits and a weak decision diagram retaining every possible
zero bracket. The [face chart](solver_remaining_face.py) has 29 real
variables and 21 quadratic metric equations; all 28 marking/mask/anchor
rewrites and 322 minor identities independently check.

The [uniform axis compactification](exhaustive_remaining_axis.md) gives
a stronger global domain for asymptotic work. It is valid for every
`y>=32` in both markings, with no finite-mask assumption. Exact cocycle
gauges justify rotating a vertical step of size at least `1/8` onto edge
01. Common-neighbor polarization and the actual faces 346 and 356 bound
every transverse coordinate and axial correction. Six products of small
intrinsic increments remain explicit bounded variables; they are not
discarded at a limiting collision. This gives **38 bounded real
variables, 24 quadratic metric equations and six quadratic product
equations** at fixed height.

The [complete product-limit cover](exhaustive_remaining_locus.md) now
reduces every unbounded sequence to two closed geometric families.
All 64 zero-factor choices give six exact nearest-lift polygons; checked
marked dihedral gauges reduce these to a three-step component opposite
one half-step, or two pairs of consecutive steps. Five exact identities
retain the full algebraic product closure, including component
intersections. Every limit has two projected endpoint triangles of
perimeter one, with alternate triangles handling the exceptional
corners. This is an asymptotic cover, not a two-mask finite-height claim.

An [exact metric reducer](solver_remaining_limit.md) eliminates fourteen
linear correction variables from the full 29-row limit system. It gives
twelve projected identities on each component, with eleven at the two
exceptional corners. All 54 parameter strata and 642 polynomial
row-combination certificates independently check, including every
feasible vanishing pivot. The two canonical families each have a sparse
identity set valid on their whole closed parameter domain. This retains
global metric compatibility in twenty projected variables.

For the regular part of the first canonical family, the
[angular cover](exhaustive_c0_angles.md) has only eighteen patterns of
fifteen anchor cross products, together with three additional necessary
tetrahedron signs. All three coverage/sign CNFs independently replayed
in 0.465 seconds. Exact degenerate and regular metric witnesses show
that the anchor patterns alone cannot prove the proposed opposite
inequality to `T36<0`; the regular witness violates one of the added
signs. The bounded quadratic LP and PSD pilots produced no certificate.
Height endpoints and degenerate cap triangles are outside this regular
cover.
The [complete eighteen-cell compiler](exhaustive_c0_cells.md) now
retains all 669 cap-compatible generic models and all seventy actual
sign dependencies, including zeros. Its 36 coverage/sign CNFs passed
fresh independent replay in 2.858 seconds. All 72 marking/height/cell
query variants parsed and passed their exact binding checks.
The [strict metric-turn proof](exhaustive_c0_turning.md) reduces the
regular ray-1 cover from 669 to 202 generic models; its 36 complete
cover CNFs replayed in 2.744 seconds. On the equal-height diagonal,
it also supplies an actual strict determinant disjunction. Retaining
that disjunction permits [50 exact product certificates](exhaustive_c0_diagonal.md)
to exclude the entire regular diagonal. Their 496 rational-weighted
terms replayed in 0.351 seconds, and the additional complete-cover
CNF independently passed in 0.277 seconds. Positive projective
normalization covers every interior diagonal height.
The [height-order extension](remaining_c0_height_order.md) now excludes
the entire regular region `0<v<=u<1/2`. Its three middle angles have
sum less than pi: an exact degree-eight simplex and degree-(2,2)
Bernstein certificate checks 10,148 nonnegative coefficients and a
strict positive slack term. The five metric identities retain both
required product-scale syzygies; their seven source rows and the
polynomial certificate replayed in 1.705 seconds. Two
[conditional-sign CNFs](exhaustive_c0_height_order.md), independently
replayed in 0.279 seconds, provide the contrary orientations. The
remaining regular height order is `v>u`; its quantitative mixed-bracket
bounds are also recorded by that topological package. The
[collinear extension](exhaustive_c0_collinear.md) additionally excludes
two strict collinear orders in `u>=v`, with the opposite cap regular.
Other collinear-cap and height-endpoint C0 limits remain open.

The second canonical family has a separate
[fourteen-pattern regular cover](exhaustive_c1_angles.md), with 132
complete generic projections and two additional tetrahedron signs.
All six orientation/coverage/sign CNFs independently replayed in
0.605 seconds. Its [closed circle and dot identities](solver_remaining_c1_geometry.md)
retain the exceptional product scale and hold at every parameter
boundary. The [turning-angle proof](solver_remaining_c1_turning.md)
now excludes the entire regular C1 component for ray 1: the first
metric pair and cap angles force one strict orientation, while the
second metric pair and certified signs force the opposite orientation.
Its zero-deficit cases are treated directly. The
[collinear-cap package](solver_remaining_c1_collinear.md) and
[rank/height extension](solver_remaining_c1_collinear_rank.md) now
exclude every interior C1 limit with exactly one collinear cap,
including coincident vertices. Five weak-sign implications and three
negative-cap exclusions use actual bracket trits, exact height
identities, and checked marked symmetries. The
[two-collinear-cap classification](solver_remaining_c1_flat_limits.md)
leaves six explicit flat families, including all zero-edge endpoints.
Their full 29-row metric witnesses and six active nonedge inequalities
check exactly. The [normal-stretch proof](solver_remaining_c1_flat_stretch.md)
then excludes every family: all seventy determinants become linear
in five normal coordinates, and 560 projection identities per family
give uniform sign constraints. Exact multilinear coefficient signs
cover the entire height rectangle and every closed deficit interval.
All fourteen CNFs, with ten distinct proofs, independently replayed
in 1.383 seconds; a separate peer replay took 1.159 seconds. This
completes the research exclusion of interior C1 for ray 1. Height
endpoints and the full ray-2 marking remain open.

For regular C1 in either marking, the
[closed turning constraint](exhaustive_c1_holonomy.md) excludes an
additional full turn of the six linked-vector angles. Its two strict
disjunctions retain all zero cross-product boundaries. Thirty-two
exact polynomial certificates with 2,687 rational terms cover all
264 word/branch combinations; their replay took 0.812 seconds and
the four source CNFs independently passed in 0.479 seconds. This
is a necessary topology reduction for ray 2, not a metric exclusion;
retained numerical diagnostics demonstrate that the reduced anchor
conditions alone remain insufficient.

In the two-block `04` limit of ray 1, the
[focal-ellipse and weak-sign proof](remaining_ray1_mask04.md) forces all
eight transverse points onto one common line, with `h0=h4=1/2` and
three remaining closed weight families. It covers zero focal lengths,
collinear triples and collapsed edges while retaining both outer
product scales. All 52 direct Boolean certificates independently
replayed in 3.066 seconds.
The [first transverse stretch](remaining_ray1_mask04_blowup.md) now
excludes twenty of its 24 closed horizontal-order cases. Its weak-slope
encoding retains zero horizontal edges explicitly and makes no comparison
between the width, height parameter and collapsing edge lengths. All
twenty independent RUP certificates passed in 2.687 seconds. Only four
symmetric endpoints remain in this limit: one of `h1,h3,h5,h7` is zero
and all seven other horizontal weights equal one half.

At the canonical endpoint, [uniform relative metric identities](remaining_ray1_endpoint.md)
control the collapsing edge without comparing its scale to the height
or transverse width. A four-edge polarization bounds its vertical step
by its horizontal weight. The [virtual-edge package](solver_remaining_virtual12.md)
replays 426 exact Farkas certificates in 0.892 seconds, including 102
parameter-polynomial certificates valid on the entire open interval.
It reduces the normalized deficit simplex to three boundary regimes,
with 172, 38 and 15 compatible primary completions respectively.
All three are now excluded. The [negative-X proof](remaining_ray1_negative_x.md)
subtracts two exact face polarizations with incompatible limits. The
[nonedge15 cut](remaining_ray1_nonedge.md) excludes every negative
limit of the normalized vertical step. The
[positive-axial proof](remaining_ray1_positive_z.md) combines a relative
face027 Gram factorization, fifteen exact profile implications, and a
rank-one metric stress on clique3456. The
[consolidated theorem](ray1_two_block_exclusion.md) therefore closes
the entire two-block limit and all four symmetric endpoints. It gives
no numerical neighborhood or height threshold for a finite-target mask.

The [axis compiler](solver_remaining_axis.md) partitions the complete
common sign set into **268 branches per marking**, without a mask split.
Every branch preserves the full bounded metric prefix, shortest lifts,
intrinsic areas, nonedge contractions and all necessary incidence tests.
Independent replay checks the source hash, every group, its exact weak
diagram, and all 268 emitted ray-2 queries. The topology-only symmetry
group is used for Boolean enumeration; it does not quotient metric cases.

Three representative new axis queries, with 3, 18 and 50 retained
circuits, each returned `UNKNOWN` at a 3,000 ms limit. That diagnostic
stopped after the sample. The next step requires exact geometric or
algebraic certificates in the reduced domain, rather than unchanged
retries. No ray-1/2 mask or marking has yet been excluded.

Exact rational witnesses also show why a local-tetrahedron shortcut
cannot finish this step: both `04` masks satisfy every shortest-edge,
face-orientation and individual K4 positive-definiteness condition.
These are not global spatial realizations. Global metric compatibility
and embedding remain indispensable. The markings have different
Hamiltonian periods, `(-4,1)` and `(-3,1)`, and are not interchangeable.

A complete eventual exclusion must cover every limit and every relative
collapse rate in one marking. Alternatively, a finite-height proof must
cover all seven masks there. A reduction or partial certificate alone
does not close a marking.

## 6. Constructive alternative and pivot rules

An exact embedded witness at `tau*` immediately stops attempts to prove
that target impossible. First verify all edges, the lattice/face cover,
and every disjoint-simplex condition, including nongeneric intersections.
If a numerical candidate is strict, certify it by rational/algebraic
reconstruction or a rigorous interval existence argument before changing
the theorem ledger.

A constructive program then needs parameter families covering the full
sharp ray, with overlaps and endpoints checked, or a new impossible
modulus for the negative route. Local rank nine can support continuation
near a regular witness, but does not provide global continuation through
collapsing edges, vanishing separation, or loss of rank.

The existing positive-height trapezoid family cannot be rescued simply
by changing the lattice basis. The transformed sharp arc is
`w=2*x-x^2`; the exact proof in
[`type7_closure/README.md`](../type7_closure/README.md) excludes every
defined nondegenerate flat member of that parametrization with `H>0`,
across all its face-sign chambers. Its hypotheses include
`D=H-1+H*x!=0` and `D+r!=0`. It excludes this family, not all planar
foldings or all spatial constructions. A positive approach needs a
different family or a separately justified singular chart.

Change priority when there is new mathematical evidence: a certified
embedded witness, an actual complete-case contradiction, or a proof that
the chosen relaxation is feasible. A timeout, small numerical residual,
or a further degeneration condition is not such a decision. If the next
ray-3 attack yields only another necessary reduction, compare it with
the concrete Type 4 and Type 5 gates before funding another solver run;
there is no present basis for an unconditional ranking of completion time.

## 7. Geometric audit and Lean bridge

The [geometric audit](geometric_audit.md) supplies the research-level
necessity arguments and the full ray-4 hand proof. The finite certificates
do not yet give the requested Lean theorem. The following dependencies
must still be connected explicitly in Lean.

1. **Arbitrary realization to marked data.** Start from `Type7.Realizes`,
   extract coherent shortest edge lifts and a generating cocycle, then
   apply the existing winding candidate and symmetry theorems. The
   four-entry `representative_count` and `orbit_partition` theorems are
   already in Lean; their hypotheses must be obtained from the actual
   realization, with the archived label/gauge convention verified.
2. **Flat embedding to geometric premises.** Formalize the Type 7 strict
   neighbor-support, mixed-side, and K4-nondegeneracy implications. The
   research argument uses the spherical-link hemisphere lemma and the
   seven-vertex nonexistence/minimality argument. Existing Type 2 support
   proofs and general geometry utilities are useful components, but the
   Type 2 theorem cannot be relabeled without checking its graph-specific
   hypotheses. The audit now gives the Type 7 hand arguments, including
   deletion and retriangulation of a non-strictly-supported flat vertex;
   the corresponding Lean bridge is still required.
3. **Linking and generic perturbation.** Prove the torus linking-form
   facts, the linked-fiber diameter bound, and invariance under the small
   perturbations used for the necessary orientation formula. Perturbations
   need not preserve flatness; actual metric constraints must continue to
   concern the original placement. Formalize the cycle periods and the
   `63/16` inequality on those premises.
4. **Necessary finite systems and certificate soundness.** Formalize the
   seven-mask and phase localization, Gram representation, and full
   affine-circuit tests. Instantiate a kernel-checked checker for the
   Boolean coverage and final-polynomial certificates, reusing
   [`Certificates/ReverseUnitPropagation.lean`](../../OrigamiTorus/Certificates/ReverseUnitPropagation.lean)
   where applicable. Replay each new nonlinear exclusion with a proved
   checker or translate its analytic proof into Lean. Python, C++, and
   SMT solver exit statuses are research evidence, not Lean proof terms.
5. **Assemble the final theorem.** Dispatch all four markings at one
   common height, using explicit exclusions or their eventual bounds,
   prove the negated realization statement, expose the classification
   through the public library and solution wrapper, and build both
   default targets. No `sorry`, new axiom, or unproved certificate
   soundness assumption may stand in for a completion gate.

Ray 4's finite algebra and Boolean coverage can be formalized while
the ray-1/2 geometry is being completed. The ray-3 analytic proof also
requires its compactness and uniform-estimate bridges in Lean.

## 8. Reproduction and review commands

Run from the repository root with assertions enabled. These commands
check existing results or generate systems; none is advertised as an
automated completion proof.

```sh
node research/type7_focus/verify.cjs
node research/type7_focus/verify_remaining_markings.cjs
node research/type7_focus/verify_final_polynomial.cjs
python3 research/linking_checkpoint/verify_cycle_thresholds.py
python3 research/linking_checkpoint/verify_full_ring4.py
python3 research/type7_focus/verify_metric3_uniform.py
python3 research/type7_closure/verify_transformed_chart.py
```

The finite checks use Node/BigInt, Python, and—in the indicated metric
and SAT checks—SymPy, NumPy, and shared libz3. The independent cap proof
also has a C++17 replay:

```sh
python3 research/type7_focus/verify_cap_order.py /tmp/type7-cap-blocked.cnf
g++ -O3 -std=c++17 research/orientation_checkpoint/check_unsat.cpp -o /tmp/type7-check-unsat
/tmp/type7-check-unsat < /tmp/type7-cap-blocked.cnf
```

Check that the checker prints `UNSAT nodes 1027`. Its exit status is zero
for both SAT and UNSAT, so a successful process exit alone does not
verify the cap certificate.

Generate the current exact IDs and full ray-3 target without invoking a
solver:

```sh
python3 research/type7_focus/generate_remaining.py /tmp/type7-localized
python3 research/type7_closure/linked_metric.py /tmp/type7-ray3-full.smt2 1000000
python3 research/type7_completion/verify_projected_metric.py
python3 research/type7_completion/projected_metric.py /tmp/type7-ray3-projected.smt2 1000000
python3 research/type7_completion/verify_relative_cap_bounds.py
python3 research/type7_completion/verify_direct_metric.py
python3 research/type7_completion/direct_metric.py /tmp/type7-ray3-direct.smt2 1000000
python3 research/type7_completion/verify_nonparallel_corner.py /tmp/type7-nonparallel-corner.cnf
```

Replay the last formula with the same independent C++ checker used above:

```sh
/tmp/type7-check-unsat < /tmp/type7-nonparallel-corner.cnf
```

Its printed result must be `UNSAT nodes 6137`. The proof and exact scope
are in the relative-cap note; it does not close the fixed-modulus query.

For ray-4 independent RUP replay, use a scratch working directory and
follow the three-command producer/checker workflow in
[`final_polynomial.md`](../type7_focus/final_polynomial.md). Keep generated
CNF/proof traces outside the source tree. For the formal endpoint use the
repository's pinned toolchain and run `lake build`; successful research
script replay does not substitute for that build.

**Review endpoint:** ray 3 now has a complete eventual research exclusion.
The next marking closure requires a full ray-1 or ray-2 exclusion with
all premises discharged, at an explicit height or eventually. The final
classification requires a common counterexample height for all four
markings and the completed Lean bridge, or a complete positive construction.
