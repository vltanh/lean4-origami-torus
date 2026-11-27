# Type 7: roadmap to a complete classification

## Decision and first target

**The next Type 7 target is the entire `ray3_phase0` system at
`tau* = 1/2 + 10^6 i`.** A proof must cover every placement in that phase,
including arbitrarily small cap edges and coplanar nonclique quadruples.
Another necessary inequality, excluded construction family, or failed
solver run does not close this target.

Type 7 is a credible alternative to prioritizing Type 4. One of its four
sharp-ray markings now has an audited hand-proof exclusion, and ray 3 has
one localized phase with several exact coordinate formulations. Its reconstruction, symmetry,
and mandatory linking constraints are particularly concrete. A successful
ray-3 proof would close a second whole marking at the common modulus.
However, its metric relaxation is rigorously feasible, the full system has
already resisted an extended solver attempt, and fourteen ray-1/2 systems
would remain. **The evidence supports trying ray 3 next; it does not
establish that Type 7 is the fastest whole type to finish.** Raw branch
counts—15 for Type 7 versus 8 for Type 4—do not measure their difficulty.

This roadmap distinguishes three accomplishments: a research lemma, a
complete marking exclusion, and the final Lean classification. The
current checkpoint has not achieved the latter two for ray 3.

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

## 4. First completion gate: all of ray 3 at the common modulus

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

The next requirement is a contradiction across the remaining angular
region using the exact metric and required long-ring linking. An
acceptable exclusion is a hand inequality proof or an independently
checked finite algebraic/interval certificate covering the full domain,
including all boundaries. Auxiliary subcases are useful internally; the
ledger stays open until their union has been discharged.

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

## 5. After ray 3: finish both seven-mask unions

Retain `tau*`. The [remaining-marking generator](remaining_systems.md)
now supplies full necessary metric/embedding systems for all fourteen
ray-1/2 IDs, with their own cocycles and masks, twelve horizontal
unlinkings, all 524 actual circuit partitions, and the correctly retained
long-link magnitudes one or two. Each has 18 reals, 382 Booleans, and
8,305 Boolean clauses. The original basic fifteen-system generator
remains only a metric relaxation.

Exact rational witnesses show why a cheaper local-tetrahedron shortcut
cannot finish this step: both `04` masks satisfy every shortest-edge,
face-orientation, and individual K4 positive-definiteness condition.
These are not global spatial realizations. Global metric compatibility
and embedding must remain in the search.

For each marking, prove that every realization maps by a checked joint
marking/triangulation symmetry to one listed mask. Use the finite gap
and component-sum estimates to derive quantitative spatial consequences,
then combine them with the complete metric and embedding system. Do not
assume that the two markings are interchangeable because their mask lists
coincide. Their Hamiltonian periods are `(-4,1)` and `(-3,1)`.

The successful ray-3 mechanism should determine the next mask. If it
depends on a four-vertex cap at each end, `ray1_04` and `ray2_04` are
natural transfer tests: the two isolated large edges separate four-vertex
groups. This is a proposed order, not a proved equivalence or complexity
claim. A proof for `04` must still be followed by `03`, `014`, `015`,
`025`, `0125`, and `0145` in each marking, or by a uniform theorem
covering all seven.

Completion criteria are exact: seven of seven exclusions close ray 1;
seven of seven close ray 2; both, together with ray 3 and the audited
ray-4 theorem at the same modulus, close the negative classification.
No symmetry reduction or successful partial certificate is counted as
an excluded mask by itself.

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
5. **Assemble the final theorem.** Dispatch all four markings at `tau*`,
   prove the negated realization statement, expose the classification
   through the public library and solution wrapper, and build both
   default targets. No `sorry`, new axiom, or unproved certificate
   soundness assumption may stand in for a completion gate.

Ray 4's finite algebra and Boolean coverage can be formalized before
solving ray 3. That would retire a genuine formalization dependency, but
would not change the fifteen-system research count.

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

**Review endpoint:** the first progress entry that closes a currently
open Type 7 marking must be a full `ray3_phase0` exclusion at `tau*`
with its premises discharged, or a certified embedded realization that
changes the negative target. The next classification entry requires the
remaining fourteen systems as well and the completed Lean bridge.
