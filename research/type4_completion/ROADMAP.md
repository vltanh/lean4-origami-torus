# Type 4: roadmap from open-strip coverage to a complete classification

**Research status, 2026-11-27: open; 0/8 fixed-target cases excluded.**
This is an independent Type 4 workstream. It does not prescribe Type 4 as
the sole priority over Types 5 and 7, and it does not turn any of the
research reductions below into a new Lean theorem.

**Current attack:** [Gate 0 is complete as a hand-proof reduction](ray2_attack_coverage.md):
an arbitrary embedding at the target enters one of the eight full domains.
The [direct strict-geometry proof](global_attack_support.md)
now establishes neighbor support and all 23 strict K4 determinants from
Type 4 embeddedness and flatness, without the earlier seven-vertex
remeshing dependency. The [uniform ray-2 core reconstruction](ray2_attack_conics.md)
has two genuine phase quadratics at every sharp-ray modulus, including
all cap collapses. The proposed whole-six-core obstruction is **false**:
an [exact embedded core](core_attack.md) survives tilted C collapse.
Both of that core's metric completions by vertex 0 are nevertheless
excluded by an exact edge `12` / face `045` crossing certificate.
The active task is consequently a coupled core-and-leaf obstruction;
this fixed-core certificate is not a full-row exclusion.
The [new complete affine formulation](direct_metric.md) retains all eight
vertices and every degenerate intersection stratum with 26 variables and
polynomial degree at most four. Its strengthened `ray2_2` query returned
`UNKNOWN (timeout)` at 10,000 ms. All eight strengthened inputs regenerate;
no row is excluded and the new hand proofs are not yet assembled in Lean.

## 1. What would finish Type 4?

Existence is already settled. The remaining question is universality.
The Lean theorem `Type4.open_strip_realizes` in
[WideLift.lean](../../OrigamiTorus/Type4/WideLift.lean) covers every reduced
modulus `x+i*sqrt(w)` with `0<=x<1/2` and `w>=1-x^2`. Its regular version
also proves rank nine at the spatial realization. The missing reduced
locus is exactly

    tau=1/2+i*y, y>=sqrt(3)/2.

Either of two outcomes completes the classification:

| Outcome | Required mathematical result | Final assembly |
|---|---|---|
| Nonuniversality | One specified modulus with no embedded Type 4 realization, covering every marking at that same modulus | Combine the obstruction with existence/open-strip coverage and formalize the obstruction |
| Universality | Embedded, facewise-isometric Type 4 realizations on the entire missing sharp ray, including its hexagonal endpoint and arbitrarily large `y` | Combine boundary coverage with the existing open-strip theorem and lattice reduction |

The current obstruction target is `tau*=1/2+10^6 i`. A certified embedded
witness there would defeat this particular target. It would settle one
modulus, not the entire ray. Conversely, an obstruction to a particular
parametrized family does not exclude the triangulation.

## 2. Is Type 4 the best next problem?

There is no established ranking by difficulty of whole-type completion.
The numbers of cases are not comparable measures of difficulty: they
refer to different continuous domains and different reductions.

| Workstream | Concrete advantage | Main unresolved obstacle |
|---|---|---|
| Type 4 | Full open-strip theorem; two sharp-ray marking orbits; a special ray-2 four-edge winding cycle gives uniform phase, tube and relative-tilt bounds | None of the eight full fixed-target cases is closed; surviving cap collapses require a new argument combining the metric with actual embeddedness |
| Type 5 | Eight-parameter reconstruction; all fourteen hexagonal B1.1 weak chambers have complete embedding tests after exact strictness propagation | Both the reconstructed and compact exact metric queries remain undecided; much more than a missing boundary ray remains for a constructive universality proof |
| Type 7 | Full open-strip theorem; one elongated marking has a geometric obstruction; the remaining ray-3 target combines an entire marking with a forced long-ring linking number | Its continuous metric/linking systems remain undecided; fifteen archived branches across the three remaining markings are still open |

Types 4 and 7 both have later research proofs of uniqueness from the
24 labeled edge lengths, conditional on their recorded geometric
premises. Thus uniqueness is not a reason by itself to prefer Type 4.
Type 5's compact B1.1 formulation has 29 variables despite its underlying
eight-parameter reconstruction; a smaller parameter count does not imply
that a particular encoding is easier to solve.

The current comparative recommendation is to treat **Type 7 ray 3 as the
next whole-marking attempt**, while retaining **Type 4 ray2_2 as a focused
analytic case** with the stop conditions below. That is a choice of the
next concrete task, not a prediction that Type 7 will be the first whole
type completed. Type 4 should regain priority if its relative cap
identities produce an exact contradiction that survives all collapse
regimes. It should not retain priority solely because its ledger has
eight rows.

Comparison sources: [Type 5 weak chambers](../type5_closure/weak_chamber_reduction.md),
[Type 5 recorded exact attempts](../type5_closure/verification.txt),
[Type 7 reconstruction](../type7_focus/README.md),
[cycle thresholds](../linking_checkpoint/cycle_thresholds.md), and
[Type 7 metric/linking target](../type7_closure/README.md).

## 3. Proof baseline and dependencies

Keep three levels of evidence separate.

| Layer | Available result | Scope needed for completion |
|---|---|---|
| Lean baseline | Open-strip realization and regularity; shortest-edge winding bounds, cocycle generation and marking orbit enumeration; the general Type 4/7 reconstruction with fourteen intrinsic coordinates and at most 80 radical branches | The marking/reconstruction theorems take the documented coherent lifted-face data or marked distances as inputs; their conclusions must be connected to the exact final obstruction statement |
| Mathematical research reductions | Strict neighbor support and strict K4 premises; Type 4 four-neighbor lateration; finite two-gap localization; ray-2 phase/product bounds; linking restrictions | Audit and discharge every inherited premise, including the passage from an arbitrary realization to the marked fixed-target data; do not describe the new reductions as already Lean-verified |
| Exact finite checks | Maximal-cell enumeration, cap-side Boolean certificates, local Radon masks, symbolic identities and the explicit diagnostic witnesses | A replay establishes the stated identities or finite consequences; it does not prove the still-missing metric contradiction |

The authoritative formalization scope is
[docs/VERIFICATION.md](../../docs/VERIFICATION.md). Relevant formal files
include [ShortestWinding.lean](../../OrigamiTorus/Winding/ShortestWinding.lean),
[WindingOrbits.lean](../../OrigamiTorus/Winding/WindingOrbits.lean) and
[TetrahedralReconstruction.lean](../../OrigamiTorus/Geometry/TetrahedralReconstruction.lean).
The stronger unbranched Type 4 lateration argument is a research result
in [the Type 4 ledger, section 16](../type4_focus/README.md#16-all-type-4-edge-length-uniqueness-independent-of-h13-signs),
not a replacement claim about what that Lean reconstruction already proves.

The exact Type 4 face list throughout this workstream is

    012 031 024 053 045 152 134 146 165 264 257 276 374 356 367 475.

Type 6 has the same degree sequence as Type 4 and a different face graph.
A Type 6 construction cannot be transferred by identifying the degree
sequences; any transfer must prove the actual flips and relabeling.

## 4. The common finite target and all eight stable case IDs

Set `y=10^6`, `W=y^2`, `epsilon=1/1000`, and gauge the universal vertex
`4` to zero. The finite two-gap theorem supplies cap centers separated by
normalized vertical distance in `(119/250,131/250)`. Cap hulls are more
than `11y/25` apart. The checked closed-cell cover broadens both strips
to retain adjacent cap endpoints; its rows may overlap.

The counts are 56/9 relative cells, 10/4 maximal cells and 6/2 symmetry
representatives for ray 1/ray 2. The following IDs, labels and integer
lifts are those of [type4_gap_enum.py](../type4_focus/type4_gap_enum.py).
Labels and lifts are in vertex order `0,...,7`.

| Work order | ID | Labels | Integer lifts `q` | Designated cap cycles |
|---:|---|---|---|---|
| 1 | `ray2_2` | `20220012` | `(0,0,0,-1,0,0,0,-1)` | `145 / 0273`; vertex 6 in the broadened strip |
| 2 | `ray2_1` | `12220002` | `(0,-1,0,-1,0,0,0,-1)` | `456 / 1273`; equivalent to `145 / 0263` |
| 3 | `ray1_1` | `00120212` | `(0,0,0,-1,0,-1,0,-1)` | `014 / 357` |
| 4 | `ray1_2` | `00130222` | `(0,0,0,-1,0,-1,0,-1)` | `014 / 567` |
| 5 | `ray1_3` | `00230223` | `(0,0,0,-1,0,-1,0,-1)` | `014 / 256` |
| 6 | `ray1_4` | `01200223` | `(0,0,0,0,0,-1,0,-1)` | `034 / 256` |
| 7 | `ray1_5` | `02200323` | `(0,0,0,0,0,-1,0,-1)` | `034 / 126` |
| 8 | `ray1_6` | `12200023` | `(0,0,0,0,0,0,0,-1)` | `345 / 126` |

All eight rows are open. The `ray2_1` cap change uses the checked
automorphism `(7,6,2,3,5,4,1,0)` and its marking action. Transferring a
proof to that row requires transporting its full hypotheses, including
the lifts and weak endpoint conditions, rather than just renaming cap
sets. The audit is in [linking_audit.md](linking_audit.md).

### Encoding counts: do not conflate parameters and auxiliary variables

| Formulation | Real unknowns | Role |
|---|---:|---|
| Global rational lateration | 14 intrinsic coordinates | Four reconstructed radial equalities and two further edge equalities, plus full validation; denominators require strict anchor checks |
| Natural fixed-metric Gram description | 18 = 14 intrinsic + 4 missing chord quantities | An alternative determinant formulation; this is not the variable count of the active cubic generator |
| Original Type 4 signed-Gram generator | 23 = 14 intrinsic + 4 missing slacks + 5 positive-complement variables | Fifteen cubic metric equations; the full incidence constraints have higher degree |
| Complete affine-anchor generator | 26 = 14 intrinsic + 12 affine coordinates | Ten cubic and eight quartic metric equations; complete cubic intersection/support cuts; all polynomial degrees at most four |
| Historical hexagonal H13 angular system | 19 = 14 intrinsic + 5 radicals | One sign branch at a different modulus; not the complete elongated target |
| Historical H13 universal-edge system | 22 = 14 intrinsic + 8 transverse coefficients | Another formulation of that sign branch; not an eight-case cover |

The active full generator produces 865 assertions per ray-1 row and
890 per ray-2 row, including 546 degeneracy-aware disjoint-simplex
exclusions. Omitting `--full` gives necessary constraints whose satisfying
assignments need not be embedded. Cubic metric equations do not make the
entire formula cubic. See [fixed_metric.md](../type4_focus/fixed_metric.md)
for the signed-Gram inertia argument and exact circuit interpretation.

## 5. Ordered gates for the obstruction route

### Gate 0 — make the final implication explicit

**Status: complete at the mathematical research level.** The
[assembled coverage proof](ray2_attack_coverage.md) supplies the implication
below, including the geometric inputs to the existing Lean marking
theorems. Its final Lean packaging remains outstanding.

**Inputs:** the formal baseline, the general eight-vertex two-gap theorem
in [the finite localization proof](../type5_focus/fixed_elongated/README.md),
the Type 4 marking lists, strict support/K4 hypotheses, and the finite
cell/symmetry checker.

**Required output:** one auditable implication from an arbitrary embedded
Type 4 realization of `tau*` to a solution in at least one of the eight
full case domains. Record exactly which parts are formalized and which
remain mathematical proof obligations. A normalization must preserve
the metric and the marking up to its stated lattice symmetry and gauge.

**Closed criterion:** all normalization, coverage, strictness and boundary
steps of that implication are proved. Replaying a finite enumeration is
only the finite part of this gate. This audit can run in parallel with
the analytic work; it must be complete before a final nonuniversality claim.

The strictness part has a [direct Type 4 hand proof](global_attack_support.md):
the finite checker verifies all eight neighborhood K5 witnesses and all
twenty possible nonedge antipodal-link cases. It supplies strict support
and strict K4s uniformly, including arbitrarily small positive volumes.
The extraction, shortestness, marking, localization, closed-cell transport
and auxiliary-variable steps are supplied in the assembled coverage proof.
Together these close the hand-proof gate; its Lean formalization remains
outstanding.

### Gate 1 — use one authoritative full domain per row

**Status: complete as an exact research encoding.** The
[affine-anchor formulation](direct_metric.md) preserves the baseline
constraints and replaces the metric and incidence expressions by an
equivalent full domain. Its independent checker verifies both marking
factorizations, the emitted metric equations, all polynomial degree
bounds, and minimal circuits of support two through five. All eight
strengthened full inputs regenerate. This is an encoding result;
real feasibility of every row remains undecided.

**Inputs:** the checked marking and `(labels,q)` row, fixed `W=10^12`,
strict shortest lifts, coherent nondegenerate intrinsic faces and degree
one, positive-definite strict clique metrics, nonedge contraction bounds,
and all minimal affine-circuit exclusions.

**Required output:** a reproducible exact domain, either the existing
23-variable signed-Gram formula or a proved equivalent chart.
Any elimination must retain its denominator sign conditions and show
that every original solution has an image in the reduced domain.

**Closed criterion:** an exact equivalence/necessary-reduction proof and
successful regeneration. This is an encoding gate, not a case exclusion.
Do not add an unproved sidedness conjecture as an assumption.

### Gate 2 — resolve the actual `ray2_2` collapse obstruction

**Available inputs:** the global [ray-2 phase/tube proof](../type4_focus/ray2_exact_phase.md),
the product inequalities in [fixed_metric.md](../type4_focus/fixed_metric.md),
the [cap identities](ray2_2_geometry.md), the [local core sign gates](core_signs.md),
and all actual face nonintersection conditions.

Write `p5=(-s,T/y)`, `p1=(a,R/y)` and

    A=a+s-1/2, B=1/2-a, C=1/2-s,
    A,B,C>0, A+B+C=1/2.

The exact cap Gram identity and three vertex-to-opposite-edge identities
retain these small margins together with the vertical tilt. They avoid
assuming a lower bound on the cap area. The two K5 cores give

    lambda6(2)<0  => lambda4(2)>0,
    lambda6(3)<0  => lambda5(3)>0.

A useful proposed metric target is a contrary implication for one of
these signs. **No such implication is currently proved.** In particular,
`lambda6(2)<0 => lambda4(2)<0` cannot be promoted from the tested anchors
to all A/B/C corners or all vertex-6 positions. Proving one of these
conditional signs would itself be an intermediate lemma, not yet the
full `ray2_2` exclusion.

**Resolved local question:** the whole-six-core exclusion is false.
The [exact tilted-C witness](core_attack.md) satisfies all fourteen core
edge equations, strictly shortest lifts, six coherent intrinsic faces,
strict core support, all strict K4s, chord `23` contraction and every core
simplex intersection test. Its cap margin is `C=1/(4W)` and vertex 6 is
within `21/(64y)` of the opposite cap. Both root masks are `{1}`. This
does not refute the narrower negative-`lambda6` implication above, whose
antecedent is false in the witness.

**Next decisive task:** include the degree-five leaves 0 and 7 from the
start. The [uniform core chart](ray2_attack_conics.md) gives at most four
core candidates per eight-parameter input; its phase quadratic leading
coefficients are positive on the whole sharp ray and exceed `4/5` for
`y>=1`. For the displayed exact core, an invertible polarized system
reduces every metric placement of vertex 0 to one quadratic. **Both**
roots force edge `12` through face `045`, so no placement of vertex 7
can complete that core to an embedding. The next required theorem must
establish an extension obstruction uniformly over the full parameter
domain, including exceptional leaf charts and cap endpoints. Neither
this isolated core nor its two excluded completions changes the row count.

**Stop/pivot conditions:**

- An exact core counterexample satisfying the full hypotheses of the
  proposed local lemma ends that lemma. Move to a coupled statement
  involving leaves 0/7 or a different cap, and record the counterexample
  so the same claim is not tried again. It does not refute `tau*` unless
  a full embedded torus is certified.
- If a proposed proof divides by a cap quantity with no relative lower
  bound, or only controls a subsequential nondegenerate limit, stop that
  proof at the missing bound. Use the exact identities to reformulate
  it; do not call the full case closed.
- A solver timeout without a changed mathematical reduction is not a
  reason to launch the same formula with successively larger limits.
- A proved local lemma earns a direct attempt at the full finite
  contradiction, including the quadrilateral cap. It does not justify
  expanding the orientation ledger into more unsupported branches.

**Closed criterion for the row:** an exact contradiction on its entire
finite domain, or a replayable exact infeasibility certificate for the
whole full formula. A full exact embedded witness instead closes the
feasibility question positively and invalidates this obstruction target.
The existing four cap-side certificates apply to a nondegenerate
transverse-limit regime; a new argument must provide the finite and
degenerate bridge before using them as a row exclusion.

### Gate 3 — finish the second marking at the same modulus

**Inputs:** any theorem proved for the entire second marking, the
`ray2_1` domain, and its checked cap relabeling.

**Required output:** a full exclusion of `ray2_1`, including its endpoint
and collapse configurations. Reuse genuinely marking-wide phase and
product estimates; reprove hypotheses that depended on cap `0273`.

**Closed criterion:** both `ray2_1` and `ray2_2` excluded at `tau*`.
Closing only the second marking does not prove nonuniversality.

### Gate 4 — finish all six first-marking rows

Work first through the shared cap `014` (`ray1_1`–`ray1_3`), then the
shared cap `034` (`ray1_4`–`ray1_5`), then `ray1_6`, unless a new proved
lemma gives a better order. The ray-2 four-cycle phase identities cannot
be assumed for ray 1. Each transfer must check its winding periods.

**Required output:** an exclusion theorem/certificate covering each
canonical row, with the quantitative constants valid at the same `y`.
If the common modulus changes, revalidate every previously used row
theorem at the replacement value or prove a common range.

**Closed criterion:** all six ray-1 rows and both ray-2 rows excluded at
one common modulus. A contradiction for an isolated hexagonal H13 sign
branch is not a substitute for any row in this ledger.

### Gate 5 — assemble, audit and formalize

Combine Gate 0 with the eight row exclusions. Audit all label changes,
strict-versus-weak premises, and certificate input hashes. Formalize the
new geometric bridges and exact algebra/certificate replay, then prove
the final nonuniversality statement in Lean. Run the repository build
and Comparator. Update the public status only to the level actually
proved; a hand proof or external exact certificate is not automatically
a new kernel-checked theorem.

## 6. Boundary coverage that every full-row proof must preserve

The finite cover includes all of the following:

- cap-center bounds and broadened-strip endpoints, including vertex 6
  approaching either cap or remaining at an intermediate scale;
- arbitrarily small A, B or C, simultaneous small margins, shrinking
  edge 45, and cap area tending to zero with independent vertical tilt;
- a collinear transverse limit of triangle 145, a collinear transverse
  limit of quadrilateral 0273, and shrinking quadrilateral edges,
  including 27/37 in the regime identified by the cap certificates;
- nonclique coplanarities, zero nonedge deficits and lower-support
  affine circuits. Strict K4 determinants do not permit declaring all
  seventy affine determinants nonzero.

Finite clique triangles/tetrahedra remain nondegenerate under their
stated strict premises. The missing issue is the lack of a uniform
positive lower bound, not permission to erase those premises. Weak
nonclique tests and the complete circuit exclusions must survive any
limit or algebraic elimination.

## 7. Alternatives and work that should not be repeated

### Alternative first cases and constructive route

`ray2_2` is selected because it has the strongest exact metric identities
and existing cap-side certificates, not because it is known to be the
easiest row. `ray2_1` is the natural alternative if a new lemma applies
to cap `0263` but fails for `0273`. A ray-1 row is a reasonable new first
case only with a specific transferable metric obstruction.

The hexagonal H13 problem is a different finite target: the hexagonal
metric has 31 joint marking/orientation classes, all still open. Its
singleton Boolean model is realized by an actual nonflat embedded
configuration, and its strongest recorded exact queries are undecided.
Its small sign count is not by itself a reason to restart it.

A constructive pivot should start with a genuinely new family or a
proved sequence of convex flips from a known universal triangulation.
It must preserve the Type 4 face list, certify embeddedness and all
marked edge lengths, establish the degree-one intrinsic quotient, and
cover `y>=sqrt(3)/2`. If inflation is used, prove the required rank and
fixed-period statement on the whole parameter range, treating the
hexagonal endpoint and the unbounded end explicitly.

### Recorded dead ends and feasible relaxations

| Tempting shortcut | Established limitation | What would justify reopening it? |
|---|---|---|
| Pure orientation, linking and qualitative cap separation | Exact nonflat embedded witnesses satisfy both allowed linking forms and the active cap ordering | A new quantitative consequence of the flat metric |
| Metric-only positivity of `[4512][4513]` | An exact six-vertex core has opposite signs while satisfying its edge metrics, shortest lifts, face orientations and tested chord contractions; edge 15 pierces face 264 | Actual core nonintersection or a stronger coupled theorem |
| Exclusion using only the embedded six-vertex core | An exact tilted-C core satisfies every local metric, support and embedding test; both of its vertex-0 extensions fail | A coupled argument retaining the leaves or other full-torus constraints |
| H13 intrinsic angular relaxation | An exact relaxed witness satisfies it but violates the required signs and has crossings | An equivalent full formulation or a proved new inequality |
| Existing trapezoid family after modular transformation | The transformed sharp arc has no nondegenerate flat member of the defined positive-H parametrization, including all its sign chambers | A different family or a rigorously different singular chart |
| Numerical endpoint continuation or random flip searches | No strict sharp-ray witness was certified | A candidate with exact validation or an analytic family, not more unchecked samples |
| Nondegenerate transverse cap certificates alone | They force the surviving limits into collapsed-cap regimes | A finite, scale-sensitive treatment of those regimes |

Sources: [linking audit](linking_audit.md), [exact metric-core diagnostic](algebra.md),
[embedded core and exhaustive leaf obstruction](core_attack.md),
[H13 ledger](../type4_focus/README.md), [transformed-chart theorem](../type7_closure/README.md),
and [cap degeneration proof](../type4_focus/elongated_hand.md).

The eight full 23-variable fixed-target systems previously returned
UNKNOWN at 5-second solver limits. The 19-variable full H13 and
22-variable Gram follow-ups were also subjected to 300-second internal
limits with 330-second external watchdogs; both ended by external timeout
without a SAT/UNSAT return. These are attempt records, not exclusions or
complexity bounds. Distinguish solver-reported UNKNOWN from an interrupted
process, and obtain an inspectable exact certificate for any future
claimed UNSAT result.

## 8. Reproduction and review gates

Run from the repository root with Python assertions enabled and SymPy
available. These commands replay the focused evidence; they do not solve
the open case.

```sh
python3 research/type4_focus/type4_gap_enum.py
python3 research/type4_focus/verify_cap_degeneracy.py
python3 research/type4_completion/verify_ray2_2_geometry.py
python3 research/type4_completion/core_signs.py
python3 research/type4_completion/algebra_core_witness.py
python3 research/type4_completion/linking_witness.py
python3 research/type4_completion/global_attack_support.py
python3 research/type4_completion/ray2_attack_verify_conics.py
python3 research/type4_completion/core_attack_witness.py
python3 research/type4_completion/core_attack_leaf.py
python3 research/type4_completion/direct_metric_check.py
```

Regenerate the active complete input, then all eight if a change affects
their common generator:

```sh
python3 research/type4_focus/type4_fixed_cubic.py /tmp/type4-ray2_2 --case ray2_2 --full
python3 research/type4_focus/type4_fixed_cubic.py /tmp/type4-all-full --full
```

The first command should report 23 real variables and 890 assertions.
The complete quartic formulation is the current input for coupled
core-and-leaf work:

```sh
python3 research/type4_completion/direct_metric.py /tmp/type4-ray2-quartic.smt2 --case ray2_2 --mixed-faces
```

This reports 26 real variables and 2,845 assertions. The exact input hash,
solver version and the recorded 10,000 ms `UNKNOWN (timeout)` result are
in [direct_metric.md](direct_metric.md). All eight choices of `--case`
were regenerated with the same complete cuts; the six ray-1 rows have
2,820 assertions each, and the two ray-2 rows have 2,845 each.

Record generator revision, command, input hash, solver version, actual
termination reason and independent certificate-checking output with each
new exact attempt. For SAT, reconstruct all eight spatial vertices and
validate the full intrinsic and extrinsic realization. For UNSAT, check
the certificate against the whole stated domain rather than a selected
generic or bounded-away-from-degeneracy subdomain.

For a proposed new formal result, use the pinned Lean/mathlib toolchain
(`v4.36.0` at this checkpoint):

```sh
lake build
lake env lake comparator --config=palomar/OrigamiTorus/comparator.json
```

These research proofs and exact checks add no full-row exclusion or Lean
theorem. The next change to the completion count must be a full-row proof
or a certified embedded witness, with the resulting target or priority
decision recorded explicitly.
