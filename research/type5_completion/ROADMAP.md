# Type 5: completion roadmap

**Status: universality open; 0/19 elongated cells excluded; hexagonal B1.1 remains 0/14 excluded.**

This research workstream is on `research/type5-completion`, based on
`research/origami-torus-checkpoint`; it does not change the formal release
on `main`. Its first target is the
**entire F1 block at `tau = 1/2 + 10^6 i`**, including its five finite cells.
The other three blocks and the exact assembly gate are specified below.
The hexagonal investigation is an alternative target, with a separate ledger.

## Current attack checkpoint — 2026-11-27

The exclusion count remains **0/19**, including **0/5 in F1**. The following
steps have been checked against the actual source revision rather than
transcribed inputs:

- [`verify_coverage.py`](verify_coverage.py) independently regenerates the
  36-cell / 19-representative cover and its full F1--F4 memberships. The
  source-pinned [`coverage.json`](coverage.json) agrees with the Lean faces,
  sharp marking, and all 24 edge shifts.
- [`coverage.md`](coverage.md) supplies the Type 5 finite incidences for the
  generic flat-link arguments: 21 antipodal obstructions, eight K5 star
  witnesses, and 23 nondegenerate K4s. Mathematically this discharges the
  inherited strict-support/K4 premise; a Type 5 Lean instantiation remains.
  It also proves that all triples except `067` are noncollinear and that at
  most one lattice lift of a missing edge can saturate metric contraction.
  [`coverage_constraints.py`](coverage_constraints.py) adds the resulting
  165 strict inequalities without fixing a continuous parameter or imposing
  a numerical lower margin. All pass the exact square construction.
- [`f1_geometry.md`](f1_geometry.md) gives a division-free cap identity.
  If the three horizontal short-edge margins are `u1,u2,u3`, the physical
  cap Gram determinant satisfies `det(B) >= u1*u2*u3/4 > 0`. Its closed
  boundary has exactly the three explicit kernel formulas in that note.
  [`f1_geometry_verify.py`](f1_geometry_verify.py) checks the identities and
  their substitutions for both caps in all five F1 cells. This controls
  where collapse can occur; it does not exclude that collapse regime.
- The primary algebraic model is now
  [`f1_algebra_projective.py`](f1_algebra_projective.py), justified in
  [`f1_algebra_projective.md`](f1_algebra_projective.md). Two bounded ratio
  charts each use **15 variables and seven metric equations**, replacing
  the 23-variable / 15-equation signed-Gram model. A cofactor identity
  proves that all eliminated denominators are nonzero on actual embeddings.
  `--cell F1` retains the complete five-cell disjunction with common variables.
  Three fixed Gram coordinates replace the five-coordinate incidence model;
  the sign of the sole remaining incidence denominator is handled explicitly.
  The complete tests include 21 new cyclic cubic inequalities and 233
  strict-support circuit exclusions. No cap-area lower constant or generic
  nonclique sign is assumed.
- [`f1_algebra_verify.py`](f1_algebra_verify.py) checks both ratio charts,
  elimination and reconstruction identities, the full five-cell conversion,
  circuit coverage and signed denominators, and compatibility of all 233
  support tests with the existing exact square embedding. The recorded
  verifier and solver results are in [`verification.json`](verification.json).
  All completed whole-F1 solver probes remain `UNKNOWN`. The final queries
  each contain 15 variables, 1,027 assertions, and 432,623 bytes; explicit
  `qfnra-nlsat` with factoring disabled returned `UNKNOWN (canceled)` in
  both charts at a 60,000 ms timeout. Neither chart nor any full cell has
  an infeasibility certificate.

The remaining geometric assembly includes extraction of lifted-face data
and formalization of the quantitative two-gap localization. The next proof
gate remains a contradiction or a full witness for the complete F1 union,
with every cap-margin boundary retained.

## Geometric continuation — 2026-11-27

The active direction is now a geometric proof. The algebraic systems remain
reproducible baselines; this checkpoint adds no new solver experiment.
**The counts remain 0/5 F1 and 0/19 elongated cells excluded.**

- **An actual embedded octahedron.** The disjoint cap hulls `014` and `356`
  cap the six-face annulus to an embedded sphere. The hand proof in
  [`f1_geometry.md`, §§7–8](f1_geometry.md#7-cutting-along-the-caps) is valid
  for arbitrarily thin caps and coplanar side-face configurations. The
  other annulus has a combinatorial five-K4 tetrahedron chain; a spatial
  nonoverlapping tetrahedral filling is not assumed.
- **A hand visibility obstruction.**
  [`exposed_caps.md`](exposed_caps.md) proves that the two cap planes cannot
  both support the seven-vertex set `0,1,2,3,4,5,6`, even weakly. The proof
  sends the strictly supported vertex 2 to infinity, derives a convex
  hexagon from the four visible corner fans, and forces the actual faces
  `035` and `146` to intersect by reversal of height order. It needs no
  orientation archive, linking constraint, metric, or vertex 7. This
  replaces the earlier finite sign obstruction in the exposed-cap regime
  with a self-contained geometric proof.
- **Three complete geometric positions.** The open edge `15` is exterior
  to that sphere, or it is interior with `25` piercing cap `014`, or with
  `12` piercing cap `356`. The last two alternatives are mutually exclusive.
  An entry propagates across the entire opposite-cap fan and gives strict
  nesting under central projection from vertex 2.
- **A metric restriction without an area denominator.** The first entry
  requires `v2<2001`; the second requires `v2>v5-2001`, where `v5>474000`.
  Thus the entire middle phase interval is exterior. The second entry is
  impossible in the three F1 cells where vertex 2 is in the first cap.
  These are restrictions on the three geometric positions, not exclusions
  of the underlying cells.
- **A global positive leaf-completion theorem.**
  [`leaf_geometry.md`](leaf_geometry.md) proves that any five-point core
  in `R^(3,2)` with positive weighted-five-cycle deficits has exactly two
  real local leaf completions, related by reflection. A saturated root lift
  in an embedded realization gives a single tangent completion, and at most
  one of the three hinges `05,16,27` can be unfolded. Both the intrinsic
  and spatial leaf coordinates vary in this statement; the candidates are
  not automatically embedded torus vertices.

The next whole-F1 argument must exclude the exterior position and the two
remaining cap-entry boundary regimes, using the selected leaves jointly.
In every such realization at least one cap plane must cut the other
vertices. The visibility theorem does not itself exclude these cutting-cap
configurations or prove that an arbitrary cap is exposed.
It must retain small positive margins: nondegeneracy and a spacelike
reflection direction do not give a uniform separation from collapse or
tangency. The new hand proofs and their exact finite/algebraic checks do
not supply the final contradiction or a compiled Lean theorem.

## Planar construction alternative — 2026-11-27

**Complete exclusion of one construction family, not of the hexagonal modulus.** At the hexagon the full three-parameter source family with positively oriented intrinsic triangles has no embedded Type 5 vertical lift after the two convex flips. All seven generic projected order patterns are closed: six by negative height-sign cycles and one by an exact positive five-inequality dependence. Rational Bernstein checks prove the fixed signs and cofactor weights uniformly. Nongeneric points follow by openness. The entire convex-flip graph has only three states in every pattern, so changing the flip order cannot rescue this family. See [proof](planar_flip.md) and [exact verifier](verify_planar_flip.py). The original elongated cell count is unchanged (0/19). Other folding patterns and nonplanar realizations remain open. No Lean source changes or new Lean theorem.

## General planar-pattern reduction — 2026-11-27

The new [proof and ledger](planar_patterns.md) enumerates the entire regular planar inflation route at the hexagonal marking, not just the two-flip family. An exact necessary-condition screen reduces 32,768 masks (global sign reversal identified) to 448 masks / 82 symmetry classes. Six complete three-parameter classes (33 masks) are excluded by uniform negative height-sign cycles, including a forced coincident projected pair. **415 masks / 76 classes remain.** See [screen verifier](verify_planar_patterns.py) and [family verifier](verify_planar_families.py); the latter prints the remaining ledger. The corrected intrinsic orientation is -2 for the recorded marking. No regular embedded lift has been constructed. This does not exclude nonregular or nonplanar embeddings; the elongated 0/19 count and full hexagonal status are unchanged.

## Saturated-route obstruction — 2026-11-27

The [geometric saturated-route theorem](saturated_routes.md) characterizes distance-preserving intrinsic lifts of a regular mixed-star planar folding: they must come from an unfolded face component or a straight degree-two crease chain. At the hexagon, fourteen complete remaining classes (72 masks) have an unlisted lift forced to tie a known route by a sum of only two to four shortest inequalities, all with coefficient one. The [standard-library integer verifier](verify_saturated_routes.py) checks every certificate and symmetry orbit. **62 classes / 343 masks remain** in the regular planar ledger. The earlier six geometric exclusions are not double-counted. This does not settle arbitrary spatial embeddings or the elongated cells; no Lean theorem is added.

## 1. What would finish Type 5?

Existence is already established. The remaining question has two possible
resolutions:

1. **Universality:** construct an embedded piecewise-isometric Type 5 realization
   for every reduced modulus, then transport it to arbitrary rank-two lattices.
   The existing square and small box do not provide this coverage. A sharp-ray
   construction alone would also be insufficient for Type 5: the rest of its
   interior moduli still need coverage.
2. **Nonuniversality:** prescribe one exact modulus and prove that **every**
   Type 5 realization there is impossible. The primary target here is
   `tau*=1/2+10^6 i`. The verified marking enumeration gives one sharp-ray
   marking orbit, and the research localization reduces it to the 19 continuous
   cells below. Excluding every cell at this same modulus, with the geometric
   coverage bridges discharged, would finish the nonuniversality direction.

An exact full witness at `tau*` would settle feasibility of that metric and
invalidate this proposed counterexample. It would not prove universality.
Likewise, exclusions obtained at different moduli cannot be added together
to prove that any one modulus is impossible.

## 2. Established foundation and the remaining proof bridges

| Component | Available result | What it does not establish |
|---|---|---|
| Square realization | [`Periodic.lean`](../../OrigamiTorus/Type5/Periodic.lean), `square_torus` and `square_complex_by_faces`, give the embedded facewise-isometric square torus. | Coverage of other moduli. |
| Nonrectangular box | [`ContinuationTorus.lean`](../../OrigamiTorus/Type5/ContinuationTorus.lean), `torus_by_faces`, applies throughout [`ModulusBox`](../../OrigamiTorus/Type5/Continuation.lean), centered at `(0.174241221618834,1.084897889755590)` with coordinate radius `10^-11`. | A continuation path or a cover of the missing domain. |
| Finite reconstruction | [`Normalize.lean`](../../OrigamiTorus/Type5/Normalize.lean), `marked_reduction_complete`, normalizes a `MarkedRealization` and includes it among at most 32 candidates for four intrinsic core points. | Automatic extraction of that input structure from an arbitrary quotient realization; acceptance of every algebraic candidate. |
| Winding classification | The [`winding modules`](../../OrigamiTorus/Winding/) verify candidate enumeration and symmetry reduction: two interior orbits, one sharp-ray orbit, one hexagonal orbit for Type 5. | Spatial feasibility of those markings. |
| Finite elongated cover | [`fixed_elongated/README.md`](../type5_focus/fixed_elongated/README.md) gives quantitative localization and 36 raw cells / 19 representatives at `tau*`, including turn boundaries. | An exclusion of any of the cells; this geometric reduction is research mathematics, not an assembled Lean theorem. |
| Full metric formulations | The 18-variable Gram formulation and 23-variable signed-Gram formulation retain exact metric compatibility and optional complete intersection tests. | A SAT or UNSAT certificate. Smaller variable count alone gives no solver-performance guarantee. |

The Type 5 graph is `K3` joined to `K2,3`: anchors `(1,2,5)`, roots `(3,4)`,
leaves `(0,6,7)`. Vertices 1, 2, and 5 are universal. Four intrinsic core
points give eight real parameters; the two roots and three leaves account
for the finite radical choices. This is the strongest existing structural
advantage for a completion attempt. The formal reduction already handles
rank loss and an identically zero leaf norm polynomial under its stated
hypotheses; a new implementation should reuse those arguments rather than
silently assuming its favorite determinant stays nonzero.

Use [`docs/VERIFICATION.md`](../../docs/VERIFICATION.md) to distinguish those
Lean results from the research generators' inherited strict-support,
K4-nondegeneracy, marking, and perturbation premises. A final theorem must
connect the actual quotient realization to the exact hypotheses used by
the chosen generator. Replaying algebra does not supply that bridge.

## 3. Exact primary target and complete cell ledger

Fix `y=10^6`, `W=y^2=10^12`, and `epsilon=1/1000`. Use the archived sharp
marking gauged at vertex 1, with `p1=0`. A label word records, in vertex order
`0,...,7`, the first cap (`0`), first open strip (`1`), second cap (`2`), or
second open strip (`3`). The integer vector `q` is in the same order.
The actual normalized levels are constrained by the eliminated cap-center
inequalities, with center separation strictly between `119/250` and
`131/250`. These are continuous feasibility problems, not isolated points.

The four maximal **limiting** families are:

| Block | Maximal label | Integer `q` | Horizontal turn cycles | Finite cells in its endpoint bookkeeping |
|---|---|---|---|---:|
| F1 | `00120221` | `(0,0,0,-1,0,0,-1,0)` | `014`, `356` | 5 |
| F2 | `00220231` | `(0,0,0,-1,0,0,-1,0)` | `014`, `235` | 9 |
| F3 | `00230232` | `(0,0,0,-1,0,0,-1,0)` | `014`, `257` | 9 |
| F4 | `01200202` | `(0,0,0,0,0,0,0,0)` | `0364`, `257` | 3 |

The following complete table was recomputed from the actual archive using
`endpoints` and `mirror` in [`elongated/verify.py`](../type5_focus/elongated/verify.py).
Include the endpoints of **both** symmetry mates before canonicalizing; this
is necessary to retain `20022020` in F4. Memberships overlap.

| Exact cell ID | Integer `q` | Block membership | Status |
|---|---|---|---|
| `00020220` | `(0,0,0,-1,0,0,-1,0)` | F1, F2, F3 | Open |
| `00020221` | `(0,0,0,-1,0,0,-1,0)` | F1, F2 | Open |
| `00020222` | `(0,0,0,-1,0,0,-1,0)` | F1, F2 | Open |
| `00022220` | `(0,0,0,-1,-1,0,-1,0)` | F3 | Open |
| `00023220` | `(0,0,0,-1,-1,0,-1,0)` | F3 | Open |
| `00120220` | `(0,0,0,-1,0,0,-1,0)` | F1 | Open |
| `00120221` | `(0,0,0,-1,0,0,-1,0)` | F1 | Open |
| `00200202` | `(0,0,0,0,0,0,0,0)` | F3, F4 | Open |
| `00200232` | `(0,0,0,0,0,0,-1,0)` | F3 | Open |
| `00220200` | `(0,0,0,-1,0,0,0,0)` | F2 | Open |
| `00220201` | `(0,0,0,-1,0,0,0,0)` | F2 | Open |
| `00220202` | `(0,0,0,-1,0,0,0,0)` | F2, F3 | Open |
| `00220230` | `(0,0,0,-1,0,0,-1,0)` | F2 | Open |
| `00220231` | `(0,0,0,-1,0,0,-1,0)` | F2 | Open |
| `00220232` | `(0,0,0,-1,0,0,-1,0)` | F2, F3 | Open |
| `00230202` | `(0,0,0,-1,0,0,0,0)` | F3 | Open |
| `00230232` | `(0,0,0,-1,0,0,-1,0)` | F3 | Open |
| `01200202` | `(0,0,0,0,0,0,0,0)` | F4 | Open |
| `20022020` | `(-1,0,0,-1,-1,0,-1,0)` | F4 | Open |

For finite-metric work, **define a block as the disjunction of the full
systems for its listed cells**. Do not identify that disjunction with just
the open two-scale chart of its maximal limiting label. The bounded
second-scale derivation in the older elongated note applies only in relative
interiors; its constants need not remain bounded at turn endpoints. The
finite localization is the source of completeness at `tau*`.

## 4. First milestone: finish all of F1

The first full block is exactly

```text
00020220  00020221  00020222  00120220  00120221
```

Start algebra development on `00120221`, but design its statement to cover
the other four cells and the symmetry mate. A proof for that one cell alone
must be recorded as one cell, not as F1 or Type 5.

F1 is a reasonable first target because its relative-interior limit already
has a specific obstruction: the archived short-unlinked orientation models
cannot have **both** limiting cap triangles spanning the transverse plane.
Consequently at least one cap must collapse in that regime. The corresponding
counts for F2, F3, F4 are positive, so the same argument does not cover them.
This is a reason to investigate F1, not evidence that F1 is nearly proved.
At finite `W`, and on endpoint cells, the missing argument must control
arbitrarily small cap areas and edges.

The desired first theorem has the form:

> There is no embedded marked Type 5 realization at `tau*` whose finite
> localized cell belongs to the displayed F1 set.

Its hypotheses must include the complete metric and embedding conditions,
or be explicitly proved necessary consequences of them. A compact or
limiting argument must either yield an explicit bound at `y=10^6` or be
restated as a different, common exact counterexample target for all blocks.

### Gate A — freeze inputs and audit coverage

**Inputs:** the face list, sharp cocycle, finite generator, formal winding
results, and the quantitative two-turn proof.

**Work:** pin the research revision; regenerate the 36 raw cells and 19
representatives; verify their cocycle, symmetry action, cap-center
elimination, and table membership. Audit the uniform two-turn proof and the
strict/weak endpoint conventions against an arbitrary actual embedding.
Identify the exact formal result or remaining lemma supplying each inherited
geometric premise. Several older recorded runs used transcribed inputs;
fresh source replay should supersede those qualifications explicitly.

**Output:** a small coverage manifest with exact labels, `q`, input hashes,
and hypotheses, plus the statement that every realization maps into one
of the listed systems. Repeating counts without this geometric statement
does not pass the gate.

### Gate B — choose one complete algebraic model

Use the two-chart projective model above as the primary implementation. Its
full F1 union shares the fourteen intrinsic variables and one bounded ratio
across all five cells. Both charts must be decided. The exact verifier proves
the chart and denominator conditions and checks the retained incidence tests.
The following older models remain independent baselines for reconstruction
and witness checking:

- [`fixed_elongated/generate.py`](../type5_focus/fixed_elongated/generate.py)
  with `--full`: 14 intrinsic variables and four missing squared distances;
  positive anchor Gram block, exact rank-three equations, all face and
  nearest-lift conditions, and degeneracy-complete affine-circuit exclusions.
- [`fixed_elongated/cubic.py`](../type5_focus/fixed_elongated/cubic.py)
  in `cubic --full --extra` mode: 23 variables and 15 cubic metric equations
  using a fixed signed pivot with strictly positive factors. Its incidence
  conditions have higher degree; the whole formula is not cubic.

The latter also uses all three universal-vertex gauges and the cyclic deficit
inequalities. These can strengthen the complete model, but their quadratic
relaxation is already known feasible. The eight-parameter radical
reconstruction or the six-equation Gram completion is useful for elimination,
provided a metric-dependent change of coordinates and all chart conditions
are proved correct. Do not substitute the hexagonal coefficients unchanged.

**Output:** one precise F1 formula, or five formulas with a proved covering
disjunction, and a reconstruction/soundness argument. Keep a second model
for independent witness checking; do not maintain multiple competing solver
ledgers for the same mathematical branch.

### Gate C — derive a constraint that survives cap collapse

Exploit the actual remaining structure: three universal vertices, two root
reconstructions, and **three leaves coupled to both roots**. The next useful result
would be a division-free inequality or finite exact certificate combining
signed rank-one compatibility with the allowed embedding circuits.

For F1, carry the cap area and phase variables at their actual scales.
If a proposed sidedness inequality needs a positive cap-area denominator,
separate its zero/near-zero regime with a justified argument. A positive
lower bound cannot be inserted merely to make interval arithmetic work.
Try to eliminate the leaf coordinates simultaneously using the existing
rank and nonzero-polynomial proofs; retain linear leaf polynomials, double
roots, and all valid root choices. When using another pivot, prove chart
coverage or fall back to the complete polynomial model on the exceptional
set.

**Output:** an exact new identity/inequality with its hypotheses and a
specific reduction of the full F1 problem. Test a proposed necessary
inequality against the stored feasible relaxations before relying on it.
An exact counterexample to an intermediate lemma is useful diagnosis,
but closes no cell.

### Gate D — obtain a decisive whole-block result

Accept one of the following:

- a hand contradiction valid for all five complete cells;
- independently replayable exact infeasibility certificates whose domains
  cover all five cells, including their weak-boundary strata;
- an exact full embedded witness at `tau*`, which ends this counterexample
  attempt and triggers a documented choice of a different target or a
  constructive strategy.

For interval proofs, every subdivision must cover its parent, and the final
frontier must be empty. Undecided or singular boxes remain open. For
polynomial certificates, record the exact rational identities, inequality
directions, strictness source, and a terminating verifier. A solver's bare
UNSAT verdict is not yet the repository's proof artifact. A SAT model must
be reconstructed and checked as described in section 7.

### Gate E — cover the other blocks at the same modulus

After a certified F1 exclusion, reuse its proved lemmas in F2, F3, and F4.
Record exclusions by exact cell ID so shared boundary cells are counted
once. F4's three cells include the symmetry-derived `20022020`; omitting it
leaves a coverage gap. The final stopping condition is **19/19**, not four
maximal interior labels.

If one new argument covers all blocks directly, use it; the staged order
is an implementation choice, not a required mathematical detour.

### Gate F — assemble and formalize the classification

Compose quotient-to-marked-data extraction, sharp-marking completeness,
finite localization, and all exact exclusions. State explicitly whether
the result is a reviewed mathematical proof with an exact checker or a
Lean theorem. Then formalize the missing bridges and certificate checker,
and run the repository Lean build and Comparator before calling the new
classification Lean-verified. Existing square and box theorems remain the
positive existence part of the Type 5 classification.

## 5. Hexagonal target: separate fallback, with complete scope

The alternative modulus is `1/2 + sqrt(3)/2 i`. It has one marking orbit,
but its necessary orientation cover is much larger than B1.1.

| Ledger item | Exact current scope |
|---|---|
| Historical orientation archive | 751 automorphism-orbit representatives. |
| Proven exclusion | Historical orbit 512, equivalently B1.5 chamber 15, and its relabelings; the six-comparison final polynomial works at every metric. |
| Remaining orientation representatives | 750; none of the 19 elongated cells is thereby closed. |
| Height family B1 | `++---` on `(0,3,4,6,7)`, with height 3 positive; 236 historical chambers, 235 after the exclusion. |
| B1 subbranches | B1.1: 14; B1.2: 16; B1.3: 33; B1.4: 34; B1.5: 41 remaining; B1.6: 97. |
| Height family B2 | `+++++`, with 102 necessary clique patterns; still open. |
| B1.1 | All 14 weak chambers remain open. Excluding them alone closes B1.1, not B1 or Type 5. |

Sources: the [`branch ledger`](../type5_focus/branch_ledger/README.md) and
[`final-polynomial proof`](../type5_focus/final_polynomial.md). The archive
is preserved unchanged; skip the identified impossible orbit explicitly
rather than silently changing historical indices.

The validated [`weak-chamber reduction`](../type5_closure/weak_chamber_reduction.md)
is the appropriate embedding tactic here. Begin with 23 strict K4 brackets,
propagate strictness by affine cofactors and signed Grassmann–Plücker
identities, and exhaust all possible minimal affine circuits. Among the 750
remaining representatives, 700 then need no separate intersection test,
10 need one four-point test, and 40 need two. Every B1.1 chamber needs none.
These are complete embedding tests within the specified weak chambers;
they are **not 700 exclusions** or claims of realizability.

The propagation and circuit proof is metric-independent, so it can also
be ported to an explicit-coordinate elongated system. Such a port must
retain the complete relevant chamber/symmetry cover and replace the metric
equations correctly. The B1.1 restriction does not cover the elongated
problem, and the hexagonal norm `X^2+3Y^2+Z^2` must not be reused for `tau*`.

[`compact_hex.py`](../type5_closure/compact_hex.py) implements the corresponding
complete hexagonal equations with 29 variables, 21 quadratic metric
equalities, and cubic bracket inequalities. Nonclique signs remain weak
unless the checker proves strictness. To resume this route, target the
entire B1.1 union first, including simultaneous completion of leaves 0, 6,
and 7, then retain the explicit B1/B2 assembly obligations. Do not advance
to B1.2 just because B1.1 times out. Exclusions at the hexagon and `tau*`
stay in their own ledgers; the metric-independent final polynomial is the
exception that genuinely transfers.

## 6. Work that must not be repeated as a proposed obstruction

| Existing evidence | Consequence for the next attempt |
|---|---|
| Exact collinear transverse `t=0` models in all four maximal elongated families | Plain weak-limit metric infeasibility is false. Weak bracket signs cannot remove models on which every bracket vanishes. |
| Exact rational witnesses for every one of the 19 four-point rectangle/phase relaxations | Stronger phase propagation alone does not establish Euclidean rank-three compatibility or embeddedness. |
| Exact rational quadratic-deficit models for all four maximal families and the hexagon | The signed rank-one metric equations or additional genuine geometric information must be used. |
| Exact embedded six-vertex B1.1 partial core | Its tested K5/conic/chord subsystem is feasible. A full exclusion must retain the omitted leaves and their joint constraints. The later certified failure near that one core does not cover all cores. |
| Positive logarithmic bracket models for the other 750 orientation representatives | Repeating the same final-polynomial relaxation cannot exclude them. A stronger identity or metric condition is needed. |
| Nonlinear queries returned UNKNOWN, including 300000 ms B1.1-union trials and the canonical first B1.1 chamber | Timeouts do not alter any cell or chamber count. Another run needs a stated new constraint, elimination, certificate-producing method, or concrete unresolved solver issue. |

The six-vertex certificate and its local nonextension are documented in
[`b11_core`](../type5_focus/branch_ledger/b11_core/README.md) and
[`b11_height`](../type5_focus/branch_ledger/b11_height/README.md). Exact phase
and quadratic witnesses are in [`phase_bounds.md`](../type5_focus/fixed_elongated/phase_bounds.md)
and [`cubic_metric.md`](../type5_focus/fixed_elongated/cubic_metric.md).
The longer solver experiments are recorded separately in
[`type5_closure/verification.txt`](../type5_closure/verification.txt).

## 7. Acceptance criteria and reproducible entry points

An accepted **full witness** supplies exact algebraic coordinates or
certified isolating intervals, all 24 edge identities, nondegenerate
coherently oriented intrinsic faces with degree of absolute value one,
the correct prescribed periods, and complete spatial simplex-intersection
exclusions. Check the actual marking and cell membership. A partial core,
rank-compatible metric without intersection checks, numerical residual,
or feasible inequality relaxation does not meet this criterion.

An accepted **exclusion** identifies its complete domain, including zero
nonclique brackets, vanishing auxiliary coefficients, all root choices,
and all turn-endpoint cells. Nonzero K4 brackets may be used under the
proved premise, but no uniform lower bound follows from nonvanishing.
Generic perturbation supplies a weak-chamber cover; it does not permit
replacing every weak inequality by a strict one.

Run from the repository root; generated systems belong outside the source
tree. These commands reproduce inputs and certificates, not a new solution:

```sh
python3 research/type5_completion/verify_coverage.py
python3 research/type5_completion/coverage_constraints.py --check-square
python3 research/type5_completion/f1_geometry_verify.py
python3 research/type5_completion/f1_algebra_verify.py
python3 research/type5_completion/f1_algebra_projective.py /tmp/type5-f1 --cell F1 --solver nlsat-no-factor --statistics
python3 research/type5_focus/solve.py 60000 /tmp/type5-f1/F1-chart8.smt2 /tmp/type5-f1/F1-chart9.smt2
```

The earlier baselines and historical certificates remain reproducible:

```sh
python3 research/type5_focus/elongated/verify.py
node research/type5_focus/elongated/verify_hulls.cjs
python3 research/type5_focus/fixed_elongated/generate.py /tmp/type5-fixed-full --full
python3 research/type5_focus/fixed_elongated/phase.py
python3 research/type5_focus/fixed_elongated/verify_cubic.py
python3 research/type5_focus/fixed_elongated/cubic.py /tmp/type5-cubic-full cubic --full --extra
node research/type5_focus/verify_final_polynomial.cjs
python3 research/type5_closure/verify_weak_chambers.py
python3 research/type5_closure/compact_hex.py --b11 all --output /tmp/type5-b11.smt2
```

For each substantive follow-up, record the base revision, exact target,
input/output hashes, assumptions, command, verifier outcome, and the precise
change in closed-cell count. Keep solver failures as diagnostics. Update
the mathematical ledger only after the acceptance criterion is met.

## 8. Priority relative to Types 4 and 7

Type 4 is not demonstrably the easiest remaining proof. Its verified
open-strip coverage makes it a strong constructive target, but the sharp-ray
cap degenerations are unresolved and local metric/sign shortcuts have
explicit counterexamples. Type 7 also has open-strip coverage and a concrete
remaining whole-marking target. Neither comparison can be decided from
the number of cells or variables alone.

Type 5 has three universal vertices, a formal finite reconstruction, and
particularly effective weak-chamber embedding tests. Those make it a
credible target for exact elimination or a small certificate. Its present
positive coverage is much smaller, however, and its simplest elongated
relaxations are provably feasible. There is no justified prediction that
five F1 cells are easier than one full Type 4 cell or one Type 7 marking.

The actionable Type 5 priority is therefore **one complete F1 result with
all five cells**, independently of which other type is pursued in parallel.
This roadmap does not defer Type 5 until Type 4 is finished, and does not
promote a small hexagonal subchamber result to a whole-type milestone.

## PR boundary

This draft now contains the roadmap, the source-pinned coverage audit,
checked necessary geometry, and the complete reduced F1 solver described above. It
changes no Lean theorem, historical archive index, or completion count.
Type 5 proof commits remain separately reviewable on the research branch;
a formal release change comes only after the relevant proof and verification
gates.
