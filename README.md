# Origami tori — research checkpoint

The research goal is to classify which of the seven Lutz eight-vertex triangulations admit embedded, intrinsically flat realizations in R³ and which realize every flat two-torus. The minimum vertex count is known to be eight. Lean proves nonexistence for Types 1 and 2, open-strip coverage for Types 4 and 7, the Type 5 square and nonrectangular box realizations, and universality for Types 3 and 6.

- [Type 1 nonexistence proof](docs/Type1.md), including the star collapse and seven-vertex hull obstruction.
- [Type 2 nonexistence argument](docs/Type2.md), including the spherical-link reduction and a finite resolution certificate.
- [Type 3 universality proof](docs/Type3.md), using the published planar families and height vectors.
- [Type 4 open-strip construction](docs/Type4.md), including the convex flip, rank, and height lifts.
- [Type 5 radical constructions](docs/Type5.md), including the square, the nonrectangular box, and the branch count.
- [Type 6 universality proof](docs/Type6.md), including the diagonal flip, the quotient triangulation, and rank nine at the spatial embedding.
- [Type 7 rectangular and open-strip constructions](docs/Type7.md), including a hand proof of horizontal rank.
- [Verification scope and Palomar status](docs/VERIFICATION.md).

## Current status (2026-11-27)

| Type | Degree sequence | Existence | Universality |
|---|---|---|---|
| 1 | 36666777 | Nonexistence proved in Lean | No |
| 2 | 45567777 | Nonexistence proved in Lean | No |
| 3 | 46666677 | Proved in Lean | Every rank-two lattice torus has a Type 3 embedding, proved in Lean |
| 4 | 55666677 | Proved in Lean | Every reduced modulus with \(0\le x<1/2\) has a Type 4 embedding, proved in Lean |
| 5 | 55566777 | Exact radical square and nonrectangular box realizations proved in Lean | Open |
| 6 | 55666677 | Proved in Lean | Every rank-two lattice torus has a Type 6 embedding, proved in Lean |
| 7 | 66666666 | Proved in Lean | Every reduced modulus with \(0\le x<1/2\) has a Type 7 embedding, proved in Lean |

Types 4 and 6 share a degree sequence and have different graphs. Lean verifies the existence classification for all seven types. [Verification scope](docs/VERIFICATION.md) records which of these results Lean checks.

## Completion roadmap

The remaining classification question is **universality**. Existence or nonexistence is already settled for all seven types. Three independent research workstreams now have detailed completion roadmaps: [Type 4, PR #2](https://github.com/vltanh/lean4-origami-torus/pull/2), [Type 5, PR #3](https://github.com/vltanh/lean4-origami-torus/pull/3), and [Type 7, PR #4](https://github.com/vltanh/lean4-origami-torus/pull/4). All three drafts target this research branch.

**Current Type 7 target: complete the ray-1 and ray-2 markings.** Ray 3 now has a complete research exclusion at every sufficiently large height, and ray 4 has an audited explicit exclusion. Eventual bounds for the other two markings would supply one common counterexample modulus. The final Lean assembly remains open. Type 4's ray-2 transport estimates remain useful, but no full Type 4 case is closed. The counts of eight Type 4 families, nineteen Type 5 cells, and fifteen fixed-target Type 7 systems describe different continuous domains and do not rank their difficulty. The previous instruction to defer Types 5 and 7 until Type 4 is finished is superseded.

| Type | Completed result | Work needed to finish the type | Current action |
|---|---|---|---|
| 1 | Nonexistence, proved in Lean | None for this classification | Retain the proof |
| 2 | Nonexistence, proved in Lean | None for this classification | Retain the proof |
| 3 | Universality, proved in Lean | None for this classification | Retain the proof |
| 4 | Existence and the full reduced open strip, proved in Lean | Decide the sharp-rhombic boundary: either one impossible modulus in both markings, or coverage of the entire missing boundary | First Type 4 case: `ray2_2`, then the other seven; [detailed roadmap in PR #2](https://github.com/vltanh/lean4-origami-torus/pull/2) |
| 5 | Exact square and nonrectangular box, proved in Lean | A single-modulus obstruction covering every marking, or a construction covering every missing modulus | Finish the five-cell F1 block, then cover all 19 localized cells; [detailed roadmap in PR #3](https://github.com/vltanh/lean4-origami-torus/pull/3) |
| 6 | Universality, proved in Lean | None for this classification | Retain the proof |
| 7 | Existence and the full reduced open strip, proved in Lean | A single-modulus obstruction covering every marking, or coverage of the entire missing boundary | **Complete rays 1 and 2**, then the Lean assembly; ray 3 is eventually excluded and ray 4 has an audited explicit bound; [detailed roadmap in PR #4](https://github.com/vltanh/lean4-origami-torus/pull/4) |

### Type 4: one fixed target, eight complete cases

Fix

\[
\tau_* = \tfrac12 + 10^6 i.
\]

The [finite cover](research/type4_focus/fixed_metric.md) gives the following eight maximal closed families, including cap endpoints and collapsed limits. The names and labels below are exactly those of [the enumeration](research/type4_focus/type4_gap_enum.py). A family is a continuous feasibility problem; its appearance in this finite list is not a proof of infeasibility.

| Case | Labels in vertex order 0,...,7 | Cap cycles in this representative | Full-case status |
|---|---|---|---|
| `ray2_2` | `20220012` | 145 / 0273; vertex 6 in the broadened strip | First Type 4 case; open |
| `ray2_1` | `12220002` | 456 / 1273; equivalent to 145 / 0263 | Next within Type 4; open |
| `ray1_1` | `00120212` | 014 / 357 | Open |
| `ray1_2` | `00130222` | 014 / 567 | Open |
| `ray1_3` | `00230223` | 014 / 256 | Open |
| `ray1_4` | `01200223` | 034 / 256 | Open |
| `ray1_5` | `02200323` | 034 / 126 | Open |
| `ray1_6` | `12200023` | 345 / 126 | Open |

1. **Finish `ray2_2`.** Use the exact ray-2 transport identities and full edge equations to control the degenerating triangle 145 and quadrilateral 0273. The previous cap-sidedness certificates exclude only their nondegenerate transverse regime. The missing proof must also cover arbitrarily small edges and cap areas, every allowed position of vertex 6, and nonclique coplanarity. An argument that divides by an area needs a bound that remains valid as that area approaches zero.
2. **Finish `ray2_1`.** Reuse any proved estimate for the entire second marking, then handle its 145 / 0263 cap geometry. Closing both rows excludes the second marking at the same modulus.
3. **Finish the six first-marking cases.** Work through the displayed rows, reusing arguments for the shared triangular caps. Every maximal family must be closed; excluding an orientation subchamber or only a limiting regime does not close its row.
4. **Assemble the theorem.** Combine the eight exclusions with the marking and closed-cell coverage theorems, discharge their documented geometric premises, and then formalize the resulting nonuniversality proof in Lean. The existing open-strip theorem remains part of the final Type 4 classification.

The present count is **0/8 full cases excluded**. A certified embedded solution in any row would refute this proposed counterexample modulus and trigger a deliberate change of target or a constructive boundary proof. It would settle that modulus, not universality.

Generate the first Type 4 case, retaining every intersection test:

```sh
python3 research/type4_focus/type4_fixed_cubic.py /tmp/type4-ray2_2 --case ray2_2 --full
```

### Type 4: checked proof work

The [cap calculation](research/type4_completion/ray2_2_geometry.md) now gives exact Gram and vertex-to-edge identities for all three small-margin regimes of triangle 145, together with positive nearest-lift deficit inequalities. These retain the cap area and vertical tilt at their actual scales. The [local affine-sign lemma](research/type4_completion/core_signs.md) gives six allowed Radon patterns for each of the two five-vertex cliques, including the implications `lambda6(2)<0 => lambda4(2)>0` and `lambda6(3)<0 => lambda5(3)>0`. The strict K4 premise excludes zero coefficients, without requiring any uniform lower bound on them.

An [exact algebraic core](research/type4_completion/algebra.md) satisfies all its metric equations, shortest lifts, intrinsic face orientations and the tested nonedge contractions while having opposite cap signs. Its certified edge 15 / face 264 crossing shows why those metric conditions alone cannot prove the desired sidedness. The [linking audit](research/type4_completion/linking_audit.md) likewise supplies actual nonflat configurations for both allowed linking forms and qualitative cap separation. These are diagnostics of insufficient arguments, not realizations of the target torus.

All four new exact checkers passed on this checkout, and the full `ray2_2` system regenerated with 23 variables and 890 assertions. The next Type 4 proof must combine the metric identities with the actual nonintersection conditions across the A, B and C collapse regimes. The proposed metric sign implication is explicitly **unproved**; no full-case count or Lean theorem has changed.

### Completion criteria and parallel work

A case closes only with a mathematical contradiction valid on its entire domain, an independently replayable exact infeasibility certificate, or an exact embedded witness that changes the proposed obstruction strategy. Numerical nonconvergence, timeout, an uncheckable solver verdict, and an exclusion requiring a positive limiting area do not meet this criterion. Each new proof must state which geometric premises it uses; algebra checks alone do not discharge those premises.

For Type 5, the first milestone is the entire five-cell F1 block in the [19-cell fixed target](research/type5_focus/fixed_elongated/README.md), using the full metric and embedding conditions. A limiting cap-collapse argument or one closed cell does not close F1. The [complete weak-chamber tests](research/type5_closure/weak_chamber_reduction.md) support a separate hexagonal fallback; its chamber counts are not the elongated cell counts.

For Type 7, the [complete ray-3 boundedness proof](research/type7_completion/ray3_boundedness.md) covers both localized phases and every collapse rate, above an unspecified height. The [ray-4 exclusion](research/linking_checkpoint/cycle_thresholds.md) applies for `y^2>=63/16` with its research geometric premises audited. Complete ray-1/2 exclusions and the Lean bridges remain. New solver work uses the independently checked [bounded quadratic branches](research/type7_completion/solver_remaining_axis.md), retaining linking, all actual zero boundaries and every potentially nonzero collapse product.

The draft roadmaps specify full case ledgers, proof gates, boundary obligations, exact reproduction commands, constructive alternatives and the final Lean bridges. The fixed-target counts remain **0/8 Type 4 cases, 0/19 Type 5 cells, and 0/15 Type 7 systems excluded**; the ray-3 eventual bound has no known comparison with `10^6`. A whole-type obstruction must cover every marking at one common modulus. Eventual exclusions can be combined by choosing a height above all their bounds.

## Repository layout

- `OrigamiTorus/Type*` contains the proofs for each triangulation.
- `OrigamiTorus/Geometry`, `OrigamiTorus/Lattice`, `OrigamiTorus/Winding`, and `OrigamiTorus/Certificates` contain the shared Lean developments.
- `docs/` contains the mathematical writeups, the verification scope, and credits.
- `palomar/OrigamiTorus/` contains the independent Challenge, Solution, and Comparator configuration.
- `research/` preserves the checkpoint packages and later research ledgers.

## Research packages

The directory names preserve the original certificate package structure. Each package's README explains its own proof, dependencies, inputs and reproduction. Historical copies are retained to preserve the original relative paths; identical files share Git blobs. The following is the single current status ledger; historical README files are proof notes, not competing live status trackers.

| Package under research/ | Content |
|---|---|
| origami_torus_certificate | Type 2 combinatorial enumeration, hemisphere/mixed-side reduction and exact DPLL checker |
| torus_classification_certificate | All seven triangulations; interval certificates for Types 4,5,6; copies of negative checker |
| torus_moduli_certificate | Exact square modulus and common local regions; Jacobian ranks |
| type6_universality_certificate | Transfer of published Type 3 families by a diagonal flip; rational sign verification |
| torus_remaining_certificate | Rectangular and initial unbounded strip for Types 4 and 7 |
| torus_type4_wide_certificate | Five rational lift certificates extending Type 4 through x=9/20 |
| torus_finite_reduction_certificate | Fifteen winding-marking cases and exact semialgebraic/SMT generator |
| torus_near_universal_certificate | Type 4 through all x<1/2; nine remaining cases and four hexagonal marking orbits |
| torus_type5_reconstruction_certificate | Eight-variable radical reconstruction and exact square witness |
| torus_type5_continuation_certificate | Exact nonrectangular Type 5 box; exact intrinsic hexagonal examples for all seven ray markings |

To replay the archived research packages, use Python 3 with assertions enabled, SymPy, networkx, and a C++17 compiler. Run `python3 research/regenerate_systems.py` to restore the generated DIMACS and SMT-LIB files. The optional libz3 checker checks syntax. For the Lean proofs and Palomar package, use the commands in the verification guide. [Verification scope](docs/VERIFICATION.md)

## Positive results and limitations

- Type 2 nonexistence follows from the Lean-verified geometric reduction and a checked resolution certificate for the 84-variable, 7,464-clause sign formula. The original search and checkers remain in the research package.
- Positive fixed-metric certificates for Types 4, 5 and 6 use exact outward-rounded integer interval arithmetic and a contraction mapping; the square-modulus certificates use nine equations. Type 5 has separate exact radical constructions. No numerical seed alone is treated as a proof.
- Lean verifies the spatial embeddings and the multiplicity-one lattice triangulations for Types 4 and 6. The Type 4 proof checks all six height cells in Lean, including the cell approaching \(x=1/2\).
- Lean verifies the Type 7 open strip \(0\le x<1/2\), \(y^2\ge1-x^2\), with rank nine. Sharp-rhombic coverage is unresolved.
- Lean verifies the Type 5 radical embedding on the closed box of sup-norm radius 10^-11 centered at (0.174241221618834, 1.084897889755590). The numerical continuation reaches x approximately 0.20726.
- Lean verifies the shortest-edge winding enumeration. The remaining coverage problems reduce to two Type 5 interior marking families and seven sharp-rhombic families. The seven give four orbits at the hexagonal endpoint. Each family has continuous geometric parameters.
- Lean verifies that Type 5 reconstruction reduces to eight real parameters and at most 32 branches per fixed marking of the lifted faces. For Types 4 and 7, Lean verifies fourteen intrinsic parameters and at most 80 radical branches, with exact edge-length and spatial intersection tests.
- Lean verifies that all seven ray representatives give affine triangulations of the hexagonal quotient with strictly shortest edges. Spatial embeddability at this modulus remains open.

## Negative results / avoid repeating

Direct searches for embedded sharp-rhombic realizations did not find a certified witness. This is not evidence of impossibility sufficient for a proof. The previously used trapezoidal family degenerates at x=1/2. Alternative diagonal flips and constant-height lifts did not supply global Type 5 or boundary constructions. Shortest-edge inequalities alone do not exclude the hexagonal metric; the elongated-limit disjoint-cycle test did not exclude any remaining type. Avoid extending pointwise continuation or creating more finite local subcases without a global coverage or obstruction argument.

## Verification before a final classification claim

The completion roadmap above sets the research order. For any new completed result, audit the exact combinatorial labels, coverage and degeneration arguments, then update the geometric bridges and certificate scope in [Verification scope](docs/VERIFICATION.md). Run the Lean build and Comparator in an environment with the repository toolchain before describing a new theorem as Lean-verified.

## Sources

- Schwartz, [Vertex-Minimal Paper Tori](https://arxiv.org/abs/2507.14998).
- Lander, [The two most symmetric flat tori as eight-vertex paper tori](https://arxiv.org/abs/2609.10703).
- Doyle and Schwartz, [near-universality preprint](https://arxiv.org/abs/2510.12623).
- Doyle, Lander, Schwartz and Trettel, [A Universal 8-Vertex Origami Torus Triangulation](https://arxiv.org/abs/2611.21909).
- Lutz face lists and numerical seeds: [Lander and Trettel's public data](https://github.com/FabianLander/low-vertex-flat-tori).

## Checkpoint verification

During preparation of this PR, the Type 2 CNF generator and independent C++ DPLL checker were rerun (84 variables, 7,464 clauses, UNSAT, 38,849 nodes), as were the latest Type 5 radical interval checker and intrinsic hexagonal feasibility checker (PASS). This is a replay of computational checks, not an independent proof audit. Other historical verifiers and recorded outputs are preserved; they are not all rerun in this checkpoint.

## Latest checkpoint: Types 4, 5, 7

See [sharp-ray proof and exact systems](research/sharp_ray_checkpoint/README.md). The four hexagonal endpoint systems now have a rational formulation with quadratic metric equations and at most cubic affine minors. All four solver tests returned unknown/timeouts. A symbolic geometric proof excludes the equally spaced parallel two-ring family for the twisted Type 7 grid, including nonsymmetric rings. Neither this restricted obstruction nor any numerical search closes a type. The classification and outstanding audit qualifications above are unchanged.

## Orientation-chamber checkpoint

See [the general nondegeneracy lemma, orientation reduction and exact relaxed witness](research/orientation_checkpoint/README.md). Minimality forces every vertex star to have strict support relative to its neighbors, at least four genuine creases, and every complete four-vertex subgraph to be noncoplanar. Exact SAT projection and independent DPLL checks leave 10, 7 and 12 spanning-3-tree orientation branches for Types 4, 5 and 7 respectively. For Type 5 the eight-variable root/leaf reconstruction can additionally use seven anchor-height sign patterns. A radical certificate at the exact hexagonal modulus satisfies all metric equations and admissible clique signs but has 15 edge–face crossings, proving this relaxation insufficient. Full embedding conditions remain essential. The new nonlinear searches did not resolve any of the three types. Earlier audit qualifications remain unchanged.

## Linking and elongated Type 7 checkpoint

See [global diameter obstruction and bounded rescaling](research/linking_checkpoint/README.md). Nonzero linking of parallel primitive geodesics implies extrinsic diameter strictly less than their period length. On the sharp-rhombic ray, all remaining markings therefore have zero short-direction linking for y^2>=35/4. Exact SAT filtering on the necessary orientation relaxation reduces Type 7 ray_4 from 316 clique patterns/12 reconstruction branches to 4/2, with only 16 full generic Boolean sign models. Type 4 ray_2 reduces to 36 clique patterns and seven branches. The Type 7 ray_4 intrinsic levels satisfy a uniform narrow-level estimate 3/(8*y^2), giving a bounded polynomial compactification; an exact degenerate t=0 witness shows that naive limit infeasibility cannot establish closure. The topology cycle check also implies the remaining three types are unknotted and Type 5 has exactly five linked pairs of disjoint triangular cycles, using standard knot-theoretic facts. Sixteen numerical chamber searches at y=4 found no positive certified separation; this is inconclusive. No universality status has changed; previous proof-audit qualifications remain.

## Planar obstruction checkpoint

See [exact planar-pattern obstruction at the hexagonal metric](research/planar_obstruction/README.md). A planar isometric-face configuration must have opposite face signs across any clique-adjacent edge unless the opposite edge has a shortest-lift tie. Exact enumeration gives no all-clique-flip sign pattern for Type 4 and exactly one for Type 5. The latter pattern is impossible at the hexagonal metric, even allowing ties elsewhere: the three unfolded root charts give a rhombus constraint and an exact bilinear identity forcing a leaf to coincide with a root. The rational checker passed. Other tied planar patterns and genuinely 3D embeddings remain possible. The full disjoint-cycle linking and elongated separation relaxations tested here did not improve Type 4/5 sign counts; exploratory searches of the 15 one-noncrease-clique-adjacency Type 5 patterns found no witness, not an infeasibility proof. No universality status changed; do not treat this as a nonuniversality theorem.

## Previous branch ledger: Type 5

[Current branch ledger](research/type5_focus/branch_ledger/README.md) records the earlier focused Type 5 task. Fix the exact hexagonal metric. The six automorphisms preserve that metric and the marking up to gauge, reducing the seven height patterns to two inequivalent families B1 (`++---`, six clique patterns) and B2 (`+++++`, 102 clique patterns). B1's six subbranches contain respectively 14, 16, 33, 34, 42 and 97 generic Boolean sign models, checked by both direct SAT exhaustion and expansion of the previous orbit archive. **Paused: B1.1 (14 models, zero certified excluded).** All 14 relaxed and 14 full closed-sign systems returned timeout; no subbranch is closed. The actual metric configurations may have coplanar nonclique quadruples, so their determinant signs are weak in the chamber systems, and clique signs are strict. See the ledger for reproduction and exact closure criteria. Also archived: the previously unpushed coincident-planar-family obstruction and 447 projected-crossing filters, with limitations. Do not advance to B1.2 on a timeout or claim a Type 5 obstruction from a restricted planar construction. All previous audit qualifications remain unchanged.

## Parallel Type 4 focus

[Type 4 reduction and branch ledger](research/type4_focus/README.md): the anchor tetrahedron (1,4,5,6), two independent conic vertices (2,3), and two degree-five leaves (0,7) give a proposed exhaustive reconstruction with eight independent geometric parameters and at most 16 radical branches per parameter choice. All 24 metric edge equations are satisfied by construction; rank/degeneracy arguments inherit the earlier audit requirement. At the exact hexagonal metric the two ray markings merge, and all four automorphisms preserve the marking up to lattice symmetry and gauge. The 120 necessary clique patterns reduce to 31 joint classes (2,405 generic sign models across chosen representatives); H13 has one full model. No class has been ruled out, and the singleton H13 exact-coefficient nonlinear relaxation timed out. The Type 4 universality classification remains open. This separate focus does not alter the Type 5 ledger.

## Active branch ledger: Type 7

**Current completion branch:** the [ray-3 boundedness proof](research/type7_completion/ray3_boundedness.md)
excludes every unbounded ray-3 sequence, hence every sufficiently large
height, with no explicit numerical threshold. It covers all common-line
degenerations, including all 300 mixed four-zero cells and sixteen
two-noncollinear zero-cone supports. The final 96-formula mixed package
independently checks in 21.377 seconds using reusable RUP traces.
Rays 1 and 2 and the Lean assembly remain open. The separate
`y=10^6` ledger is unchanged; see the
[current roadmap](research/type7_completion/ROADMAP.md).

The [ray-1/2 compiler](research/type7_completion/solver_remaining_compilation.md)
now covers all 18,080 generic signs, with matched Boolean enumeration
reduced from 121.338 to 3.951 seconds and independent completeness replay.
A [uniform bounded axis chart](research/type7_completion/exhaustive_remaining_axis.md)
retains all six collapse products for every `y>=32`. Its
[268 branches per marking](research/type7_completion/solver_remaining_axis.md)
have quadratic metric equations and only 3–50 remaining actual circuit
tests. These verified reductions support further proof search; no full
ray-1/2 marking is yet excluded.

The [complete limiting cover](research/type7_completion/exhaustive_remaining_locus.md)
has two canonical families and retains all product scales at their
intersections. For ray 1's two-block limit, the
[focal-ellipse proof](research/type7_completion/remaining_ray1_mask04.md)
forces a common transverse line, including every degenerate focal
triangle; its 52 Boolean certificates independently replayed. The
[first transverse stretch](research/type7_completion/remaining_ray1_mask04_blowup.md)
excludes twenty more closed cases, leaving four symmetric single-edge
endpoints. The [metric reducer](research/type7_completion/solver_remaining_limit.md)
also supplies exact projected identities for both canonical families;
all 54 parameter strata and 642 row certificates independently check.
All three canonical endpoint regimes are now excluded by exact metric
contradictions, completing the
[entire ray-1 two-block limit](research/type7_completion/ray1_two_block_exclusion.md).
The [turning-angle proof](research/type7_completion/solver_remaining_c1_turning.md)
also excludes every regular C1 limit for ray 1, including zero individual
deficits. The [complete C0 cells](research/type7_completion/exhaustive_c0_cells.md)
retain all 669 generic models in eighteen angular patterns, with exact
weak-sign decision diagrams and independent coverage proofs. Ray 1's
other limit regions, ray 2, and the Lean assembly remain open.

See [Type 7 reconstruction, rigidity and two elongated branches](research/type7_focus/README.md). The anchor-leaf reconstruction proves at most two embedded candidates per intrinsic placement on every marking. Using the earlier necessary clique-sign archive, the weighted mirror-distance identity and the checkerboard twist test strengthen this to **uniqueness up to congruence from the 24 labeled edge lengths**, conditional on the earlier strict-support and orientation-projection proof premises. The exact finite checker ran on the current input archives: 308/316 clique patterns have a unanimous anchor; the eight others have no admissible checkerboard partner. This is a rigidity result, not a universality result.

For the elongated range y^2>=35/4, ray_4's 16 generic orientation models reduce under the joint 32-element marking stabilizer to two orbits of eight. Canonical anchor 0127 has opposite-side and same-side mirror patterns, respectively. Both have an exact Gram-completion formulation with 18 real unknowns for a fixed metric, or 19 over the entire elongated range. All nonclique determinant signs are weak, with full intersection circuit constraints retained. The new fixed y=4 R1 and R2 systems both returned unknown (5000 ms solver timeouts); no branch is excluded or realized.

| Type 7 marking | Current outstanding gate |
|---|---|
| ray_1 | Seven fixed-metric large-step branches at y=10^6, all open |
| ray_2 | Seven fixed-metric large-step branches at y=10^6, all open |
| ray_3 | One localized canonical phase at y=10^6, open |
| ray_4 | **Conditionally excluded for y^2>=63/16** by the [winding-cycle bound](research/linking_checkpoint/cycle_thresholds.md); shorter range unresolved |

**New global asymptotic reduction:** [positive slack transport and common-line limit theorem](research/type7_focus/limit_obstruction.md). On every ray_4 embedding, a 4x4 matrix of strict nearest-lift slacks equals the difference between intrinsic and extrinsic ring-edge dot products, with positive horizontal ring steps as row and column marginals and total mass one. This is valid for every sharp modulus. On the elongated range, the exact cross correction identities and both weak orientation representatives exclude rank two (both parallelogram and one-zero-edge triangle limits) and rank one (adjacent/opposite half-stick limits). Consequently every convergent bounded limit as y tends to infinity has both rings on the same transverse line. The companion SymPy checker was executed successfully on transcribed current cocycle and representative signs. The theorem is conditional on the earlier geometric, compactification and necessary SAT reduction premises.

**Second blow-up (new):** [four affine intrinsic limit families](research/type7_focus/blowup_obstruction.md). Magnifying the transverse width is orientation-preserving at every positive t, irrespective of its rate relative to the axial correction. The resulting nonzero-rank balanced-Laplacian classification, projected metric residuals, and slack equations reduce all possible normalized intrinsic limits to four explicit line segments up to marking symmetry (F1/F2 for R1 and F3/F4 for R2). Each has at least three vanishing horizontal ring steps and rescaled vertical spread exactly 3/8. The former eight-quarter-step degenerate limit witness cannot be approached by actual embeddings. The companion checker was executed on transcribed current inputs; all exact finite and symbolic checks passed. The conclusion inherits the previous geometric and orientation/SAT audit qualifications.

**Elongated ray_4 closed (conditional):** [two six-inequality final polynomial certificates](research/type7_focus/final_polynomial.md). Every one of the 16 generic sign models is algebraically nonrealizable, by two explicit Grassmann–Plücker multiplicative contradictions and the checked orbit coverage. Thus ray_4 is impossible throughout y^2>=35/4, conditional on the earlier strict-support, linking and necessary SAT enumeration premises. This supersedes the common-line and second blow-up gates; no positive-t nonlinear solver or asymptotic argument is necessary. The exact final-polynomial checker passed on the branch inputs. A fresh Boolean orbit enumeration and independently checked 4,379-step RUP proof of the 7,786-clause blocked formula establish completeness of the orientation elimination; see the reproduction commands in the proof note. The geometric premises still require independent audit. In fact, the two alternating four-edge cycles must have nonzero linking in every flat Type 7 embedding, irrespective of the modulus.

**Remaining markings: quantitative fixed-metric localization.** [Proof and exact checks](research/type7_focus/remaining_markings.md). For ray_1 and ray_2, the exact cyclic metric identities force two groups of large vertical steps, separated by gaps of at least two small steps, at every y>=10^6. There are seven rotation classes of large-step masks for each marking. For ray_3, a global squared-distance variance identity forces its phase h within 1/y^2 of one of two equivalent endpoints whenever y>=4, and gives strict separation of the two short-ring hulls at y>=8. The phase branches are equivalent by cyclic rotation. The new exact integer witnesses also show the orientation/linking-only relaxation is realizable for all three remaining markings, including qualitative hull separation; hence final-polynomial filtering alone cannot close them. The integer checker passed on the current archive. A small numerical ray_3 search at y=4 found no positive candidate; no infeasibility follows.

**Ray_3 metric relaxation proved feasible:** [uniform exact nonembedded witnesses](research/type7_focus/remaining_markings.md#uniform-exact-feasibility-of-the-ray_3-metric-only-relaxation). For every y>=10^6, an integer-interval contraction certificate gives exact metric realizations satisfying the phase0 Gram relaxation, including all strict shortest lifts, positive/strictly contracted nonedge distances, oriented intrinsic faces and all 70 nonzero affine determinants. They have 20 certified edge-face crossings. Thus the metric-only relaxation cannot be closed as UNSAT at this or any larger modulus. The full embedding constraints are essential. The uniform checks passed locally with the transcribed archive inputs; the checked-in verifier uses the actual archive.

**Exact Type 7 two-cap obstruction:** [supporting-plane theorem and finite-metric determinant bound](research/type7_focus/cap_order_obstruction.md). The two rings 0145/2367 cannot lie in mutually supporting planes (in particular parallel planes), conditional on the inherited strict-support, mixed-side and K4 premises. A direct Boolean enumeration with only this pair unlinked gives 16 models; all 128 signed planar line orders for each contain a directed cycle. The 7,834-clause blocked CNF is independently UNSAT by exhaustive DPLL in 1,027 nodes. Using ray_3's verified quantitative two-cluster bounds, any actual embedding at y=10^6 must have one of 24 projected cap triangle/edge-pair determinants of magnitude at most 4e-10. This excludes the exact supporting-plane construction class but not all near-degenerate configurations.

**Current attack:** retain the common metric y=10^6 and the full metric-and-embedding system. Ray_3's metric-only relaxation is known feasible; the new cap obstruction supplies necessary finite determinant bounds but does not close ray_3. The seven masks each for ray_1 and ray_2 remain open. Earlier geometric audit qualifications and ray_4's conditional elongated closure are unchanged.

Type 4 H13 follow-up: an exact integer sign-only embedding realizes the singleton orientation model, so orientation-only contradictions cannot close it. The two universal vertices give a 22-variable exact Gram relaxation (362 assertions), with an alternative division-free 14-intrinsic-variable reconstruction and six residual metric equations; four strict clique-volume comparisons are available for the H13 metric attack. The solver returned UNKNOWN at 15 seconds and exploratory searches found no positive witness. See [Type 4 ledger, section 10](research/type4_focus/README.md#10-h13-metric-only-obstruction-remains-universal-edge-elimination). No class is yet excluded.

Type 4 H13 follow-up: exact circuit propagation forces 63 of 70 determinant signs strict (40 additional), including the four vertices surrounding each of the 24 edges. Thus all edges are genuine creases and the four nonedge chords are strictly shorter than their intrinsic distances. The hexagonal Voronoi bound reduces the necessary nearest-lift comparisons to seven shifts per nonedge. The strengthened 22-variable, 298-assertion system did not return a result within the external 15-second local limit; H13 remains open. The coarse weighted curvature-order relaxation also cannot yield a nonconstant separating weight. See [Type 4 ledger, section 11](research/type4_focus/README.md#11-h13-exact-exclusion-of-40-determinant-degeneracies). No orientation class has been excluded.


Type 5 follow-up: [signed Gram completion and root-chord inequalities](research/type5_focus/gram_completion/README.md) gives uniqueness from labeled edge lengths under the strict K4 premise and a radical-free 14-variable fixed-hexagonal system with six metric determinant equations. Two global slack-square bounds and a three-gauge slope-order disjunction strengthen the exact system; symbolic tests passed, but both nonlinear queries returned UNKNOWN at 10 seconds. B1.1 is still 0/14 excluded. No universality or proof-audit status changes.

Type 4 H13 angular-cycle checkpoint: the six projected triangle equations give an intrinsic-only 14-variable angular/metric relaxation. An exact radical witness satisfies that relaxation and all nonedge contractions, but violates 17 H13 signs and has ten certified crossings; the relaxation is provably feasible and must not be attacked for UNSAT. A new circuit check of 56 five-point and 28 four-point partitions proves the strengthened H13 sign conditions suffice for embeddedness, including degeneracies. The resulting complete 19-variable (five positive radicals), 310-assertion metric system timed out at 5 seconds. See [Type 4 ledger, sections 12–13](research/type4_focus/README.md#12-intrinsic-only-angular-cycle-reduction-and-exact-relaxed-witness). H13 remains open and no orientation class has been closed.


Type 5 elongated sharp-ray follow-up: [four maximal limit families and bounded second scale](research/type5_focus/elongated/README.md). Every normalized elongated sequence collapses to a two-turn doubled segment. Exact enumeration gives 36 relative cells, seven maximal closed families, four up to sharp-ray marking symmetry. In their relative interiors, cap vertical widths are O(1/y), yielding a bounded polynomial second scale and exact t=0 elimination of axial corrections. The earlier sign archive excludes two spanning cap triangles in F1 (0 models), but F2-F4 retain 60,130,40 models. Exact rational degenerate t=0 witnesses exist in all four families. Intrinsic placements are certified for y^2>=256, not extrinsic embeddings. Boundaries and positive-t degenerations remain open. **No Type 5 universality or hexagonal B1.1 status change.** See verification limits and earlier audit qualifications.

Type 4 hand-proof checkpoint: no computer-assisted search was used. A new convex-hull lemma for three pairwise intersecting hulls of closed curves of length L bounds every triangle perimeter by strictly less than 3 sqrt(3)L/2. Applied to linked parallel short geodesics, it forces q(1,0)=0 on the sharp-rhombic ray for y^2>=13/2 (previous threshold 35/4). A direct hand check of the prior H13 sign representative shows cycles 014 and 256 linked in the first ray marking, so this entire elongated interval is excluded for that labeled sign branch. The hexagonal H13 case and Type 4 classification remain open. See [the hand proof](research/type4_focus/README.md#14-hand-proof-a-sharp-convex-hull-bound-for-linked-short-fibers).


Type 5 quantitative fixed-metric follow-up: [finite two-gap localization](research/type5_focus/fixed_elongated/README.md). For every y>=10^6, trimmed face intervals have connected components of length <13/25, every uncovered level forces a horizontal cycle on at least three near vertices, and two gaps are separated by normalized vertical distance in (119/250,131/250). Their epsilon=1/1000 cap hulls have distance >11y/25. Snapping the caps proves the previous 36 relative cells cover positive finite metrics, including all boundary degenerations; the checked sharp-ray symmetry leaves 19 branches. Two auxiliary gap centers eliminate by linear inequalities. At y=10^6 each branch has an exact full 18-variable Gram formulation (conditional on the inherited K4 and marking premises). All 19 necessary and full queries at 500 ms and five longer full queries at 1500 ms returned UNKNOWN. **0/19 localized branches excluded, Type 5 open.** This supersedes the need to resolve asymptotic boundary cells before a finite target can be attacked; it does not prove nonuniversality or change hexagonal B1.1.

Type 4 global hand-proof checkpoint: [bounded caps, eight cap-pair families and the uniform bounded-tube theorem](research/type4_focus/elongated_hand.md). Any elongated eight-vertex sequence has two horizontal essential turn cycles of bounded physical vertical width, by at most two successive width rescalings per cap. For Type 4, hand enumeration gives six triangle/triangle cap-pair classes in ray 1 and two triangle/chordless-quadrilateral classes in ray 2. Each has a direct edge through each strip, forcing cap separation y/2+O(1) and the entire surface into a uniformly bounded neighborhood of a single actual edge of length y/2+O(1), including intermediate-scale degenerations. In ray 2 at least one isolated cap has physical width tending to zero and perimeter tending to one. No computational search was used, and no surviving cap family has been excluded; Type 4 nonuniversality remains open. The earlier two-marking classification is a premise for the Type 4 tables.

Type 4 elongated follow-up: [four exact cap-sidedness certificates](research/type4_focus/elongated_hand.md#7-computer-assisted-exclusion-of-nondegenerate-transverse-limits-in-ray-2-cap-pair-145--0273) exclude the nondegenerate transverse regime of cap pair 145 / 0273 in ray 2, including all placements of vertex 6. Every surviving bounded limit has a collinear triangular cap, a collinear quadrilateral, or a zero quadrilateral edge (27 or 37 if vertex 6 is outside the triangular cap and the quadrilateral spans). Four Z3-extracted UNSAT clause subsets were independently replayed by exact DPLL; no numerical feasibility claim is made. The new [global four-neighbor reconstruction](research/type4_focus/README.md#16-all-type-4-edge-length-uniqueness-independent-of-h13-signs) also proves uniqueness from labeled edge lengths, up to congruence, and removes extrinsic reconstruction branches for each intrinsic placement. Both results inherit the earlier geometric premises and their audit qualifications. All eight full elongated families and Type 4 universality remain open; the H13 fixed-hexagonal status is unchanged.


Type 5 phase checkpoint: [exact cross-rectangle phase bounds and 19 rational relaxed witnesses](research/type5_focus/fixed_elongated/phase_bounds.md). Four-point polarization and rational row propagation sharpen many physical phase differences from 2000 to near 10^-6, retaining all cap degenerations. The necessary rectangle/nearest/orientation/phase relaxation is **certifiably feasible in all 19 branches**, so cannot prove nonuniversality on its own. A stronger 14-variable signed-Gram relaxation timed out on all 19 (1200 or 3000 ms). **0/19 excluded, Type 5 open.** Exact rational checks ran locally on transcribed current input; repository import version still needs replay. No new branch decomposition or classification change.

Type 4 exact ray-2 follow-up: [four-cycle phase transport and explicit tube](research/type4_focus/ray2_exact_phase.md). The winding cycle 4253 forces positive nearest-lift slacks with sum <=s, where s is the positive horizontal length of edge 45, and the rescaled vertical difference of 45 has absolute value <s/2. The two opposite vertices 2,3 lie within 3/(8y) vertically of the half-period levels. For y>=1 all ray-2 realizations lie within radius 3/2 of edge 42, whose length differs from y/2 by <1/y; for y>=2 the axial component of edge 45 is <3s/y even if its length collapses. These are global quantitative hand bounds with no cap degeneration assumptions. A numerical interior continuation approached x=.5 but did not produce a strict sharp-ray witness. No full marking is excluded; Type 4 remains open.


Type 5 signed-deficit checkpoint: [cyclic link inequalities and exact cubic signed-Gram pivot](research/type5_focus/fixed_elongated/cubic_metric.md). All three universal-vertex gauges give quadratic product inequalities valid even with zero nonedge deficits; rank and signature yield a fixed sparse 4-ray pivot and a 5-by-5 rank-one Schur complement. The resulting exact metric equations are 15 cubics in 23 unknowns, and the polynomial positive-complement coordinates permit full degeneracy-complete embedding tests. The basic quadratic relaxation has exact rational witnesses at the hexagon and all four maximal elongated branches. Symbolic and rational checks passed locally on transcribed inputs; final repository-import version needs replay. Initial cubic/full solver trials timed out or were interrupted; no certified contradiction or actual embedding. **0/19 elongated branches excluded; Type 5 open.** This does not replace the existing eight-variable radical or 14-variable determinant approaches, nor change their audit qualifications.

Type 4 fixed-metric checkpoint: [finite eight-family cover and ray-2 product inequalities](research/type4_focus/fixed_metric.md). Applying the verified eight-vertex two-gap theorem at y>=10^6 and enumerating maximal closed cells gives 56/9 relative cells, 10/4 maximal cells and 6/2 symmetry representatives for the two ray markings. This gives an exhaustive common finite target y=10^6, including endpoints and cap collapses. In ray_2 axial polarization proves |z_i-H_i|<5/y and three product bounds t1*t6, (1-t0)*(1-t1), (1-t6)*(1-t7)<21/y^2 for y>=10, giving cap widths <3 and at least one <22/y. Both markings admit the sparse signed-Gram pivot (2,6,1,3), with fifteen cubic metric equations in 23 variables; the full augmented-Gram circuit tests cover degeneracies. All eight necessary (3000 ms final version) and full (5000 ms) queries timed out; no feasibility or infeasibility certificate. **0/8 finite maximal branches excluded; Type 4 open.** The local exact enumeration and generator ran on transcribed current data; archived version needs fresh replay. No independent audit of the new phase proof is claimed.


Type 5 final-polynomial checkpoint: [six exact signed Grassmann–Plücker identities](research/type5_focus/final_polynomial.md) close one **entire weak-sign chamber** (B1.5 chamber 15, one-based), not merely a generic sign model. Exact circuit propagation forces 60 brackets nonzero and the identities force the remaining two cancellation factors strict. Multiplication gives P<P. The six automorphism relabelings are excluded at every modulus under inherited strict-support/K4 premises. Thus 750/751 orientation orbits, 4500/4506 labeled full models, 3000/3004 short-unlinked models, and 235/236 B1 chambers remain. B1.5 is 1/42 excluded; B1.1 remains 0/14. The exact checker passed on actual branch inputs; longer single-dominant-term Plücker log constraints are feasible for the other 750 representatives. **No full marking or localized elongated branch is closed; Type 5 universality remains open.**



## Closure attempt: 27 November 2026

Types 4, 5 and 7 remain open as universality questions. The [new exact winding-cycle bounds](research/linking_checkpoint/cycle_thresholds.md) give thresholds for all seven sharp markings, sharpen six of the earlier three-fiber thresholds, and extend the inherited Type 7 ray_4 exclusion to **y^2>=63/16**, including equality. The certificate is the Hamiltonian cycle of period (-3,4), together with the existing mandatory-linking theorem and diameter bound. Exact enumeration on the actual cocycles verifies that each listed threshold is best for this particular cycle/diameter test; no claim of an optimal geometric threshold is made.

At the common finite target y=10^6, the outstanding full systems are still eight Type 4 families, nineteen Type 5 families, and fifteen Type 7 branches across ray_1, ray_2 and ray_3. The strengthened ray_4 result does not exclude any of those outstanding systems. The new cycle checker and both existing Type 5/7 final-polynomial checkers passed on this checkout. Earlier conditional geometric premises are unchanged.

The [Type 5 weak-chamber reduction](research/type5_closure/weak_chamber_reduction.md) gives complete embedding tests without assuming general position. After the previously proved final-polynomial exclusion, 700 of the 750 remaining orientation representatives need no extra intersection tests beyond their propagated strict/weak brackets; the other 50 need one or two four-point circuit exclusions. All fourteen B1.1 chambers fall in the first group. The accompanying exact verifier passed on all 751 historical representatives, and the direct-coordinate generator gives quadratic metric equations and cubic bracket inequalities. This is a simplification of the full feasibility problem, not an exclusion of any further chamber.

The [transformed-chart proof](research/type7_closure/README.md) also rules out every nondegenerate flat member of the defined positive-H trapezoid parametrization on the modularly transformed sharp arc, for both the Type 4 flip and Type 7 face lists. It covers all parameter chambers of that family, not other constructions. The symbolic identities and a separate mathematical review passed. The new Type 7 ray_3 generator retains full degeneracy-aware intersection tests and required long-ring linking of magnitude two; its two extended queries returned no result before external interruption. Extended Type 4 H13 queries also reached external limits without a decision. The Type 5 full B1.1 union returned UNKNOWN at 300000 ms in both the previous Gram formulation and a prototype of the new direct-coordinate formulation; the canonical first-chamber query also returned UNKNOWN at the same limit. None of these solver outcomes closes a marking or a type.
