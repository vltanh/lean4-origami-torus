# Origami tori — research checkpoint

**Scope:** classify which of the seven Lutz eight-vertex torus triangulations admit embedded, intrinsically flat realizations in R³, and which are universal (realize every flat two-torus). The minimum vertex count is known to be eight. This branch preserves the research in progress; it does not contain Lean-verified proofs.

## Current status (2026-11-26)

| Type | Degree sequence | Existence | Universality |
|---|---|---|---|
| 1 | 36666777 | Known impossible | No |
| 2 | 45567777 | Candidate nonexistence proof (SAT UNSAT; geometric reduction needs audit) | Conditional no |
| 3 | 46666677 | Known yes | Published universality |
| 4 | 55666677 | Exact interval/algebraic certificates | Candidate full open strip 0 <= Re tau < 1/2 |
| 5 | 55566777 | Exact interval and radical constructions | Open; square and other small open regions |
| 6 | 55666677 | Exact interval certificates | Candidate global diagonal-flip proof |
| 7 | 66666666 | Known yes | Candidate coverage off sharp-rhombic ray, combining literature and rectangular strip proof |

Types 4 and 6 have identical degree sequences but different graphs. The five-realizable/two-impossible existence classification is conditional on the Type 2 geometric reduction. Four of seven universality statuses are addressed only if all relevant proofs survive audit; the other three remain open. No priority or novelty claim is made.

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

Generated DIMACS and large SMT-LIB files are intentionally not versioned. Run `python3 research/regenerate_systems.py` to restore them. For verification, use Python 3 with assertions enabled, SymPy, networkx, and a C++17 compiler. The optional parse checker uses libz3; parsing is not a feasibility result. See each original proof note for the actual commands and dependencies.

## Positive results and limitations

- Type 2 Boolean formula: 84 variables, 7,464 clauses, exhaustive DPLL UNSAT in 38,849 search nodes. **This establishes only the encoded Boolean contradiction until the necessary geometric lemmas and degeneracy handling have been independently audited.**
- Positive fixed-metric certificates for Types 4, 5 and 6 use exact outward-rounded integer interval arithmetic and a contraction mapping; the square-modulus certificates use nine equations. Type 5 has separate exact radical constructions. No numerical seed alone is treated as a proof.
- The Type 6 universality proof and Type 4 open-strip proof use rational planar families, determinant sign checks and an implicit-function argument. They rely on cited literature lemmas and require a full independent audit.
- Type 7's rectangular strip certificate complements the published near-universality statement; sharp-rhombic coverage is unresolved.
- Latest Type 5 nonrectangular box: center (0.174241221618834, 1.084897889755590), sup-norm radius 10^-11. Continuation to x approximately 0.20726 is numerical only.
- Shortest-edge winding reduction leaves two Type 5 interior families and seven sharp-rhombic families (Type 4: 2, Type 5: 1, Type 7: 4). At the hexagonal endpoint these give four symmetry orbits. These are finite semialgebraic families, not solved finite Boolean obligations.
- Type 5 reconstruction reduces to eight real geometric parameters and at most 32 branches per fixed marking, conditional on auditing the rank and quadric arguments. Types 4 and 7 have related 14-variable reconstructions.
- Intrinsic feasibility of all seven ray marking representatives at the hexagonal modulus is checked exactly; it does not imply three-dimensional embeddedness.

## Negative results / avoid repeating

Direct searches for embedded sharp-rhombic realizations did not find a certified witness. This is not evidence of impossibility sufficient for a proof. The previously used trapezoidal family degenerates at x=1/2. Alternative diagonal flips and constant-height lifts did not supply global Type 5 or boundary constructions. Shortest-edge inequalities alone do not exclude the hexagonal metric; the elongated-limit disjoint-cycle test did not exclude any remaining type. Avoid extending pointwise continuation or creating more finite local subcases without a global coverage or obstruction argument.

## Gated next steps

1. Audit Type 2 geometry (hemisphere equality, planar K5-minus-edge separation, perturbation and sign encoding), then audit positive interval and planar-inflation certificates. Check exact combinatorial labels and all degeneracies; do not publish a conditional theorem as established.
2. Fixed hexagonal metric: resolve all applicable marking orbits for one type using exact infeasibility or a certified embedded witness. Infeasibility of all markings for one metric suffices for nonuniversality. A witness at one metric does not suffice for universality.
3. If the hexagonal metric is realizable, attack whole sharp-rhombic ray for Types 4 and 7 using a parametrized regular lift or finite coverage certificate; do not assume continuity of embeddings across a degenerating boundary.
4. Type 5: use the radical reconstruction to seek a parameter-global construction or a rigorous single-metric obstruction. A finite number of marking families by itself does not guarantee practical quantifier elimination.
5. Once all statuses are settled, extract auditable mathematical statements/proofs and only then decide whether to formalize in Lean. Do not open another large formalization project merely to archive exploratory results.

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

See [Type 7 reconstruction, rigidity and two elongated branches](research/type7_focus/README.md). The anchor-leaf reconstruction proves at most two embedded candidates per intrinsic placement on every marking. Using the earlier necessary clique-sign archive, the weighted mirror-distance identity and the checkerboard twist test strengthen this to **uniqueness up to congruence from the 24 labeled edge lengths**, conditional on the earlier strict-support and orientation-projection proof premises. The exact finite checker ran on the current input archives: 308/316 clique patterns have a unanimous anchor; the eight others have no admissible checkerboard partner. This is a rigidity result, not a universality result.

For the elongated range y^2>=35/4, ray_4's 16 generic orientation models reduce under the joint 32-element marking stabilizer to two orbits of eight. Canonical anchor 0127 has opposite-side and same-side mirror patterns, respectively. Both have an exact Gram-completion formulation with 18 real unknowns for a fixed metric, or 19 over the entire elongated range. All nonclique determinant signs are weak, with full intersection circuit constraints retained. The new fixed y=4 R1 and R2 systems both returned unknown (5000 ms solver timeouts); no branch is excluded or realized.

| Type 7 marking | Current outstanding gate |
|---|---|
| ray_1 | Entire sharp ray unresolved |
| ray_2 | Entire sharp ray unresolved |
| ray_3 | Entire sharp ray unresolved |
| ray_4 | **Conditionally excluded for y^2>=35/4**; shorter range unresolved |

**New global asymptotic reduction:** [positive slack transport and common-line limit theorem](research/type7_focus/limit_obstruction.md). On every ray_4 embedding, a 4x4 matrix of strict nearest-lift slacks equals the difference between intrinsic and extrinsic ring-edge dot products, with positive horizontal ring steps as row and column marginals and total mass one. This is valid for every sharp modulus. On the elongated range, the exact cross correction identities and both weak orientation representatives exclude rank two (both parallelogram and one-zero-edge triangle limits) and rank one (adjacent/opposite half-stick limits). Consequently every convergent bounded limit as y tends to infinity has both rings on the same transverse line. The companion SymPy checker was executed successfully on transcribed current cocycle and representative signs. The theorem is conditional on the earlier geometric, compactification and necessary SAT reduction premises.

**Second blow-up (new):** [four affine intrinsic limit families](research/type7_focus/blowup_obstruction.md). Magnifying the transverse width is orientation-preserving at every positive t, irrespective of its rate relative to the axial correction. The resulting nonzero-rank balanced-Laplacian classification, projected metric residuals, and slack equations reduce all possible normalized intrinsic limits to four explicit line segments up to marking symmetry (F1/F2 for R1 and F3/F4 for R2). Each has at least three vanishing horizontal ring steps and rescaled vertical spread exactly 3/8. The former eight-quarter-step degenerate limit witness cannot be approached by actual embeddings. The companion checker was executed on transcribed current inputs; all exact finite and symbolic checks passed. The conclusion inherits the previous geometric and orientation/SAT audit qualifications.

**Elongated ray_4 closed (conditional):** [two six-inequality final polynomial certificates](research/type7_focus/final_polynomial.md). Every one of the 16 generic sign models is algebraically nonrealizable, by two explicit Grassmann–Plücker multiplicative contradictions and the checked orbit coverage. Thus ray_4 is impossible throughout y^2>=35/4, conditional on the earlier strict-support, linking and necessary SAT enumeration premises. This supersedes the common-line and second blow-up gates; no positive-t nonlinear solver or asymptotic argument is necessary. The exact final-polynomial checker passed on the branch inputs. The earlier SAT completeness check and geometric premises have not been independently audited in this checkpoint.

**Current attack:** apply final-polynomial filtering to the other three markings at a common elongated modulus, then solve the remaining genuine metric feasibility problems. The shorter ray_4 range remains open, as do ray_1, ray_2 and ray_3. Excluding only ray_4 does not prove Type 7 nonuniversality. All previous audit qualifications remain.

Type 4 H13 follow-up: an exact integer sign-only embedding realizes the singleton orientation model, so orientation-only contradictions cannot close it. The two universal vertices give a 22-variable exact Gram relaxation (362 assertions), with an alternative division-free 14-intrinsic-variable reconstruction and six residual metric equations; four strict clique-volume comparisons are available for the H13 metric attack. The solver returned UNKNOWN at 15 seconds and exploratory searches found no positive witness. See [Type 4 ledger, section 10](research/type4_focus/README.md#10-h13-metric-only-obstruction-remains-universal-edge-elimination). No class is yet excluded.

Type 4 H13 follow-up: exact circuit propagation forces 63 of 70 determinant signs strict (40 additional), including the four vertices surrounding each of the 24 edges. Thus all edges are genuine creases and the four nonedge chords are strictly shorter than their intrinsic distances. The hexagonal Voronoi bound reduces the necessary nearest-lift comparisons to seven shifts per nonedge. The strengthened 22-variable, 298-assertion system did not return a result within the external 15-second local limit; H13 remains open. The coarse weighted curvature-order relaxation also cannot yield a nonconstant separating weight. See [Type 4 ledger, section 11](research/type4_focus/README.md#11-h13-exact-exclusion-of-40-determinant-degeneracies). No orientation class has been excluded.


Type 5 follow-up: [signed Gram completion and root-chord inequalities](research/type5_focus/gram_completion/README.md) gives uniqueness from labeled edge lengths under the strict K4 premise and a radical-free 14-variable fixed-hexagonal system with six metric determinant equations. Two global slack-square bounds and a three-gauge slope-order disjunction strengthen the exact system; symbolic tests passed, but both nonlinear queries returned UNKNOWN at 10 seconds. B1.1 is still 0/14 excluded. No universality or proof-audit status changes.
