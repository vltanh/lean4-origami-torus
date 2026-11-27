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
| ray_4 | R1 and R2 unresolved for y^2>=35/4; shorter range unresolved |

**Current attack:** resolve ray_4's two continuous branches with the new Gram formulation or a global geometric inequality. Do not count the two orbits as solved, nor infer Type 7 nonuniversality from exclusion of ray_4 alone. The other three markings must be excluded at the same metric to prove nonuniversality. All prior proof-audit qualifications and classification entries remain unchanged.
