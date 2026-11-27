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
