# Origami tori — research checkpoint

The research goal is to classify which of the seven Lutz eight-vertex triangulations admit embedded, intrinsically flat realizations in R³ and which realize every flat two-torus. The minimum vertex count is known to be eight. Lean proves Type 2 nonexistence, Type 4 near-universality, the Type 5 square and nonrectangular box realizations, Type 6 universality, and coverage of every rectangular lattice torus for Type 7.

- [Type 2 nonexistence argument](docs/Type2.md), including the spherical-link reduction and a finite resolution certificate.
- [Type 4 open-strip construction](docs/Type4.md), including the convex flip, rank, and height lifts.
- [Type 5 radical constructions](docs/Type5.md), including the square, the nonrectangular box, and the branch count.
- [Type 6 universality proof](docs/Type6.md), including the diagonal flip, the quotient triangulation, and rank nine at the spatial embedding.
- [Type 7 rectangular construction](docs/Type7.md), including a hand proof of horizontal rank.
- [Verification scope and Palomar status](docs/VERIFICATION.md).

## Current status (2026-11-27)

| Type | Degree sequence | Existence | Universality |
|---|---|---|---|
| 1 | 36666777 | Known impossible | No |
| 2 | 45567777 | Nonexistence proved in Lean | No |
| 3 | 46666677 | Known yes | Published universality |
| 4 | 55666677 | Proved in Lean | Every reduced modulus with \(0\le x<1/2\) has a Type 4 embedding, proved in Lean |
| 5 | 55566777 | Exact radical square and nonrectangular box realizations proved in Lean | Open |
| 6 | 55666677 | Proved in Lean | Every rank-two lattice torus has a Type 6 embedding, proved in Lean |
| 7 | 66666666 | Proved in Lean | Every rectangular lattice and the reduced strip \(0\le x\le1/20\) have Type 7 embeddings, proved in Lean |

Types 4 and 6 share a degree sequence and have different graphs. The existence classification combines the Type 2 proof with the existing constructions and nonexistence result for the other types. [Verification scope](docs/VERIFICATION.md) records which of these results Lean checks.

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
- Lean verifies the Type 7 strip \(0\le x\le1/20\), \(y^2\ge1-x^2\), with rank nine. Sharp-rhombic coverage is unresolved.
- Lean verifies the Type 5 radical embedding on the closed box of sup-norm radius 10^-11 centered at (0.174241221618834, 1.084897889755590). The numerical continuation reaches x approximately 0.20726.
- Lean verifies the shortest-edge winding enumeration. The remaining coverage problems reduce to two Type 5 interior marking families and seven sharp-rhombic families. The seven give four orbits at the hexagonal endpoint. Each family has continuous geometric parameters.
- Lean verifies that Type 5 reconstruction reduces to eight real parameters and at most 32 branches per fixed marking of the lifted faces. For Types 4 and 7, Lean verifies fourteen intrinsic parameters and at most 80 radical branches, with exact edge-length and spatial intersection tests.
- Lean verifies that all seven ray representatives give affine triangulations of the hexagonal quotient with strictly shortest edges. Spatial embeddability at this modulus remains open.

## Negative results / avoid repeating

Direct searches for embedded sharp-rhombic realizations did not find a certified witness. This is not evidence of impossibility sufficient for a proof. The previously used trapezoidal family degenerates at x=1/2. Alternative diagonal flips and constant-height lifts did not supply global Type 5 or boundary constructions. Shortest-edge inequalities alone do not exclude the hexagonal metric; the elongated-limit disjoint-cycle test did not exclude any remaining type. Avoid extending pointwise continuation or creating more finite local subcases without a global coverage or obstruction argument.

## Gated next steps

1. Audit the remaining positive interval and planar-inflation certificates. Check exact combinatorial labels and all degeneracies before stating full coverage.
2. Fixed hexagonal metric: resolve all applicable marking orbits for one type using exact infeasibility or a certified embedded witness. Infeasibility of all markings for one metric suffices for nonuniversality. A witness at one metric does not suffice for universality.
3. If the hexagonal metric is realizable, attack whole sharp-rhombic ray for Types 4 and 7 using a parametrized regular lift or finite coverage certificate; do not assume continuity of embeddings across a degenerating boundary.
4. Type 5: use the radical reconstruction to seek a parameter-global construction or a rigorous single-metric obstruction. A finite number of marking families by itself does not guarantee practical quantifier elimination.
5. Complete the geometric bridges and remaining certificates listed in [Verification scope](docs/VERIFICATION.md).

## Sources

- Schwartz, [Vertex-Minimal Paper Tori](https://arxiv.org/abs/2507.14998).
- Lander, [The two most symmetric flat tori as eight-vertex paper tori](https://arxiv.org/abs/2609.10703).
- Doyle and Schwartz, [near-universality preprint](https://arxiv.org/abs/2510.12623).
- Doyle, Lander, Schwartz and Trettel, [A Universal 8-Vertex Origami Torus Triangulation](https://arxiv.org/abs/2611.21909).
- Lutz face lists and numerical seeds: [Lander and Trettel's public data](https://github.com/FabianLander/low-vertex-flat-tori).

## Checkpoint verification

During preparation of this PR, the Type 2 CNF generator and independent C++ DPLL checker were rerun (84 variables, 7,464 clauses, UNSAT, 38,849 nodes), as were the latest Type 5 radical interval checker and intrinsic hexagonal feasibility checker (PASS). This is a replay of computational checks, not an independent proof audit. Other historical verifiers and recorded outputs are preserved; they are not all rerun in this checkpoint.
