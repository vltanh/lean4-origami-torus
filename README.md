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
| ray_1 | Seven fixed-metric large-step branches at y=10^6, all open |
| ray_2 | Seven fixed-metric large-step branches at y=10^6, all open |
| ray_3 | One localized canonical phase at y=10^6, open |
| ray_4 | **Conditionally excluded for y^2>=35/4**; shorter range unresolved |

**New global asymptotic reduction:** [positive slack transport and common-line limit theorem](research/type7_focus/limit_obstruction.md). On every ray_4 embedding, a 4x4 matrix of strict nearest-lift slacks equals the difference between intrinsic and extrinsic ring-edge dot products, with positive horizontal ring steps as row and column marginals and total mass one. This is valid for every sharp modulus. On the elongated range, the exact cross correction identities and both weak orientation representatives exclude rank two (both parallelogram and one-zero-edge triangle limits) and rank one (adjacent/opposite half-stick limits). Consequently every convergent bounded limit as y tends to infinity has both rings on the same transverse line. The companion SymPy checker was executed successfully on transcribed current cocycle and representative signs. The theorem is conditional on the earlier geometric, compactification and necessary SAT reduction premises.

**Second blow-up (new):** [four affine intrinsic limit families](research/type7_focus/blowup_obstruction.md). Magnifying the transverse width is orientation-preserving at every positive t, irrespective of its rate relative to the axial correction. The resulting nonzero-rank balanced-Laplacian classification, projected metric residuals, and slack equations reduce all possible normalized intrinsic limits to four explicit line segments up to marking symmetry (F1/F2 for R1 and F3/F4 for R2). Each has at least three vanishing horizontal ring steps and rescaled vertical spread exactly 3/8. The former eight-quarter-step degenerate limit witness cannot be approached by actual embeddings. The companion checker was executed on transcribed current inputs; all exact finite and symbolic checks passed. The conclusion inherits the previous geometric and orientation/SAT audit qualifications.

**Elongated ray_4 closed (conditional):** [two six-inequality final polynomial certificates](research/type7_focus/final_polynomial.md). Every one of the 16 generic sign models is algebraically nonrealizable, by two explicit Grassmann–Plücker multiplicative contradictions and the checked orbit coverage. Thus ray_4 is impossible throughout y^2>=35/4, conditional on the earlier strict-support, linking and necessary SAT enumeration premises. This supersedes the common-line and second blow-up gates; no positive-t nonlinear solver or asymptotic argument is necessary. The exact final-polynomial checker passed on the branch inputs. A fresh Boolean orbit enumeration and independently checked 4,379-step RUP proof of the 7,786-clause blocked formula establish completeness of the orientation elimination; see the reproduction commands in the proof note. The geometric premises still require independent audit. In fact, the two alternating four-edge cycles must have nonzero linking in every flat Type 7 embedding, irrespective of the modulus.

**Remaining markings: quantitative fixed-metric localization.** [Proof and exact checks](research/type7_focus/remaining_markings.md). For ray_1 and ray_2, the exact cyclic metric identities force two groups of large vertical steps, separated by gaps of at least two small steps, at every y>=10^6. There are seven rotation classes of large-step masks for each marking. For ray_3, a global squared-distance variance identity forces its phase h within 1/y^2 of one of two equivalent endpoints whenever y>=4, and gives strict separation of the two short-ring hulls at y>=8. The phase branches are equivalent by cyclic rotation. The new exact integer witnesses also show the orientation/linking-only relaxation is realizable for all three remaining markings, including qualitative hull separation; hence final-polynomial filtering alone cannot close them. The integer checker passed on the current archive. A small numerical ray_3 search at y=4 found no positive candidate; no infeasibility follows.

**Current attack:** use the common explicit metric y=10^6, with 7+7+1=15 localized continuous feasibility branches. None of these 15 is certified infeasible yet. The shorter ray_4 range is irrelevant to this single-metric target but remains open. All previous geometric audit qualifications remain.

Type 4 H13 follow-up: an exact integer sign-only embedding realizes the singleton orientation model, so orientation-only contradictions cannot close it. The two universal vertices give a 22-variable exact Gram relaxation (362 assertions), with an alternative division-free 14-intrinsic-variable reconstruction and six residual metric equations; four strict clique-volume comparisons are available for the H13 metric attack. The solver returned UNKNOWN at 15 seconds and exploratory searches found no positive witness. See [Type 4 ledger, section 10](research/type4_focus/README.md#10-h13-metric-only-obstruction-remains-universal-edge-elimination). No class is yet excluded.

Type 4 H13 follow-up: exact circuit propagation forces 63 of 70 determinant signs strict (40 additional), including the four vertices surrounding each of the 24 edges. Thus all edges are genuine creases and the four nonedge chords are strictly shorter than their intrinsic distances. The hexagonal Voronoi bound reduces the necessary nearest-lift comparisons to seven shifts per nonedge. The strengthened 22-variable, 298-assertion system did not return a result within the external 15-second local limit; H13 remains open. The coarse weighted curvature-order relaxation also cannot yield a nonconstant separating weight. See [Type 4 ledger, section 11](research/type4_focus/README.md#11-h13-exact-exclusion-of-40-determinant-degeneracies). No orientation class has been excluded.


Type 5 follow-up: [signed Gram completion and root-chord inequalities](research/type5_focus/gram_completion/README.md) gives uniqueness from labeled edge lengths under the strict K4 premise and a radical-free 14-variable fixed-hexagonal system with six metric determinant equations. Two global slack-square bounds and a three-gauge slope-order disjunction strengthen the exact system; symbolic tests passed, but both nonlinear queries returned UNKNOWN at 10 seconds. B1.1 is still 0/14 excluded. No universality or proof-audit status changes.

Type 4 H13 angular-cycle checkpoint: the six projected triangle equations give an intrinsic-only 14-variable angular/metric relaxation. An exact radical witness satisfies that relaxation and all nonedge contractions, but violates 17 H13 signs and has ten certified crossings; the relaxation is provably feasible and must not be attacked for UNSAT. A new circuit check of 56 five-point and 28 four-point partitions proves the strengthened H13 sign conditions suffice for embeddedness, including degeneracies. The resulting complete 19-variable (five positive radicals), 310-assertion metric system timed out at 5 seconds. See [Type 4 ledger, sections 12–13](research/type4_focus/README.md#12-intrinsic-only-angular-cycle-reduction-and-exact-relaxed-witness). H13 remains open and no orientation class has been closed.


Type 5 elongated sharp-ray follow-up: [four maximal limit families and bounded second scale](research/type5_focus/elongated/README.md). Every normalized elongated sequence collapses to a two-turn doubled segment. Exact enumeration gives 36 relative cells, seven maximal closed families, four up to sharp-ray marking symmetry. In their relative interiors, cap vertical widths are O(1/y), yielding a bounded polynomial second scale and exact t=0 elimination of axial corrections. The earlier sign archive excludes two spanning cap triangles in F1 (0 models), but F2-F4 retain 60,130,40 models. Exact rational degenerate t=0 witnesses exist in all four families. Intrinsic placements are certified for y^2>=256, not extrinsic embeddings. Boundaries and positive-t degenerations remain open. **No Type 5 universality or hexagonal B1.1 status change.** See verification limits and earlier audit qualifications.

Type 4 hand-proof checkpoint: no computer-assisted search was used. A new convex-hull lemma for three pairwise intersecting hulls of closed curves of length L bounds every triangle perimeter by strictly less than 3 sqrt(3)L/2. Applied to linked parallel short geodesics, it forces q(1,0)=0 on the sharp-rhombic ray for y^2>=13/2 (previous threshold 35/4). A direct hand check of the prior H13 sign representative shows cycles 014 and 256 linked in the first ray marking, so this entire elongated interval is excluded for that labeled sign branch. The hexagonal H13 case and Type 4 classification remain open. See [the hand proof](research/type4_focus/README.md#14-hand-proof-a-sharp-convex-hull-bound-for-linked-short-fibers).


Type 5 quantitative fixed-metric follow-up: [finite two-gap localization](research/type5_focus/fixed_elongated/README.md). For every y>=10^6, trimmed face intervals have connected components of length <13/25, every uncovered level forces a horizontal cycle on at least three near vertices, and two gaps are separated by normalized vertical distance in (119/250,131/250). Their epsilon=1/1000 cap hulls have distance >11y/25. Snapping the caps proves the previous 36 relative cells cover positive finite metrics, including all boundary degenerations; the checked sharp-ray symmetry leaves 19 branches. Two auxiliary gap centers eliminate by linear inequalities. At y=10^6 each branch has an exact full 18-variable Gram formulation (conditional on the inherited K4 and marking premises). All 19 necessary and full queries at 500 ms and five longer full queries at 1500 ms returned UNKNOWN. **0/19 localized branches excluded, Type 5 open.** This supersedes the need to resolve asymptotic boundary cells before a finite target can be attacked; it does not prove nonuniversality or change hexagonal B1.1.

Type 4 global hand-proof checkpoint: [bounded caps, eight cap-pair families and the uniform bounded-tube theorem](research/type4_focus/elongated_hand.md). Any elongated eight-vertex sequence has two horizontal essential turn cycles of bounded physical vertical width, by at most two successive width rescalings per cap. For Type 4, hand enumeration gives six triangle/triangle cap-pair classes in ray 1 and two triangle/chordless-quadrilateral classes in ray 2. Each has a direct edge through each strip, forcing cap separation y/2+O(1) and the entire surface into a uniformly bounded neighborhood of a single actual edge of length y/2+O(1), including intermediate-scale degenerations. In ray 2 at least one isolated cap has physical width tending to zero and perimeter tending to one. No computational search was used, and no surviving cap family has been excluded; Type 4 nonuniversality remains open. The earlier two-marking classification is a premise for the Type 4 tables.
