# Credits

## Project and mathematical sources

**The-Anh Vu-Le** initiated and directs the project, provided the research material that seeded the proofs, and maintains the repository. The planar families used for Types 3 and 6 come from Peter Doyle, Fabian Lander, Richard Evan Schwartz, and Steve Trettel. The Type 1 star reduction is due to Lander, using Schwartz's seven-vertex obstruction. The Type 4 and 7 constructions build on the near-universality and square-torus work. [Detailed mathematical attribution](RELATED_WORK.md)

## AI contribution

**OpenAI Codex (GPT-6)** contributed to mathematical proof development, wrote and repaired the Lean formalization and Comparator package, and drafted the manuscript and proof documentation under The-Anh Vu-Le's direction. Its proof work included the Type 2 geometric-to-Boolean reduction, the degree-one lattice-quotient argument and rank transfer for Type 6, the rank and gluing arguments for the Type 4 and 7 strip, the verification of the Type 5 exact constructions, and the formal proofs for Types 1 and 3.

Separate Codex review runs checked theorem statements against the literature, the strict-support and mixed-side arguments, exact sign and interval data, face lifts and marked periods, rank at the final spatial placements, and the completeness assumptions in the finite reconstruction and winding reductions. Lean and NanoDa checked the configured proofs. Independent human review is pending.

## Computational tools

Lean 4 and Mathlib supply the proof kernel and mathematical library. CaDiCaL was used to find short propositional refutations for the Type 1 and 2 obstructions. SymPy assisted in finding the elimination order for the Type 6 derivative calculation. Lean replays the relevant proof steps using the explicit clauses and identities. [Verification guide](VERIFICATION.md)
