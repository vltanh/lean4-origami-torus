# Credits

The-Anh Vu-Le maintains this project and supplied the research checkpoint with
the original geometric reduction and certificates. Peter Doyle, Fabian Lander,
Richard Evan Schwartz, and Steve Trettel supplied the underlying Type 3
construction. The proof writeups cite the relevant sections.

On 26 November 2026, a Codex GPT-6 session used the formalize-math-paper
workflow (v4.8.1) to check the arguments and formalize proof components in Lean
4.36.0 with Mathlib. CaDiCaL found a short Type 2 refutation, and SymPy was
used to find the Type 6 derivative elimination order. Lean checks the input
clauses, resolution steps, and elimination identities directly. The Type 4,
5, and 7 Lean components use the rational coordinates and markings supplied
in the checkpoint. Separate GPT-6 agents independently checked the Type 2
geometric reduction, the Type 5 and Type 6 geometric arguments, and the Type 4
and Type 7 marking calculations. The latter audit derived the hand cone-angle
and rank arguments for the trapezoidal charts. Independent human review is pending.

Independent agent reviews also checked that the added Type 2 perturbation
and Type 6 spatial, metric, and quotient-map statements match the hand
arguments and identified the remaining steps in the two geometric proofs.

On 27 November 2026, the Type 6 development added the multiplicity-one proof
using the area of a period cell and transported the embedding through the
modular lattice reduction. A separate agent checked the universal theorem,
the area argument, and the scaling and reflection in the lattice change.
An independent agent later checked the conformal angle calculation, the
two period directions, and the transport of rank nine through exact length
matching to the same rescaled spatial vertices. Spend was not tracked.

The Type 5 square proof uses the same development and area argument with
separately checked face lifts and link cycles. An independent agent review
compared the quotient, coordinate formulas, and squared-distance equality
with the research checkpoint.

A separate agent audited the complete Type 2 strict-support proof, including
the algebraic antipodal exclusion and the proof of the planar complete-graph
obstruction by affine dependences.

An independent agent review checked the projected edge intersections, the
relative boundary and half-plane descriptions, the enclosing triangle, and
the angular estimate for an individual cut against the Type 2 hand argument.
An independent review also checked the chord geometry, edge subdivision,
and finite iteration of half-plane cuts against that argument.
A further review checked the common refinement of the two boundary lists
and the completed mixed-side face theorem.
An independent agent audited the determinant-sign interpretation, the three
clause families, the transport of geometric witnesses into the sign formula,
and the full Type 2 nonexistence statement in the Palomar Challenge.

An independent agent checked the angle-derivative assembly for Types 4 and 7,
including the negative-block sign convention and the projection factor in
the Type 4 balance at vertex 6.

On 27 November 2026, independent GPT-6 reviews checked the Type 7 horizontal
rank elimination, the exact displacement ratio, the affine gluing identities,
and the final quotient and distance scale for either ordering of a rectangular
basis. The six-triangle readout and full dual-tree development use the same
marking. The final Lean proof uses the two commuting generators and the
oriented area cancellation to prove that the gluing maps are translations.

Independent reviews checked the Type 4 diagonal flip in the shared quotient
construction and its relabeling to the Lutz faces. They also verified the
strip-wide rank calculation, the two one-sided chart derivatives, and the
hypotheses of the conditional Type 4 realization. A further review checked the
rational height data from all six PR cells, the treatment of their endpoints,
the strict edge–face separation argument, and the transport of the scaled lift.
A separate review confirmed that the spatial rank-nine assertion in the
open-strip theorem applies to the same rescaled embedding.

An independent agent checked the Type 5 geometric exclusions, the Gram
and null-plane arguments for leaf rank, and the nonvanishing of the norm
polynomial. The review also checked the shift gauge, rigid normalization,
root pivot swap, and completeness of the finite candidate list for marked
realizations.

An independent agent reviewed the Type 4 and Type 7 reconstruction. The
review checked the shared-face argument for a noncoplanar anchor, the sign
and scale of the three-sphere radicals, the spatial reflection, and the
completeness and size of the candidate lists. It also checked the exact
disjoint subface test with degeneracies and the Type 4 and Type 5 Challenge
statements against the labeled constructions.

An independent agent compared the winding orbit tables to the archived
counts and checked the tree gauge, the marking determinant from primitive
walks, and the chosen lattice isometries. It checked that overlapping tiles
share an integer lifted corner and that the walk through such corners has
exactly the desired period. It also compared the seven
hexagonal coordinate systems to the archived harmonic solves and checked
the strict shortest-edge argument and the degree-one intrinsic development.

An independent agent compared the exact Type 5 continuation box, core
coordinates, integral shifts, and radical signs to the checkpoint. The
review checked that the determinant tests exclude surface intersections,
that the edge equalities give the full face metrics, and that the exact
area identity transports from lattice coordinates to physical coordinates.
