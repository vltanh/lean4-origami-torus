# Closure of elongated Type 7 ray_4 by biquadratic final polynomials

**Conditional theorem.** No embedded flat Type 7 torus with marking ray_4 exists at a sharp modulus tau=1/2+iy with y^2>=35/4. This closes **both** R1 and R2 in the elongated range, including actual configurations with coplanar nonclique quadruples. The earlier geometric strict-support lemma, linking obstruction, and necessary SAT enumeration must survive audit. The proof here replaces all asymptotic limit attacks and nonlinear metric solvers for this range. No claim about other markings or the shorter range follows yet.

## Reduction

By the earlier linking theorem in ../linking_checkpoint/README.md, at y^2>=35/4 the horizontal primitive slope must have self-linking zero. In ray_4 its two ring cycles are disjoint representatives of that slope. A sufficiently small generic perturbation of any actual embedding preserves the embedded simplicial complex, strict local support and mixed-side conditions, and the linking of its disjoint cycles. Flatness itself need not be preserved during the perturbation: the orientation formula is only a necessary condition for this perturbed configuration.

The earlier verify_full_ring4.py verifies completeness of the 16 generic full orientation models in ring4_full_signs.json. The 32 triangulation automorphisms give two orbits of size eight (representatives 1 and 3, using one-based archive indices). The new checker independently verifies the two algebraic contradictions and coverage of all 16 strings under these permutations. For this orientation-only argument even a relabeling not preserving the metric would suffice.

## Six inequalities for each representative

Write [ijkl] for the determinant of the four homogeneous vectors (1,r_i), (1,r_j), (1,r_k), (1,r_l) in this order, and write |ijkl| for its absolute value. In a generic configuration all 70 sorted brackets are nonzero. For distinct indices s,t,a,b,c,d the three-term Grassmann-Plucker identity is
    [stab][stcd] - [stac][stbd] + [stad][stbc] = 0.
If the sign of one of the three signed terms is opposite to the other two, its positive magnitude is their sum and is strictly larger than either. Sorting the bracket indices requires their permutation parity; the checker does this exactly.

R1 (archive model 1):
    |0136||0157| < |0137||0156|
    |0156||0457| < |0157||0456|
    |0137||1236| < |0136||1237|
    |1237||2346| < |1236||2347|
    |2347||2456| < |2346||2457|
    |0456||2457| < |0457||2456|

R2 (archive model 3):
    |0134||1457| < |0147||1345|
    |0247||2357| < |0237||2457|
    |0346||1345| < |0134||3456|
    |0367||3456| < |0346||3567|
    |0237||3567| < |0367||2357|
    |0147||2457| < |0247||1457|

In each list the product of the six left sides equals the product of the six right sides, factor by factor. All factors are positive. Multiplying yields P<P, a contradiction. Consequently neither sign representative, nor any relabeling or global sign reversal, can be realized even by arbitrary eight points in R^3 in general position. No metric equations are needed.

These are biquadratic final polynomials, in the standard method of Bokowski and Richter-Gebert. We found the inequalities by an auxiliary floating LP over logarithms of bracket magnitudes, then verified the final six-relation certificates entirely by integer sign arithmetic and multiset cancellation. No LP output is trusted as a proof. Reference for the general method: J. Richter-Gebert, *Euclideaness and Final Polynomials in Oriented Matroid Theory*, 1993 (https://science-to-touch.com/Articles/jrg/08_EuclideanAndBiquadatic.pdf). The proof above is self-contained given the sign models.

## Reproduction and outstanding work

From research/type7_focus run:
    node verify_final_polynomial.cjs

This exact checker passed on the branch archive, covering all 16 generic models. For the completeness of the necessary orientation enumeration, replay ../linking_checkpoint/verify_full_ring4.py (requires libz3). The latter proof and the geometric premises were inherited, not independently audited in the present certificate check. In particular the prior blow-up analysis is not a premise of this proof.

Next target: apply final-polynomial elimination to the full generic orientation models of ray_1, ray_2 and ray_3 with zero horizontal linking, preferably at a single fixed elongated metric. Those markings are still open. Excluding all four at the same metric suffices to prove nonuniversality; excluding only ray_4 does not.

## Independent Boolean proof replay

The full necessary orientation CNF with all 16 nonrealizable models blocked was regenerated locally from the transcribed archived cocycle, face list and earlier encoding (215 variables, 7,786 clauses). A fresh orbit-blocking SAT run found exactly two orbits, 16 labeled models. To avoid relying on a solver's UNSAT answer, generate_ray4_rup.py also produces a text SAT proof trace from the blocked formula. check_ray4_rup.cpp checks every learned clause by reverse unit propagation from the active database, accepts a logged input clause only if already present or RUP-implied, allows clause deletions, and requires the empty clause. The guard extension is trivially equisatisfiable and fixes the proof producer's internal variable order. The independently checked local trace had 8,018 checked input records, 4,379 RUP additions and 3,976 deletions, and no RAT steps. A compatible Z3 build can regenerate the trace; a different build may produce a different trace or order, in which case the checker must still pass before asserting this replay.

From a scratch directory, using the actual repository paths in place of ROOT:
    g++ -O3 -std=c++17 ROOT/research/type7_focus/check_ray4_rup.cpp -o check_ray4_rup
    python ROOT/research/type7_focus/generate_ray4_rup.py
    ./check_ray4_rup ray4_blocked.cnf ray4_ordered.drat

The exact finite certificate check and the independent RUP replay substantiate the Boolean and algebraic part of the proof. The necessary geometric lemmas remain the only mathematical premises inherited from earlier checkpoints. The generated large proof trace is deliberately not checked into Git.

## Metric-independent consequence

In fact, the final-polynomial proof requires no aspect-ratio hypothesis except to establish unlinking. The labeled cycles (0,2,4,6) and (1,3,5,7) must have **nonzero linking number in every embedded flat Type 7 torus**, conditional only on the strict-support/mixed-side geometric lemma. If they were unlinked, their necessary orientation formula and these final polynomials would give the same contradiction. This applies to all moduli and all markings. In any marking in which the common primitive slope of these cycles is h, the prior geometric diameter theorem therefore gives diameter(T)<|h|.

## Follow-up on other markings

A fresh enumeration of the ray_3 necessary generic sign relaxation with zero horizontal linking produced 66 orbits (1,888 labeled models) under the 32 automorphisms preserving its two short disjoint-cycle pairs. Applying all disjoint-cycle linking checks (691 pairs) and the log-bracket GP LP eliminated one orbit by an exactly canceled final polynomial; the other 65 LPs were feasible. This does not certify realizability of those 65 models or exclude any of them. The analogous ray_1/ray_2 enumeration (identical short-triangle-pair lists) was interrupted after 900 representatives, so it is incomplete. These exploratory counts do not close another marking. No new metric feasibility or infeasibility theorem for ray_1, ray_2 or ray_3 is claimed here.
