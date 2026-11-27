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
