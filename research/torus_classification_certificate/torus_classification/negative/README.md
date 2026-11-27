# Certificate for the degree-(4,5,5,6,7,7,7,7) origami torus conjecture

Target: Fabian Lander, The two most symmetric flat tori as eight-vertex paper tori, arXiv:2609.10703, Section 6.

Run from this directory:

```
python3 enumerate_faces.py
python3 generate_cnf.py
g++ -std=c++17 -O3 check_unsat.cpp -o check_unsat
./check_unsat < torus.cnf
```

Expected outputs: 12 labelled face lists, one orbit, automorphism group of order 4; 84 variables and 7464 clauses; `UNSAT nodes 38849`.

## Geometric reduction

The graph is K8 minus 01, 02, 03, 12, with universal vertices 4,5,6,7. For any flat embedded realization, the link of a vertex on a small sphere is an embedded spherical polygon of length 2 pi. By the hemisphere lemma (Schwartz, Vertex-Minimal Paper Tori, Lemma 2.1), it lies in a closed hemisphere.

In fact every vertex link lies in an open hemisphere. Otherwise its unit directions have the origin in their convex hull, and a supporting plane through the origin gives either an antipodal pair or three directions on its great circle whose spherical triangle perimeter is 2 pi. In the latter case (without an antipodal pair), equality of length forces the link to be exactly that great circle. A planar star is impossible: its vertices include a K5, using the four universal vertices and the center if the center is nonuniversal, or vertices 3,4,5,6,7 if the center is universal. In the antipodal case the link is the union of two geodesic semicircles. The antipodal endpoints a,b cannot be adjacent (their edge would pass through the center v). Neither is universal, and at least three universal neighbors remain. Two, w,x, lie strictly in the same half-plane of the star bounded by the antipodal line. Then v,a,b,w,x give a planar straight-line K5 minus ab, with both a and b outside triangle vwx. This is impossible: a planar embedding of K5 minus ab has six triangular faces, all incident to a or b (three each), and therefore triangle vwx must separate a and b. Both outside would make its bounded interior a face. This also excludes collinear degeneracies.

Next each flat star has a face whose plane has other neighboring vertices on strictly opposite sides. Otherwise project the star rays radially onto an affine plane transverse to its open hemisphere. Its simple link polygon has each edge on a supporting line of the convex hull of the projected neighbors, so it is the boundary of that hull. The spherical link is then a convex spherical polygon in an open hemisphere, with perimeter strictly less than 2 pi by Crofton's formula (generic great circles meet it at most twice, and an open set miss it). Contradiction.

The strict hemisphere and mixed-side witnesses persist under a sufficiently small generic perturbation. Embeddedness of a finite nondegenerate simplicial embedding is open (also stated in Lander, Section 2.1). Thus if a flat embedded realization existed, a generic embedded realization would satisfy these necessary conditions, even though it need not remain flat. We only use the mixed-side condition at vertices 0,1,2.

## CNF

Use a Boolean sign for each of the 70 sorted 4-subsets, the sign of the affine homogeneous determinant. Ordered signs are alternating. Fix the sign of 0123 by reflection. For every 2-subset S and disjoint a<b<c<d, use the Grassmann-Pluecker identity: [Sab][Scd]-[Sac][Sbd]+[Sad][Sbc]=0. Forbid the 16 of 64 assignments for which all three terms have the same sign.

For each sorted 5-subset C, its unique affine circuit has coefficients proportional to (-1)^i times the determinant of C with i removed. The signs cannot all agree, since the coefficients sum to zero. Each 2-vs-3 partition is forbidden if the pair is an edge and the complementary triple a face: the convex hulls would intersect. Each singleton-vs-four partition is forbidden if all four other vertices are neighbors of the singleton: that vertex would lie in their convex hull, violating strict hemisphere support. Each forbidden sign pattern and its negative is excluded by a clause.

At each of 0,1,2, introduce one auxiliary Boolean per incident face. If true, that face must have other neighbors strictly on both sides. Require at least one such auxiliary per vertex. These are the only auxiliary variables.

The exhaustive checker does standard DPLL unit propagation and branches on an unassigned literal, trying both signs. Its heuristic uses integer scores only; it affects ordering, not correctness. The checker does not use geometry, a nonlinear solver, floating point, or any external SAT library. A separate Z3 encoding of the same necessary conditions also returned UNSAT.

Status: proposed complete computer-assisted proof; requires independent mathematical audit. No claim that this proves existence or nonexistence for any of the other six combinatorial types.
