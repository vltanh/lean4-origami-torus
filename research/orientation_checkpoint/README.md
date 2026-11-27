# Orientation chambers for the remaining eight-vertex paper-torus types

**Status:** Types 4, 5 and 7 are still unresolved as universality questions. This checkpoint gives a general nondegeneracy lemma, an independently checked finite orientation reduction, and a certified counterexample to a relaxation of the Type 5 hexagonal embedding problem. It does not establish an embedding of the hexagonal Type 5 torus or a nonuniversality theorem. Previous audit qualifications still apply.

## 1. Strict support and nondegenerate cliques

Let a vertex v of an eight-vertex paper torus have spherical link L. Embeddedness makes L a simple polygon, and intrinsic flatness gives length 2 pi. By the hemisphere lemma (Schwartz, *Vertex-Minimal Paper Tori*, Lemma 2.1, https://arxiv.org/abs/2507.14998), L is in a closed hemisphere. Suppose it is not in any open hemisphere. Then the origin belongs to the convex hull of its points on the boundary equator: otherwise a small tilt of the hemisphere normal makes all dot products positive. More directly, the failure of strict support implies the origin is in the convex hull of L, and every nonnegative dot product with the closed hemisphere normal must vanish on the support of a convex combination giving zero.

By planar Caratheodory, either the equatorial set has an antipodal pair, or there are three points whose convex hull contains the origin in its relative interior. In the first case both paths around L between the antipodal points have length at least pi and hence both are great semicircles. In the second case the three pairwise minor-arc distances sum to 2 pi, so the three paths joining the points realize these distances; the polygon is the equator. If the two semicircles are distinct and not on one great circle, their endpoints are corners of the link and thus actual incident edge directions. If the link is a great circle, the whole star is planar.

In the planar case the star can be replaced by a triangulation of its planar boundary polygon with no new vertices. In the distinct-semicircle case split the star along the straight segment joining the two antipodal neighbors and triangulate each of the two planar boundary polygons without v. Simple planar polygons with collinear boundary subdivisions admit triangulations into nondegenerate triangles without adding vertices (one can triangulate the polygon after suppressing collinear subdivisions and split adjacent triangles back along them). The new edges are inside the original embedded star or on its split line; no new interior diagonal can already be an edge outside the star, since that would intersect the star interior. The replacements therefore produce an embedded simplicial torus with the same metric and seven vertices. This contradicts Schwartz's nonexistence theorem. Thus every vertex has a strictly supporting plane **relative to its neighbors**. This does not mean every vertex is a global convex-hull vertex.

A simple spherical polygon in an open hemisphere with at most three genuine corners has length less than 2 pi: suppress intermediate collinear vertices, then it is a spherical triangle (or a degenerate loop, which is not simple); its perimeter is strictly less than 2 pi by Crofton's formula, since a convex spherical polygon is crossed by a generic great circle at most twice and there is an open set of missing great circles. Hence each vertex has at least four incident edges whose adjacent face planes differ. In addition, at each vertex at least one incident face has neighbors on both strict sides of its plane. Otherwise each link edge supports the entire link, which under central projection to a plane is a convex polygon, again contradicting perimeter 2 pi.

Any K4 of the one-skeleton is a nondegenerate tetrahedron. If four clique vertices were coplanar, their embedded K4 would have one point inside the triangle of the other three (a convex quadrilateral gives crossing diagonals; three collinear points give overlapping edges). This contradicts strict support at that point. This supplies robust strict determinant signs even if other quadruples are coplanar.

Finally, embeddedness, strict support, and the existence of the mixed-side incident face are open conditions on the finite vertex configuration. For embeddedness one can use the positive separation of all disjoint simplex pairs, plus nondegenerate faces; a prohibited intersection of simplices with shared vertices would give an intersection of disjoint subfaces by canceling common barycentric coefficients. Hence a sufficiently small generic perturbation preserves these necessary properties, and preserves all K4 determinant signs. The perturbed configuration need NOT stay flat. Use it only to derive necessary orientation conditions. In particular no actual metric solution with coplanarity is dropped by imposing the K4 sign projection.

## 2. Exact SAT reduction

The Boolean formula in `satgeom.py` is a necessary relaxation, not a sufficient realization test. It uses 70 signed affine determinants, the three-term Grassmann-Plucker sign relations, affine five-point circuits (including exclusion of all disjoint edge-face crossings), the supporting-plane condition (no vertex inside a tetrahedron of its neighbors), and at least one mixed-side face per vertex. It fixes global reflection by setting the first determinant sign positive. The 48 auxiliary variables encode incident mixed-side faces.

| Type | K4 count | Clique sign projections modulo reflection | Generic hull patterns modulo automorphism | Chosen spanning 3-tree branches |
|---|---:|---:|---:|---:|
| 4 | 23 | 120 | 75 | 10 |
| 5 | 23 | 138 | 24 | 7 |
| 7 | 16 | 316 | 29 | 12 |

The counts are satisfying sign patterns of the necessary Boolean formula, not counts of realizable metric configurations. The hull patterns are for generic perturbations, not a claim that actual hulls must be simplicial. The K4 signs are unchanged in the perturbation, so the projection is valid also for degenerate metric configurations. At Type 5 the full generic formula has 4,506 labelled sign models with reflection fixed and 751 orbits under its six graph/triangulation automorphisms. At the hexagonal endpoint the 12 admissible Type 5 markings form a single orbit under the 12 lattice symmetries alone (the action is free), so the automorphism quotient can be combined with the fixed marking there. For other types or moduli do not independently quotient the marking and orientation data without checking the joint action.

The cached clique lists in `clique_signs*.json` were obtained by exact SAT projection. `verify_projection.py` checks that each listed projection satisfies the Boolean relaxation, and that blocking all listed projections and their reflections is UNSAT. It also checks the spanning 3-tree and verifies the branch exclusion independently by exhaustive DPLL. For Type 7 the independent proof uses a 137-clause unsatisfiable subset of the generated blocked formula. The core index list is checked as a subset, and no trust in the core extraction algorithm is required.

Reproduce (Python 3, shared libz3, C++17 compiler; no assertions disabled):

```
g++ -O3 -std=c++17 check_unsat.cpp -o check_unsat
python3 verify_projection.py
python3 verify_hex_relaxation.py
```

Optional enumeration: `python3 hull_orbits.py 4 5 7`, `python3 full_sign_orbits.py 5`. `clique_signs.py` and `tree.py` are the original exploration scripts for projected signs and best trees; they overwrite the JSON lists, so preserve the verified checkpoint data if experimenting. Re-run `verify_projection.py` after regeneration. The fixed certificates were freshly replayed.

## 3. Metric reconstruction from a true spanning 3-tree

Choose the initial triangle (0,1,2). The stored `true_tree` entries `(j,(a,b,c))` mean introduce vertex j using three previously placed neighbors which form a triangle all of whose edges were already used in the reconstruction. The underlying subgraph has 18 edges, leaving exactly six metric equalities to check.

For a fixed marking and modulus, let intrinsic coordinates p determine the 24 squared edge distances d_ij. In a candidate realization put the first triangle in a plane, using its three lengths. Given already reconstructed r_a,r_b,r_c, let U=r_b-r_a, V=r_c-r_a and let G be their 2 by 2 Gram matrix. Define

```
b = ((d_aj+d_ab-d_bj)/2, (d_aj+d_ac-d_cj)/2)
(alpha,beta)^T = G^(-1)b
h2 = d_aj - b^T G^(-1)b
r_j = r_a + alpha U + beta V + s_j sqrt(h2/det G) (U cross V).
```

Every true embedding has det G>0 and h2>0 because these are K4 tetrahedra. The sign s_j is the orientation sign of (a,b,c,j), obtained from the cached sorted clique sign by permutation parity. The formula is the unique solution of the three distance equations with that sign. There are five such signs, one redundant under global reflection. The SAT projection reduces the 16 naive sign choices to 10/7/12. Each branch now has only 14 independent intrinsic coordinates, six residual metric equalities, positivity of the tetrahedral radicands, intrinsic face orientation/marking and shortest-edge conditions, plus exact simplex-intersection constraints. The complete metric system remains continuous; the branch count is not a solved feasibility proof. One can convert the radical expressions into polynomial constraints by introducing positive square roots with exact defining equations. Alternatively use interval or algebraic elimination over the bounded intrinsic domain. For actual coplanar subsets outside the K4s, use the degeneracy-complete circuit checks from the previous checkpoint.

The existing eight-variable Type 5 root/leaf reconstruction is even smaller in continuous dimension. The five heights relative to its universal anchor triangle (1,2,5), ordered (0,3,4,6,7) and normalized to the first positive, have only the seven admissible sign strings `+++++`, `++-+-`, `++--+`, `++---`, `+-++-`, `+-+-+`, `+-+--`. These restrict the earlier radical reconstruction; they do not assert that each quadratic leaf root is uniquely selected by its height sign.

## 4. Exact witness that metric and projected signs are insufficient at the hexagonal endpoint

`verify_hex_relaxation.py` modifies the earlier Type 5 radical core construction at the exact lattice (1,0),(1/2,sqrt(3)/2). The core coordinates are rational inputs chosen from a numerical search. The root/leaf reconstruction satisfies all edge equations identically; integer outward-rounded intervals verify strict face orientations, degree one, strictly shortest edges, nonzero affine determinants and a clique projection present in the Boolean list. However, the same exact circuit tests certify 15 disjoint edge-face crossings. This is an exact **nonembedded** piecewise isometric configuration, not an origami-torus witness. The numerical search alone would not prove this diagnostic.

This demonstrates that the metric equations even with the projected clique-sign constraints do not suffice for a Type 5 obstruction. Full embedding geometry, or additional necessary consequences of it, is required. In particular, do not attempt to prove the relaxed system UNSAT.

## 5. Computational exploration and next direction

The following searches were exploratory and not rigorous global exclusions. `metric_tree_search.py` reconstructs a true 3-tree and optimizes over intrinsic coordinates using JAX and SciPy SLSQP. At the first hex marking of each type, the 7/10/12 sign branches were tried with 5/4/4 starts per branch. None produced a strictly feasible embedded candidate. Best reported numerical margins were approximately 0 (Type 4 and 5) and -5.93e-7 (Type 7). These figures use a particular scaled max-min objective and do not bound the true optimum. The second Type 7 hex orbit was not tried with this new method. `metric_only_search.py` removes the disjoint-face separation inequalities and found the candidate subsequently certified in Section 4. `chamber_search.py` fixes all 70 determinant signs for a Type 5 chamber; the first roughly 50 prioritized chambers were tested before the run timed out, with no positive verified margin. This was not exhaustive over the 751 chambers and would miss actual nongeneric embeddings if used alone. Other preliminary explorations of Gram differences, collapse partitions, and necessary clique distances gave no exclusion, so are not proposed as proof gates.

The recommended next attack is a rigorous branch solver on the seven Type 5 core-height sign families, retaining the full simplex-intersection constraints, or a stronger algebraic consequence of the full orientation chambers. The K4 nondegeneracy lemma gives exact strict radicand constraints that remove false solutions with collapsed complete tetrahedra. For Types 4 and 7, use the true 3-tree reconstruction on the remaining sharp-ray markings; do not infer universality from an isolated endpoint witness. A rigorous exclusion of all marking branches at one metric would establish nonuniversality. There is still no such exclusion here. The scope is restricted to the three remaining types; the lemma also simplifies the earlier Type 2 perturbation argument, but a full independent audit of that proof is not claimed.
