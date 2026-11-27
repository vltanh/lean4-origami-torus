# Type 1 nonexistence

An embedded realization of the Lutz Type 1 triangulation has a vertex whose
cone angle differs from \(2\pi\). The theorem takes a placement of the eight
labeled vertices and injectivity of its affine evaluation on the face complex.
Those hypotheses are the embedding conditions used in the other type results.
[Lean theorem](../OrigamiTorus/Type1/Nonexistence.lean)

The degree-three vertex has three link angles. At flatness their sum is
\(2\pi\), and the complete graph on the center and its three neighbors rules
out opposite rays. The center therefore has strictly positive barycentric
coordinates in the triangle of its neighbors. Removing the star and inserting
that triangle preserves the spatial image, injectivity, and the cone angle at
every other vertex. The remaining seven labels form a complete graph.
[Star](../OrigamiTorus/Type1/Star.lean) · [Collapse](../OrigamiTorus/Type1/Collapse.lean)

If a remaining vertex lacks a strict supporting plane, Carathéodory's theorem
gives a positive dependence on at most four of its link directions. Two
directions in such a dependence would be opposite, so the edge between their
endpoints would pass through the vertex. Three directions have perimeter
\(2\pi\). Equality in the three angular triangle inequalities forces the
entire star into their plane, which would embed a straight-line \(K_5\) in
that plane. Four affinely independent directions in a positive dependence
have perimeter greater than \(2\pi\) in link order, so the whole link does
too. Flatness therefore forces every remaining vertex to be strictly exposed.
[Strict support](../OrigamiTorus/Type1/Support.lean)

Generic perturbation preserves the embedding and all the strict supporting
planes. The signs of the 35 four-point determinants then satisfy the
Grassmann–Plücker clauses and the five-point circuit clauses. The latter exclude
a disjoint edge meeting a face and a vertex lying in the convex hull of four
other vertices. The formula has 2,100 clauses. Lean verifies the 733 clauses used in the
refutation against the formula and checks all 418 reverse-unit-propagation
steps.
[Certificate](../OrigamiTorus/Type1/Certificate.lean) · [Geometric reduction](../OrigamiTorus/Type1/Nonexistence.lean)

Schwartz proves the seven-vertex obstruction using a convex-hull case
enumeration and a spherical Crofton argument. The Lean proof uses the
strict-support criterion and the determinant-sign certificate above for
the collapsed face list. These give a direct proof for the Type 1 reduction.
[Schwartz, §2](https://arxiv.org/html/2507.14998v9#S2)
