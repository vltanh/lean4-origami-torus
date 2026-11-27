# Classification of eight-vertex paper torus triangulations

Candidate complete classification: Lutz types 3,4,5,6,7 admit embedded intrinsically flat realizations; types 1 and 2 do not. Type 2 is conditional on independent audit of the geometric reduction in `negative/README.md`. The SAT result itself is reproduced. No claim of classification of all possible moduli or connected components is made.

## Sources

- Richard Evan Schwartz, Vertex-Minimal Paper Tori, https://arxiv.org/abs/2507.14998 (seven-vertex impossibility and type 7 existence).
- Fabian Lander, The two most symmetric flat tori as eight-vertex paper tori, https://arxiv.org/abs/2609.10703, especially Section 6 (type 1 impossibility, type 2 suspected impossible, numerical examples of five types).
- Doyle, Lander, Schwartz, Trettel, A Universal 8-Vertex Origami Torus Triangulation, https://arxiv.org/abs/2611.21909 (type 3 universality; Section 6 also reports exact checks on another pattern).
- The Lutz numbering, face data and numerical coordinate seeds are from https://github.com/FabianLander/low-vertex-flat-tori, `src/core/triangulations/eightVertex.ts` and the second rows of `data/flat-embedded/type-{4,5,6}.csv`. The authors' numerical searches are not new here; the interval validation of these three examples is the contribution of this package. See `lutz_faces.json` for the lists.

## Reproduction

Run `python3 certify_positive.py` (standard library only). Do not use `python -O`, since the verifier uses assertions. Each of types 4,5,6 must print PASS. The rational preconditioners in `preconditioners.json` were obtained from numerical column-pivoted QR and matrix inversion; the verifier does not trust these computations and checks all certificate inequalities independently. The numerical coordinates are treated as exact rational decimals. All interval computations round outward on a dyadic grid of denominator 2^100, using integer addition, multiplication, floor division and integer square root. Printed diagnostic decimals are not used for acceptance.

Run `python3 enumerate.py` (requires networkx) for the independent combinatorial enumeration. The complement of each possible one-skeleton has 4 edges, so its non-isolated part has at most 8 vertices. We use all graph-atlas four-edge graphs without isolates and append the only eight-vertex possibility, a four-edge matching. For each complement, require every edge in exactly two faces, connected cyclic links and consistent orientation; Euler characteristic 0 then gives a torus. There are seven orbits. `triangulations.json` records their representatives. Both types 4 and 6 have degree sequence 55666677, but their complement graphs are respectively a length-three path plus an edge and two length-two paths (plus isolated vertices).

For type 2, the permutation from Lutz numbering to the certificate's numbering is (0,4,7,6,5,1,3,2). See `negative/README.md`. From `negative`, run `python3 enumerate_faces.py`, `python3 generate_cnf.py`, `g++ -O3 -std=c++17 check_unsat.cpp -o check_unsat`, and `./check_unsat < torus.cnf`. Expected result UNSAT nodes 38849.

## Proof of the positive certificates

For every face at vertex v, let u,w be its incident nonzero edge vectors, d=u·w, c=||u×w||, and s=||u||||w||. Then (d+ic)/s = exp(i theta) where theta is the triangle angle at v. The product over incident faces is exp(i S_v), where S_v is the cone angle. Let F_v be its imaginary part, and use F=(F_0,...,F_6). Its derivative is cos(S_v) times the gradient of S_v. In particular the angle gradient in u is (d u/(u·u)-w)/c, and the gradient in w is (d w/(w·w)-u)/c. The verifier evaluates these expressions with intervals.

Fix 17 coordinates at the rational seed values, and let the remaining seven vary in a closed infinity-norm ball X of radius r=10^-9 about the seed x0. Let A be the rational matrix from the input. The verifier checks beta=||AF(x0)||_inf < 3*10^-15 and q=sup_{x in X} ||I-A DF(x)||_inf < 2*10^-5. It also checks beta+q*r<r directly with integers. Thus G(x)=x-AF(x) is a contraction of X into itself. Its fixed point has AF(x)=0. Since ||I-A DF||<1, A is invertible, so F=0 there.

The interval checks on every face bound the angle above by pi/4, pi/2, 3pi/4 or pi according to d and c. Summing these rational multiples of pi bounds every S_v strictly below 4pi, and the product real part is positive. Hence F_v=0 implies S_v=2pi for v=0,...,6. The sum of all eight cone angles is 16pi, so S_7=2pi as well. This prevents the spurious solutions that would result from merely checking that sine is zero.

For embeddedness, the 70 affine determinants of all four-element subsets have strictly nonzero interval signs throughout X. This implies distinct vertices and nondegenerate triangles. For every five-element subset, the unique affine dependence has coefficient signs (-1)^i times the complementary determinant signs. The convex hull of a pair and a disjoint triple meet exactly when these coefficients separate into those two sign classes. The verifier excludes every such partition in which the pair is an edge and the triple a face. With general position, two faces sharing an edge meet exactly along that edge. If faces share a vertex, an extra intersection would reach an edge not containing the common vertex; if they are disjoint, an intersection would reach some edge. In both cases there would be a forbidden disjoint edge-face intersection. General position also excludes accidental edge-edge intersections. Thus the whole box consists of embedded triangulations, and the fixed point is a flat embedded torus.

## Status

The positive certificates ran successfully. The negative SAT checker was rerun successfully. The principal remaining review obligation is an independent audit of the geometric strict-hemisphere and non-supporting-face lemmas for type 2 (including coplanar cases), not additional numerical searches. This package does not establish priority for the interval validation, nor universality for each realizable triangulation.
