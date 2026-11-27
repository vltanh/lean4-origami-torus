# Type 6 is universal: a diagonal-flip proof

## Statement and dependency

The eight-vertex torus triangulation numbered 6 in Lander and Trettel's `low-vertex-flat-tori` repository, with degrees (5,5,6,6,6,6,7,7), admits an embedded piecewise-affine isometric realization of **every** flat two-torus in R^3. At each prescribed modulus there is a regular realization: the seven angle deficits and two marked modulus coordinates have joint differential of rank nine. In particular the local realization space at such a point, for prescribed intrinsic shape modulo Euclidean similarities, has dimension eight.

This is a computer-assisted consequence of Peter Doyle, Fabian Lander, Richard Evan Schwartz and Steve Trettel, *A Universal 8-Vertex Origami Torus Triangulation*, arXiv:2611.21909, specifically their planar families in Section 3.1, Lemma 3.4 and the flatness submersion of Lemma 5.3. Their Section 6 reports a second universal candidate with this degree sequence and exact checks, but does not specify which of the two nonisomorphic triangulations of this degree sequence or give its full proof. We do not claim priority for discovering a second universal type. The argument here gives an explicit transfer from the published Type 3 families to Type 6, with an independently executable new sign certificate. We have not independently re-proved the cited lemmas of the published preprint.

## Reproduction

Run `python3 verify_type6_universal.py` with SymPy installed and assertions enabled. No numerical optimization, numerical sampling, or floating-point arithmetic is used by this verifier. The two strips cover the entire fundamental domain, including the unbounded cusp. The script checks the isomorphism, four convexity inequalities per strip, the original 70 signed volumes per strip (for generic perturbation), and a separating determinant witness for every disjoint edge-face pair of the new triangulation. It uses exact rational coefficients. `verification.txt` records the actual output.

## 1. Retriangulation preserves the planar flat metric and its regularity

Use the Type 3 labeling of the paper. Remove triangles 012 and 152, delete the edge 12, and replace them by triangles 015 and 052, inserting edge 05 (which was absent). This is a legal combinatorial edge flip, and the result is isomorphic to Lutz Type 6. The old-to-new label map, in order of old labels 0 through 7, is (3,7,0,6,1,5,2,4). The script checks the exact face sets.

In each of the two published flattened families, denote the projected vertices by p_i. The signed planar area determinants for triples (1,2,0), (1,2,5), (0,5,1), (0,5,2) have respective signs (+,-,-,+) everywhere on both domains. Thus 12 and 05 cross strictly in their interiors; the two triangles sharing 12 form a strictly convex quadrilateral with cyclic boundary 0,1,5,2. The two intrinsic triangles in Section 3.1 of the paper use the same lifts of both shared vertices, and the planar folding acts by the same rigid isometry on them: their projected images lie on opposite sides of the shared diagonal, so the two isometries agreeing on that diagonal are the same isometry. Flipping the quadrilateral is consequently a genuine retriangulation of the same flat intrinsic torus, and preserves its planar folded image. The new planar family has the same modulus as the old one at each point of the domain.

For every sufficiently small *planar* perturbation of the eight vertices, the quadrilateral remains strictly convex. The sum of the triangle angles at each of its four corners is unchanged when its diagonal is flipped. Hence the seven angle deficit functions of the two triangulations agree on an open neighborhood in the planar coordinate space; their horizontal derivatives agree. The rank-seven result for Type 3 (Lemma 5.3 of the cited paper) therefore transfers verbatim to Type 6.

A smooth extension of the marked modulus can be obtained by developing triangles along fixed dual walks representing an integral basis of the torus homology, as in Lemma 5.1 of the paper. Along the new two-parameter planar family its value is exactly the chosen modulus. Differentiation along the two family directions gives the two independent modulus directions in the kernel of the angle-deficit differential. Thus the combined angle-deficit and modulus map has rank nine on the planar coordinate space. At boundary moduli this differentiation is valid locally: all triangle areas and the flip convexity are strict, and the published rational families extend to open neighborhoods there (the flatness and edge-length identities persist).

## 2. A new embedded vertical lift

Write the modulus as x+iy, with 0<=x<=1/2 and y^2>=1-x^2, y>0. Use precisely the two published planar families, with their stated parameter choices (u,k,lambda). On the first strip 0<=x<=1/6 retain the original lift heights

    (0,0,-11,-1,-3,-15,0,977).

On the second strip 1/6<=x<=1/2 use the new heights

    (0,-361,2527,2525,5105,2527,1,19639).

For the new triangulation there are 140 edge-triangle pairs with disjoint vertex sets. For each ordered five-tuple (a,b,c,d,e) representing edge (a,b) and triangle (c,d,e), let V_i be the signed affine determinant after deleting the i-th element, starting at i=0. In general position, if the edge intersects the triangle, the affine dependence has first two coefficients of one sign and last three coefficients of the opposite sign. Its coefficients, up to a common scalar, are (V_0,-V_1,V_2,-V_3,V_4). Therefore an intersection requires

    V_0 V_1 < 0, V_2 V_3 < 0, V_3 V_4 < 0, V_2 V_4 > 0.

It suffices to establish one of the four *strict* witnesses

    V_0 V_1 > 0, V_2 V_3 > 0, V_3 V_4 > 0, -V_2 V_4 > 0.

The last witness is useful for the new second-strip height vector; it avoids requiring every determinant to have a globally fixed sign.

All areas and volumes used here, after multiplying by y>0, have the form A(x)+B(x)y^2 for rational polynomials A and B. To certify a positive sign on an interval [l,r], check that the Bernstein coefficients on that interval of A+B(1-x^2) are all strictly positive, and those of B are nonnegative. Negative signs are certified by applying the same rule to the negative polynomial. This proves the required signs for the entire infinite strip, since y^2-(1-x^2)>=0. No subdivision of either strip is needed.

The verifier certifies 70 of 70 new lifted determinant signs on the first strip, and 67 of 70 on the second. It certifies a strict separation witness for all 140 pairs on each strip. The three uncertified signs in the second strip are 0124, 0127 and 0267; the verifier does not claim that they vanish or have fixed sign. Independently, the original height vectors have all 70 determinant signs certified throughout both strips. In particular, at each fixed modulus, each of the 70 determinants is a nonzero linear functional of the eight height coordinates, not an identically zero function. Thus we can perturb our new height vector arbitrarily slightly (at that fixed modulus) off the finite union of determinant-zero hyperplanes. The finitely many strict witnesses persist under this perturbation. The perturbed lift is in general position and has no disjoint edge-face intersections. This implies embeddedness of the entire complex by the elementary triangle-intersection argument of Lemma 4.2 of the paper. No continuous choice of perturbations across moduli is required.

## 3. Inflate while preserving the intrinsic lattice shape

Fix a modulus and one generic embedded lift z as above. The map Phi recording seven angle deficits and two marked modulus coordinates is smooth near the planar configuration P because all faces are nondegenerate and the developed period denominator is nonzero. Its horizontal derivative has rank nine by Section 1. Choose a nine-dimensional subspace of the horizontal motions on which this derivative is invertible. The implicit function theorem applied to Phi(P+t*z+h) gives horizontal corrections h(t)->0 as t->0 with Phi(P+t*z+h(t))=Phi(P). The ordinary three-dimensional configurations P+z+h(t) remain embedded for small t by openness of embeddedness (all strict determinant witnesses persist). Applying the invertible vertical scaling by t>0 yields precisely P+t*z+h(t), which is therefore also embedded. Its angle deficits vanish (including the eighth by Gauss-Bonnet) and its marked intrinsic shape is the specified one. Scaling and reflection realize the remaining lattices. This proves universality.

The rank-nine property persists at sufficiently small positive t. The implicit function theorem then gives a 17-dimensional local flat locus, a 15-dimensional local fixed-shape locus in R^24, and local dimensions 10 and 8 respectively after quotienting by the 7-dimensional similarity group (the labeled general-position configurations have no continuous stabilizer).

## 4. Scope

This result does not establish universality or nonuniversality of Types 4, 5 or 7. The previously obtained Type 2 nonexistence certificate is not needed for this theorem and its geometric reduction is not independently audited here. The earlier six positive local modulus certificates were rerun successfully; the new proof is global and does not depend on them.

References:
- Doyle, Lander, Schwartz, Trettel, arXiv:2611.21909, https://arxiv.org/abs/2611.21909
- Lander and Trettel, public triangulation numbering and data, https://github.com/FabianLander/low-vertex-flat-tori
