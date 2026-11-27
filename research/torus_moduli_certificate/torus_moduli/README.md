# All five realizable eight-vertex triangulations admit the square torus

## Statement

Using Lutz numbering as in Fabian Lander's and Steve Trettel's repository, types 4, 5 and 6 admit embedded intrinsically flat realizations of the square lattice. More strongly, for each of these types, every marked shape `tau = x + i y` satisfying `|x| <= 1/200000000` and `|y-1| <= 1/200000000` has an embedded realization. Similarity scaling yields any lattice scale. Each type has a regular square realization where the joint map of seven cone-angle constraints and two modulus coordinates has rank 9. Thus its embedded flat realization space is locally a smooth 17-dimensional manifold in R^24, and its fixed-shape locus is locally 15-dimensional (8-dimensional modulo similarities). The vertices are labeled; no quotient by combinatorial automorphisms is used.

Type 3 realizes every shape by Doyle, Lander, Schwartz and Trettel, arXiv:2611.21909, Theorem 1.1. Type 7 realizes a neighborhood of the square by Lander, arXiv:2609.10703. Consequently all five known realizable types realize the same open neighborhood of the square shape; the explicit radius above is certified for types 4, 5 and 6, not for type 7. Conditional on the prior type-2 exclusion, this is a classification of *all* possible vertex-minimal triangulations at the square modulus and throughout some open neighborhood of it. The negative certificate and prior existence classification are in `previous_classification/`.

These results do not classify the full modulus images of types 4–7 or prove that any further type is universal. Novelty of the square examples relative to all unpublished prior work is not independently established.

## Reproduction

`python3 certify_moduli.py`

Run with assertions enabled (do not use `python -O`). Requires only the Python standard library. All six records in `moduli_certificates.json` must print PASS. The first three cover neighborhoods of earlier certified examples; the final three cover the same explicit square neighborhood. All inputs are rational decimals; arithmetic is outward-rounded on a grid of denominator 2^100 using integers, including integer square roots. Floating-point printed diagnostics are not used for acceptance. The preconditioners and approximate square configurations were found numerically, but no numerical solver, numerical Jacobian or floating-point residual is trusted by the proof.

`previous_classification/README.md` contains reproduction instructions for the previous enumeration and classification, and `previous_classification/negative/README.md` contains the geometric reduction of the type-2 exclusion. This archive does not claim external peer review of the reduction.

## Proof

### 1. Intrinsic lattice development

Let T be a primal spanning tree of the given triangulated torus. Choose a dual spanning tree D among dual edges not corresponding to primal edges of T. Such a tree exists, since a primal tree is nonseparating. Exactly two edges of the original triangulation belong to neither tree: 24 - 7 - 15 = 2.

In the dual cell decomposition collapse D, so the remaining dual edges generate the fundamental group and dual 2-cells correspond to original vertices. In the abelianized presentation, eliminate the generators corresponding to edges of T by removing leaves of T one at a time: the corresponding dual cell relation contains that edge exactly once (with coefficient +1 or -1), and the only remaining incident primal tree edge is that leaf edge. At the final vertex the remaining relation is redundant, because the sum of all oriented dual 2-cell boundaries is zero. Thus the two residual dual edges, closed by paths along D, give a Z-basis of H_1(torus,Z). Their directions may be reversed by convention without changing this conclusion.

Develop the root oriented triangle in R^2, with its first vertex at (0,0) and second vertex on the positive horizontal axis. Develop all other triangles along D. For a new triangle (a,b,c), ordered positively in the oriented complex, use the known planar positions A,B of its first two vertices. Let u=p_b-p_a, w=p_c-p_a in R^3, and let J denote positive 90-degree planar rotation. The third developed vertex is

    C = A + (u.w / |u|^2)(B-A) + (|u x w| / |u|^2) J(B-A).

This uses only arithmetic and square roots. The code checks opposite edge orientations when passing between the triangles. A residual dual edge connects two already developed faces. The difference of the two copies of the same endpoint in these charts gives the translation of the corresponding closed dual walk, once the metric is flat. The two resulting periods form a lattice basis: a closed orientable flat torus is R^2 modulo translations, and the two walks form an integral homology basis. The integer change-of-basis matrix U in the certificate has determinant +1 or -1. Apply U to these two periods to obtain (u,v). The marked complex shape has coordinates

    x = (u.v)/|u|^2,   y = det(u,v)/|u|^2.

The target y is positive. If x=0,y=1, then u and v are perpendicular and equally long; the torus is square. Off the flat locus the same formulas are a smooth extension of the modulus near nondegenerate triangles and nonzero u, which is all the fixed-point argument requires.

### 2. Simultaneous prescribed flatness and modulus

For each vertex v define S_v as the sum of its incident triangle angles. The first seven components of H are sin(S_v), computed by complex multiplication of the normalized dot product and cross product norm for each angle. The last two components are the modulus coordinates above. As in the previous existence certificate, on the entire interval box the angle bounds ensure 0 < S_v < 4*pi and cos(S_v)>0. So a zero of the first seven components implies S_v=2*pi at these vertices, and the sum of the eight cone angles, 16*pi, implies the same at the eighth.

Fix 15 of the 24 vertex coordinates at the rational seed. For the other 9 coordinates, let z_0 be their seed and X the closed infinity-norm ball of radius R about z_0. Define h_0=(0,...,0,x_0,y_0), with the desired rational center (x_0,y_0). For any h=(0,...,0,x,y) satisfying max(|x-x_0|,|y-y_0|)<=rho, use

    G_h(z)=z-A(H(z)-h)

with the supplied rational matrix A. The verifier evaluates H(z_0) and an interval enclosure of its 9-by-9 Jacobian throughout X. For the flatness components, use the analytic angle derivatives; for the modulus components, use interval forward-mode automatic differentiation of the development formulas. Nonzero denominators and positive square-root arguments used in differentiation are checked by interval arithmetic. All bounds are outward-rounded.

The checked inequalities are:

    beta >= ||A(H(z_0)-h_0)||_infty,
    q >= sup_X ||I-A DH||_infty,
    L >= max_i (|A_i,8| + |A_i,9|),
    q < 1,   beta + q R + L rho < R.

The norm is the induced infinity norm, and matrix column numbers in the expression for L are 1-based. These inequalities give a contraction of the closed ball into its interior for *every* target in the modulus rectangle. By Banach's theorem there is a unique fixed point in the chosen nine-coordinate slice. The q<1 bound implies A and DH are invertible (Neumann-series criterion), so H=h there. The check proves an uncountable continuum of prescribed shapes with a single finite computation, not a sample of moduli.

### 3. Embeddedness

Throughout each box all 70 four-vertex affine determinants have strict signs. The affine circuit test in `certify_positive.py` excludes all intersections of disjoint edges and faces. In general position this also excludes unintended face-face intersections: if faces are disjoint an intersection reaches a boundary edge; if they share one vertex any intersection beyond that vertex reaches an opposite edge of at least one face; and if they share an edge their planes intersect only in the line of that edge. Nondegenerate faces and no collinear triples are guaranteed by the strict determinant checks. Thus each fixed point is an embedded triangulated torus.

### 4. Dimension

Invertibility of the nine-coordinate Jacobian at each square solution implies rank 9 for the joint map in the 24-dimensional ambient coordinate space and rank 7 for the flatness equations alone. The implicit function theorem, with embeddedness open, yields dimensions 24-9=15 for fixed shape and 24-7=17 for the flat locus. The group of Euclidean similarities has dimension 7 and acts freely on a labeled nondegenerate noncoplanar configuration, so the respective local quotient dimensions are 8 and 10. Equivalently, fixing the actual lattice scale and quotienting by Euclidean isometries leaves 8 dimensions for the fixed-metric locus.

## Attribution and limitations

The triangulations and starting seeds derive from Fabian Lander and Steve Trettel, https://github.com/FabianLander/low-vertex-flat-tori, `src/core/triangulations/eightVertex.ts` and `data/flat-embedded/type-{4,5,6}.csv`. The numerical constrained optimization to move types 4–6 to the square modulus and the exact interval certificates are the work of this attempt. Their published work already provides square/hexagonal realizations on other types and a modulus-submersion method; this proof uses a related fixed-point approach with an explicit target rectangle. The square seeds and certificate parameters are included, so reproducing the heuristic search is unnecessary. No claim of a computer-free proof, proof of universality for types 4–7, or priority relative to all numerical experiments is made.
