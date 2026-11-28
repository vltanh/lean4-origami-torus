# Type 5 embeddings at fixed periods

Fix the two period vectors of a flat torus. At every embedded Type 5 realization, the Jacobian of the 24 squared edge-length equations with respect to the intrinsic and spatial vertex positions has rank 24. In particular, the moduli that Type 5 embeds form an open set. On the sharp ray, at each individual modulus, existence is equivalent to existence with a rational intrinsic core and all 70 spatial tetrahedron determinants nonzero. These statements also apply at the hexagon. They leave the existence question there open.

## Equilibrium at the core

Write $p_i\in\mathbb R^2$ and $r_i\in\mathbb R^3$ for the intrinsic representatives and spatial vertices. With marked period shift $K_{ik}$, the edge equation is
\[
 |r_k-r_i|^2-|p_k-p_i+K_{ik}|^2=0.
\]
A linear dependence of the Jacobian rows is a symmetric edge stress $s_{ik}$ in equilibrium at every vertex, separately for the spatial and lifted intrinsic edge vectors. This follows by differentiating with respect to each of the five coordinates of that vertex.

The core consists of anchors $1,2,5$ and roots $3,4$. Its nine edges omit only $34$. Each root with the three anchors forms a clique tetrahedron, so both tetrahedra have nonzero volume in an embedding. All five spatial points span three-space. Write $\lambda$ for their unique affine dependence up to scale. Both $\lambda_3$ and $\lambda_4$ are nonzero by the two tetrahedron tests. [Clique independence and strict support](../../OrigamiTorus/EightVertex/Type5/StrictSupport.lean)

First add edge $34$ with the shift induced by a path $3,j,4$ through a leaf $j$. The symmetric stress matrix of this complete graph has the edge weights off its diagonal and zero row sums. Spatial equilibrium makes it annihilate the three spatial coordinate columns as well as the all-ones column. These columns have rank four, so any such matrix is $t\lambda\lambda^T$. In particular the nine core rows alone are independent, since a stress on them has $s_{34}=0$.

Suppose $t\ne0$. Substitute these weights in intrinsic equilibrium at roots 3 and 4, divide by $t\lambda_i$, and subtract the two rows. Since $\sum_k\lambda_k=0$, all dependence on the positions drops out, giving
\[
  \sum_{k=1}^5\lambda_k(K_{4k}-K_{3k})=0.
\]
The following are the components of the left side in the square marking, with $(a,b,c,d,e)=(\lambda_1,\ldots,\lambda_5)$. The middle anchor $M$ is the common neighbor between 3 and 4 on this leaf's link.

| Leaf $j$ | $M$ | Period components | Consequence using $\sum\lambda_i=0$ |
| --- | --- | --- | --- |
| 0 | 5 | $(-(b+c+d+e),c+d+e)$ | $a=b=0$ |
| 6 | 1 | $(-(b+e),e)$ | $b=e=0$ |
| 7 | 2 | $(-(b+c+d+e),e)$ | $a=e=0$ |

Under a change $K'_{ik}=L K_{ik}+u_k-u_i$, the sum changes by the invertible linear map $L$. Every valid marking has this form because the period classes give a basis of the lattice and cocycles with the same periods differ by a vertex gauge. Thus a dependence of the ten rows requires $r_3,r_4,r_M$ to be collinear, in any marking. [Kernel-checked period computation](../../OrigamiTorus/EightVertex/Type5/HingeStress.lean) · [Cocycle reconstruction](../../OrigamiTorus/Winding/WindingCocycle.lean) · [Period generation](../../OrigamiTorus/Winding/WindingGeneration.lean)

## Leaf equations and the unfolded hinge

For leaf $j$, set $Y_i=(r_i-r_j,p_i-K_{ij}-p_j)$ for its five neighbors. With $Q(r,p)=|r|^2-|p|^2$ the vectors are null. Their Gram matrix for this form is supported on the five-cycle complementary to the link. Four weights are strictly positive. Indeed, contraction gives nonnegativity, and a zero weight for one of the four edges other than $34$ gives three neighboring rays whose spatial and intrinsic Gram matrices agree. The corresponding clique tetrahedron would be coplanar. The weight for $34$ is half its coherent squared intrinsic distance minus half its squared spatial distance. If it vanishes, we call the leaf saturated. The three $34$ lifts differ by distinct periods. If two saturated, equality in the length bound along both intrinsic straight segments would give the same straight spatial segment, contradicting injectivity at small equal fractions of the two paths. [Five-cycle order and completion formula](Type5FoldedModuli.md#the-two-choices-at-each-leaf) · [Hinge and marking computations](https://github.com/vltanh/lean4-origami-torus/blob/fe5a6eee0cf14dc8cfb0614505d63812f1bbfa25/research/type5_completion/leaf_geometry.md)

At a positive leaf, the Gram determinant is twice the product of the weights. Thus the five rays are independent, and equilibrium forces all five incident stresses to vanish. At a saturated leaf, the remaining path has Gram rank four and inertia $(2,2,0)$. The rays span a four-space of signature $(2,2)$, since spanning five dimensions would make their Gram matrix invertible. Solving its path kernel gives its sole relation $Y_M=\alpha Y_3+\beta Y_4$ with $\alpha,\beta>0$. Strict spatial support at $M$ rules out $\alpha+\beta\le1$, which would place $r_M$ in the convex hull of its neighbors $j,3,4$. The spatial relation now puts a point of the open segment $r_3r_4$ in the open segment $r_jr_M$. If $r_3,r_4,r_M$ were collinear, so would $r_j,r_M,r_3$, contrary to nondegeneracy of face $jM3$. The ten augmented core rows are therefore independent at a saturated leaf.

To finish the rank proof, take a stress on the 24 edges. The only possible nonzero leaf stresses occur at a single saturated leaf. They are proportional to $(\alpha,\beta,-1)$ on neighbors $(3,4,M)$, so their sum $S$ is nonzero if they are nonzero. Eliminate $j$ by adding $s_{ij}s_{jk}/S$ to the weight of each pair $i,k$ among these three neighbors. For either set of coordinates, equilibrium at $j$ writes its position as the stress-weighted average of the three neighbors, which proves this replacement preserves equilibrium at each neighbor. In the intrinsic calculation use the common lifts at $j$. Their differences agree with the existing edge shifts on $3M,4M$ because $jM3,jM4$ are faces, and give exactly the augmented shift on $34$. The new weight on $34$ is nonzero, contradicting independence of the ten augmented rows. All leaf stresses thus vanish, and independence of the nine core rows finishes the proof.

There are 40 position coordinates. The implicit function theorem gives a 16-dimensional solution manifold at fixed periods, or dimension eight after fixing the two intrinsic translations and six spatial rigid motions. The same nonsingular minor in the position variables gives solutions for all sufficiently close periods. Positive intrinsic faces and spatial embedding persist locally. For the latter assertion, finitely many disjoint simplices have positive separation in an embedding. An unintended intersection of two moved faces yields intersecting disjoint subfaces by cancelling common barycentric coefficients and renormalizing.

At a saturated leaf the independence of the ten augmented rows also lets us increase its $34$ deficit while keeping the nine core equations fixed, by the implicit function theorem. For the perturbed core the two leaf completions converge to the original saturated leaf. To see this, the sole ray relation has nonzero coefficient sum $1-\alpha-\beta$, so the four affine core differences span the same nondegenerate $(2,2)$ space as the rays. Subtracting the five null equations gives a line with spacelike direction, depending continuously on the core. The last quadratic on that line has positive leading coefficient and a double root at the saturated leaf. Both nearby real roots therefore approach that root. The other leaves keep their chosen continuous completions. This approximates the original embedding at its exact periods by embeddings with all three deficits positive. At such an embedding the eight coordinates of $p_2,p_3,p_4,p_5$ are free locally after aligning the anchor face and setting $p_1=0$. Anchor projection determines each root up to its height sign, and each positive leaf has two continuous completions.

## Four intrinsic orientation tests

For a core with positive five-cycle weights at all three leaves, intrinsic orientation can be tested before choosing the three completions. At each leaf $j$, take the five coherent neighbor lifts $s_i=p_i-K_{ij}$ in their oriented link order. Every completion has all five face areas of the same strict sign. This sign equals that of the signed area of the polygon through the five $s_i$. Thus it suffices to test the orientation of face 152 and these three polygon areas, all quadratic functions of the core.

To prove this, number the neighbors in the complementary cycle order and write their signed Gram matrix as $D C D$, with $D$ positive diagonal and $C$ the unweighted five-cycle adjacency matrix. Rescale each ray by its corresponding positive diagonal entry to obtain a basis with Gram matrix $C$. In the spectral realization of $C$ with the form $|r|^2-|u|^2$, the two negative coordinates of its $k$th basis vector are a common positive multiple of
\[
   (\cos(4\pi k/5),\sin(4\pi k/5)).
\]
Indeed the Fourier modes of $C$ have eigenvalues $2\cos(2\pi m/5)$, and modes $m=2,3$ form precisely the real negative eigenspace. Consecutive link steps are all $+2$ or all $-2$ modulo five. In the model the negative projections of the five rays therefore turn by a common angle of magnitude $2\pi/5$ and make one full turn around the origin.

The actual signed basis differs from the model by an isometry of the form. Its negative projection has the form $Ar+Bu$. The isometry identity gives $BB^T-AA^T=I$, hence $B$ is invertible and $B^{-1}A$ has operator norm strictly below one. Consider the projections $u+t B^{-1}Ar$ for $0\le t\le1$. Two consecutive link rays span a totally null plane. On that plane $|r|=|u|$, so none of these projections vanishes on a nonzero vector. Each consecutive pair keeps its nonzero orientation throughout the homotopy. Multiplication by $B$ at the end changes all signs by the same factor. The positive ray scalings have no effect on these signs. All five triangles of a completed fan thus have the same orientation. Their signed double areas sum to $\sum_{i\to k}\det(s_i,s_k)$ around the link because the terms containing the leaf position cancel. In particular either completion gives the same sign test, independently of its position and height.

## Sharp-ray bounds from the nine core edges

On the sharp ray, the nine strict shortest-edge comparisons alone imply all four intrinsic orientation tests. In fact, let $T=1/4+y^2$ and write $A_{152}$ for the physical area of the anchor triangle. For each leaf let $A_j$ be half the signed physical double area of its coherent link polygon. Throughout the strict core domain,
\[
 0<A_{152}<\frac{T}{8y},\qquad
 \frac{T}{8y}<A_j<\frac{5T}{8y}\quad(j=0,6,7).
\]
Consequently, start with any such core, choose positive squared heights at the two roots and choose a relative height sign. If all three coherent root-pair deficits are positive, **all eight leaf completions develop facewise isometrically to the prescribed torus**. The other four weights of each cycle compare an actual core edge with a different lift, so they are already positive. Spatial intersections still depend on the chosen completions.

Here is a rational certificate uniform in $y$. Set $U=1/T$ and store the core by $w_i=4U(p_i\cdot A,p_i\cdot B)$ for $i=2,3,4,5$. Append $U$ as a ninth coordinate. A marked shift $mA+nB$ adds $(U(4m+2n),2mU+4n)$ to a difference of $w$ coordinates. The closed shortest-lift conditions for each of the nine edges say that the absolute values of the first coordinate, second coordinate, and second minus first coordinate of the shifted difference are at most $2U,2,2$ respectively. The three period directions $A,B,B-A$ suffice by the reduced-basis nearest-lift criterion. With $0\le U\le1$, these inequalities define a bounded polytope since each vertex is joined to the origin. [Nearest-lift criterion](../../OrigamiTorus/Winding/ReducedNearest.lean)

The polytope has exactly **39 vertices**, all integral in $(w,U)$ coordinates. Thirty-four lie at $U=1$ and five at $U=0$. In particular every intermediate slice is the set of all $(1-U)v_0+Uv_1$ in the first eight coordinates, with $v_0,v_1$ in the respective end polytopes. The zero slice is used only to compactify the domain.

The verifier starts with $[-2,2]^8\times[0,1]$ and clips it one rational halfspace at a time. A cut retains the old vertices on its inside and adds the intersection with each edge whose endpoints lie on strictly opposite sides. Two old vertices form an edge exactly when all the facets tight at both have no third vertex in common. The implementation keeps the full incidence sets, including redundant cuts. The test point $( -1,-11,5,2,-2,6,-5,-11,3)/6$ is strictly inside all the halfspaces, so the intermediate polytopes remain nine-dimensional. Every edge has at least eight common tight constraints. These facts verify completeness of the vertex enumeration.

In $w$ coordinates write $a$ for the anchor double area and $s_j$ for a link's signed double area. The eight functions $a$, $4U-a$, $s_j-4U$ and $20U-s_j$ are polynomials of degree at most two. For each of them, say $f$, the verifier checks for every pair of the 39 vertices $v,w$, including equal pairs,
\[
 4f((v+w)/2)-f(v)-f(w)\ge0.
\]
These are twice the entries of the symmetric matrix of the homogenized quadratic on vertex barycentric coordinates. Nonnegative entries imply nonnegativity on the entire polytope. For each function at least one vertex at $U=1$ has positive value. A relative interior point of a polytope has a convex representation using every vertex with positive coefficient: subtract a sufficiently small positive multiple of their barycenter and renormalize. Apply this to the whole polytope for $0<U<1$, and to its upper face for $U=1$. The nine strict shortest-edge tests place the core in the corresponding relative interior, so all eight inequalities are strict there. Dividing by $2(4U)^2 y$ converts the signed double areas to physical areas and gives the stated bounds. [Exact polytope and quadratic checks](../../scripts/type5_rectangles/sharp_core_bounds.py)

Lean independently proves the same eight strict inequalities directly from the 54 signed core comparisons. It splits on the sign of the first coordinate of vertex 2 for the lower anchor bound, and on the first coordinate of vertex 4 and its sum with that of vertex 3 for the lower bound at leaf 0. In each case a positive integer multiple of the desired polynomial equals a sum of products of nonnegative linear factors with positive integer coefficients. At least one product uses only strictly positive factors, including at $U=1$. The kernel checks all eleven polynomial identities and their signs. [Lean area theorem](../../OrigamiTorus/EightVertex/Type5/SharpCore.lean)

## General position at every sharp modulus

Take $A=(1,0)$, $B=(1/2,y)$ and $y\ge\sqrt3/2$. The Type 5 marking has a single orbit on this ray and at the hexagon. The periods of the cycles $014,015$ in the square marking are $(-1,1),(-1,0)$. The negative row swap from the automorphism group and central inversion on the target identify this with the representative $(-1,0),(-1,1)$. We can thus use the same core coordinates and labeled shifts for any candidate embedding. [Marking orbit theorem](../../OrigamiTorus/Winding/WindingOrbits.lean) · [Automorphism action](../../OrigamiTorus/Winding/WindingAutomorphisms.lean)

For each quartet of vertices $q$ we construct a polynomial $P_q$ in the eight core coordinates and $y$. It vanishes whenever a completion has zero spatial determinant on $q$, or whenever a chart divisor used for $q$ vanishes. The construction below initially has denominators that are powers of the nonzero anchor determinant, which we clear. For every real $y$, the resulting polynomial in the core coordinates is nonzero. Here is the exact check of this last assertion.

Write $z_3,z_4$ for the root heights, $h_i=z_i^2$, $g=z_3z_4$. The root horizontal positions and $h_3,h_4$ are rational functions of the core. Work with $g^2=h_3h_4$ and multiply the spatial height coordinate by $z_3$. For leaf $j$ and intrinsic point $v$, its horizontal projection $\pi_j(v)$ is affine in $v$, determined by subtracting the origin distance equation from the equations at anchors 2 and 5. Write $s_i=p_i-K_{ij}$ and
\[
 L_i(v)=s_i\cdot v+(|p_i|^2-|s_i|^2)/2-r_i^{xy}\cdot\pi_j(v).
\]
The scaled height of the leaf is $L_3(v)$. The second root equation gives $h_3L_4(v)-gL_3(v)=a v_x+b v_y+c=0$. Substitute $v=(t,(-at-c)/b)$ and multiply its homogeneous spatial column by $b$. This gives a column $X+tD$ and the remaining origin distance gives a quadratic $A_jt^2+B_jt+C_j=0$. The formulas for $X,D,A_j,B_j,C_j$ use no division by $b$.

Start with the four-column determinant for $q$, which is multilinear in the leaf parameters. For each leaf in turn, clear higher powers of its parameter by repeatedly substituting $A_jt^2=-B_jt-C_j$, multiplying the whole polynomial by $A_j$ as needed. For a remainder $U+tV$, replace it by $A_jU^2-B_jUV+C_jV^2$, which vanishes if the remainder vanishes at either root. When all leaves have been eliminated, multiply the expression by its conjugate under $g\mapsto-g$. Multiply also by $h_3h_4$ and by the norms of $b$ and $A_j$ for the leaves used. This gives $P_q$ with the asserted vanishing implication.

At each of the following two test cores the anchor determinant is a nonzero constant. Entries are the physical Cartesian coordinates at labels $2,3,4,5$.

| Core | $p_2$ | $p_3$ | $p_4$ | $p_5$ |
| --- | --- | --- | --- | --- |
| I | $(1,2)$ | $(3,5)$ | $(7,11)$ | $(2,-1)$ |
| II | $(-5,-6)$ | $(1,3)$ | $(-3,-6)$ | $(6,3)$ |

For each of the 70 quartets the verifier computes both specializations in $\mathbb Q[y]$ and checks that their greatest common divisor has degree zero. Thus at every fixed $y$ at least one specialization is nonzero. This argument uses only polynomial evaluation at the two test cores and places no geometric assumptions on them. [Exact elimination and coprimality check](../../scripts/type5_rectangles/general_position.py)

The union of the 70 polynomial zero sets at a fixed $y$ has empty interior. Its complement meets each open core neighborhood of an embedding with positive deficits in an open set, which contains rational core coordinates. Desaturation proved above gives the same approximation starting from an arbitrary embedding. Conversely, a completed core with positive oriented intrinsic faces and with separated disjoint edge–face pairs gives an embedded flat torus by degree one and the barycentric argument. This proves the equivalence.

In particular the sharp-ray test at a prescribed $y$ needs only twelve real variables: the eight core coordinates, $g$, and the three leaf parameters. The four equations are $g^2=h_3h_4$ and the three leaf quadratics. Impose $h_3,h_4>0$, nonzero chart divisors, positive face orientations and the strict alternating-cofactor separation tests for all 138 pairs. Use affine columns with leading coordinate one when testing signs, or multiply each column $X+tD$ by its own $b$ to make its leading coordinate $b^2>0$. One can also require every quartet determinant to be nonzero. This test represents all possible embeddings up to the fixed-modulus perturbation. The sharp-ray embedding certificate establishes feasibility for every $y>\sqrt3/2$. Only $y=\sqrt3/2$ remains undecided. [Sharp-ray embeddings](Type5SharpEmbeddings.md) [Orientation and separation tests](Type5FoldedModuli.md#spatial-separation-over-the-full-rectangle)

The exporter writes the first-order formula to SMT-LIB. It represents the physical point $(a,yb)$ by $(a,b)$, so $Y=y^2$ is the only metric parameter and every coefficient is rational. It clears the common anchor determinant, uses the four orientation tests above, and requires all 15 cycle weights to be positive. Each disjoint edge–face pair involves at most two leaves, so only 65 of the 70 spatial determinants enter the formula. A fixed-height formula is satisfiable exactly when that torus embeds. The all-heights formula quantifies $Y$ over the whole real ray and is true exactly when Type 5 is universal. The open sharp-ray theorem reduces that universally quantified statement to the single existential formula at $Y=3/4$. At the endpoint, a second formulation gives twelve cases using only the fourteen intrinsic coordinates. [SMT-LIB exporter](../../scripts/type5_rectangles/sharp_query.py) · [Intrinsic-coordinate tests](Type5HexagonalAngles.md#twelve-feasibility-tests-in-intrinsic-coordinates)

At the hexagon an alternative parametrization has eight rational inputs and only two independent square roots in scaled coordinates. [Hinge chart](Type5HingeChart.md)

At the hexagon the anchor plane supports all five other vertices. The exporter uses the positive sign of the scaled height of root 3 to require positive scaled heights at root 4 and at all three leaves. [Hexagonal angle certificate](Type5HexagonalAngles.md)

With the optional Python package `z3-solver`, the following commands emit the hexagonal and universal formulas.

```sh
python3 -m scripts.type5_rectangles.sharp_query 3/4 > /tmp/type5-hex.smt2
python3 -m scripts.type5_rectangles.sharp_query all > /tmp/type5-all.smt2
```

Run `python3 -m scripts.type5_rectangles core-bounds` for the polytope and the uniform area bounds, and `python3 -m scripts.type5_rectangles generic` for the coprimality checks. Lean checks the normalized area bounds, the finite period-row calculation, and the clique and support lemmas. The differential and density proofs above use those results and the exact Python certificate.
