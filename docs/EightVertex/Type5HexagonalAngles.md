# The anchor face of a hexagonal Type 5 embedding

**In any embedded Type 5 realization of the hexagonal flat torus, face 125 is a facet of the spatial convex hull.** All five other vertices lie strictly on the same side of its plane. Of the 751 candidate spatial determinant sign patterns up to symmetry, the angular inequalities below exclude 401, including all 236 with vertices on both sides of 125. On the 23 tetrahedra whose six edges belong to the triangulation, the other 350 patterns give 12 classes. Existence in any of those classes would settle universality. [Integer certificate](../../scripts/type5_rectangles/hex_angles.py) · [Certificate data](../../scripts/type5_rectangles/hex_angle_certificates.json)

## Angles in a winding triangle

Normalize the periods to $A=(1,0)$ and $B=(1/2,\sqrt3/2)$. In the square marking the graph has 18 nonfacial three-edge cycles. The winding $H$ of each oriented cycle is one of $\pm A,\pm B,\pm(B-A)$, all of length one. The marking orbit theorem permits this marking at the hexagon. Each spatial edge realizes its marked displacement and is strictly shorter than every alternative lattice lift. If the three marked edge vectors around a winding triangle are $d_1,d_2,d_3$, each $H\cdot d_i<1/2$. Their sum is $H$, so each $H\cdot d_i>0$ as well. Write $\delta_i\in(-\pi/2,\pi/2)$ for the directed angle from $H$ to $d_i$. [Marking orbits](../../OrigamiTorus/Winding/WindingOrbits.lean) · [Strict lift comparison](../../OrigamiTorus/Winding/ShortestWinding.lean)

At a corner between two successive directed edges let $\alpha$ be the interior angle of the spatial triangle. If the incident edges have lengths $l_i,l_j$, put $X_i=1/(2l_i)-\cos\delta_i$ and define $X_j$ in the same way. Both are positive by strict shortestness. The opposite side has squared length $|H-d_i-d_j|^2$. Expanding this squared length and applying the spatial cosine law gives

$$
\cos\alpha=\cos(\delta_i+\delta_j)-2X_iX_j.
$$

Consequently $\alpha>|\delta_i+\delta_j|$. The other two hexagonal period directions give a second strict bound

$$
\alpha > |\delta_i-\delta_j|-\pi/3.
$$

To see this, the first bound suffices when the angles have the same sign or when at least one has magnitude at most $\pi/6$. In the remaining case interchange the two indices so that $\delta_i>\pi/6$ and $\delta_j<-\pi/6$. Strict shortestness against the unit periods at headings $+\pi/3$ and $-\pi/3$ relative to $H$ gives

$$
 X_i>\cos(\delta_i-\pi/3)-\cos\delta_i=\sin(\delta_i-\pi/6)>0,\qquad
 X_j>\cos(\delta_j+\pi/3)-\cos\delta_j=-\sin(\delta_j+\pi/6)>0.
$$

Substitution in the cosine identity gives $\cos\alpha<\cos(\delta_i-\delta_j-\pi/3)$ by the product-to-sum identity. The angle on the right belongs to $(0,\pi)$, proving the bound. Lean verifies the squared-distance product identity, the comparisons with two further equal-length periods, and both strict angle bounds in radians. [StarDirections.lean](../../OrigamiTorus/EightVertex/Type5/StarDirections.lean)

## From spatial angles to height orders

For cyclically oriented face $abc$, its spatial angle at $a$ equals the counterclockwise turn from the intrinsic ray $ab$ to $ac$. The verifier stores one heading per edge and unwraps it in the intersection of the open semicircles prescribed by the winding triangles containing it. At each face corner precisely one multiple of $2\pi$ puts the turn in $(0,\pi)$, as the verifier checks from the sector endpoints. The face angles around each vertex sum to $2\pi$. Together with the two winding-triangle bounds, these give linear equalities and strict inequalities in the edge headings and spatial angles. All constant terms are integers in units of $\pi/6$.

Choose a uniformly random spatial direction $n$ and order the eight vertices by $n\cdot r_i$. Ties have measure zero. The angle $\angle bac$ divided by $\pi$ is the probability that $a$ lies between $b$ and $c$ in this order. Indeed, project $n$ onto the plane of the two rays. Its azimuth is uniform, and the dot products with the two rays have opposite signs on two arcs of length $\angle bac$. Order reversal preserves betweenness, leaving 20,160 possible orders to test.

For five labels in general position, the alternating four-point determinants give their affine dependence. Its positive and negative parts have the same barycenter after normalization. A height order putting the positive part entirely above the negative part, or entirely below it, is therefore impossible. This filters the possible orders using only the signs of the 70 determinants.

Each of nine integer linear combinations in the certificate cancels every intrinsic edge heading. Equality rows have arbitrary multipliers. Inequality rows have nonnegative multipliers with at least one positive. Thus each combination must be strictly negative. Its value is the expectation of an explicit integer function of the height order. If that function is nonnegative on every order permitted by a sign pattern, that pattern is impossible. The verifier evaluates the functions with exact integer arithmetic.

## Coverage of the sign patterns

The fixed-period perturbation theorem gives a general-position embedding at the same hexagonal modulus arbitrarily close to any hypothetical embedding. Every vertex has a strict supporting plane relative to its neighbors. The generic determinant signs therefore satisfy the Grassmann–Plücker relations, the signed affine dependence on each five-set, the disjoint edge–face clauses, and the clauses excluding a vertex from the convex hull of its neighbors. [Fixed-period perturbation](Type5Regularity.md) · [Strict support](../../OrigamiTorus/EightVertex/Type5/StrictSupport.lean)

At each vertex at least one incident face plane has neighbors on both sides. Otherwise, under central projection from the vertex to a plane cutting every neighbor ray, all the edges of the simple link polygon support its convex hull. The polygon is convex. A generic great circle then crosses its spherical link at most twice. An open set of great circles misses it by strict support. The expected number of crossings is strictly less than two, whereas the betweenness formula applied to the successive arcs gives expected crossing count $2\pi/\pi=2$.

The verifier checks the six face-list automorphisms and their integral isometries of the hexagonal marking. It includes both choices of spatial orientation by normalizing one determinant sign. Blocking the 4,506 labeled sign assignments from the 751 orbits gives a propositional contradiction. Its reverse-unit-propagation proof is replayed independently of the solver. The nine angular certificates then exclude all 236 split orbits and 165 of the 515 orbits with the five vertices on one side. Each of the anchor tetrahedra $125i$ is a clique, so its determinant is already nonzero in an arbitrary embedding. Its sign persists under the fixed-period perturbation. This transfers the supporting-face conclusion to every hexagonal embedding. [Archived sign patterns](https://github.com/vltanh/lean4-origami-torus/blob/fe5a6eee0cf14dc8cfb0614505d63812f1bbfa25/research/type5_focus/full_sign_orbits5.json) · [Clique independence](../../OrigamiTorus/EightVertex/Type5/StrictSupport.lean)

Every surviving orbit also has a supporting nonfacial triangle sharing an edge with face 125. After a hexagonal marking symmetry it is either 123 or 126. The verifier checks the supporting signs and the nonzero winding of each candidate. For a possibly nongeneric embedding, pass to a subsequence in the fixed-period perturbation with the same triangle. Its vertices remain noncollinear in the limit, since the three edges form an embedded three-cycle. Its limiting plane therefore supports the convex hull, with other coplanar vertices allowed. The three-cycle bounds a disk in the exterior. To construct it, take the cone from a point strictly beyond the supporting plane to the three edges. The interior of this disk lies strictly outside the convex hull. Its boundary represents a shortest lattice vector. This singles out a unique unoriented systolic slope that bounds an exterior disk. Indeed, boundaries of two oriented disks in the same complementary component have algebraic intersection zero on the torus. After a small transverse perturbation, their signed intersection points on the boundary form the boundary of their compact oriented one-dimensional intersection. Any two distinct unoriented systolic slopes of the hexagonal lattice have algebraic intersection of absolute value one.

From a built checkout with NumPy and the Lean toolchain's CaDiCaL, replay the sign coverage and the angular exclusions together.

```sh
python -m scripts.type5_rectangles hex-angles
```

The supporting plane also excludes planar folding mask 11149 as a nondegenerate limit at these periods. Nine strict planar orientations would make the relative interiors of faces 012 and 256 meet. [Projected-cone proof](Type5PlanarMasks.md#a-planar-limit-excluded-by-the-hexagonal-anchor-face)

## Recovering radii at a universal vertex

At vertex 2, fix the seven intrinsic and spatial unit ray directions. Write $u_i$ for the reciprocal length of ray $i$. On a chord $ij$ the shifted length equation is a product of two strictly positive factors, one strictly increasing in $u_i$ and one strictly increasing in $u_j$. Its right side depends only on the directions and the marked period. Comparing any two realizations, a strict increase at one endpoint therefore forces a strict decrease at the other. On the chord triangles 035 and 146 a strict change would reverse sign three times. This fixes the six radii there. Chord 17 fixes the seventh radius. Lean checks the chord incidences and proves this uniqueness for arbitrary independent periods, including the hexagonal ones. [Radius uniqueness](../../OrigamiTorus/EightVertex/Type5/StarDirections.lean)

For the hexagonal existence test one can now orient the perpendicular axis at the anchor face so that all five heights are positive. The fixed-period real-algebraic formula enforces these strict signs at $y^2=3/4$ and uses a hexagonal symmetry to make either 123 or 126 supporting. [Existence formula](../../scripts/type5_rectangles/sharp_query.py)

## Twelve feasibility tests in intrinsic coordinates

Fix $p_1=0$ and write the other seven intrinsic vertices in the lattice basis $A,B$. Their 14 real coordinates determine each marked squared length $d_{ij}$ by the form $x^2+xy+y^2$. Set $d_{ii}=0$ and $g_{ij}=d_{1i}+d_{1j}-d_{ij}$ whenever the pair is an edge. These are twice the desired spatial Gram entries based at vertex 1. Let $C=(g_{ij})_{i,j=2,5}$, $\Delta=\det C$ and $u_i=(g_{2i},g_{5i})$. For the five nonanchor vertices, define

$$
H_{ij}=\Delta g_{ij}-u_i^T\operatorname{adj}(C)u_j
$$

on the diagonal and on the six pairs joining a root $i\in\{3,4\}$ to a leaf $j\in\{0,6,7\}$. In a spatial realization with signed heights $z_i$ above face 125, $H_{ij}=2\Delta z_i z_j$. The supporting-face theorem makes all five diagonal and six mixed entries strictly positive.

For each root–leaf pair, set the determinant of the $4\times4$ matrix $(g_{ab})_{a,b\in(2,5,i,j)}$ equal to zero. Each of these six equations has total degree six in the intrinsic coordinates. Indeed, the quadratic part of the Gram matrix is twice the Gram matrix of the four unshifted intrinsic vectors and has rank at most two. The remaining entries are affine because the period shifts are constant. In the multilinear determinant expansion, at most two quadratic columns contribute, giving degree at most six. Direct polynomial expansion gives equality in all six cases. Multiplication of the determinant by $\Delta$ gives $H_{ii}H_{jj}-H_{ij}^2$. Conversely, the anchor face has positive area, so $C$ is positive definite. Place its three vertices in a plane and project each other vertex horizontally using its two prescribed inner products. Giving it height $\sqrt{H_{ii}/(2\Delta)}$ then realizes its distance to all three anchors. The six equations and $H_{ij}>0$ give the correct product of heights on each root–leaf edge. These are all 24 edges. The Lean theorem `realize_cliques` constructs the five spatial points simultaneously from the anchor vectors, inner products and six vanishing determinants. Their prescribed norms and inner products give all edge lengths by polarization. [HexagonalMetric.lean](../../OrigamiTorus/EightVertex/Type5/HexagonalMetric.lean)

The 23 four-vertex cliques have nonzero determinants, including in nongeneric embeddings. List them in increasing lexicographic order and set bit $k$ when the $k$th determinant has the same sign as the first, starting at bit zero. The least such integer under the six label symmetries identifies a class. The verifier computes these signatures for all 350 surviving spatial patterns. In increasing order the hexadecimal class identifiers are

```text
dad  def  dfd  f87  e879  1697b  20787  28687  286d7  2e051  89e87  89eff
```

Each signature can be tested directly from the intrinsic lengths. For a clique $q$ choose a nonanchor $i\in q$ and put $t=(1,2,5,i)$. The union is also a clique. The three-by-three cross Gram matrix of the edges of $q$ and $t$ based at their respective first vertices therefore uses only known squared lengths. Its determinant is the product of the two oriented spatial volumes. The second factor has the same strict sign for every $i$. The quadratic part of this cross Gram matrix likewise has rank at most two, so its determinant has degree at most five. For clique 1256 both volumes are the same. This positive reference product fixes the absolute sign of all 23 quintics in each class.

To test spatial embeddedness, use the affine coordinates $(u_i,2\Delta z_3 z_i)$. Their third coordinate is zero at the anchors, $H_{33}$ at root 3 and $H_{3j}$ at each leaf. At root 4 it is $H_{33}H_{40}/H_{30}$. Multiplying its homogeneous row by the positive denominator preserves every determinant sign. In each of the twelve classes, four to seven additional strict determinant signs suffice for embeddedness. Number the 70 increasing quartets in lexicographic order starting at one. A positive index requires the same sign as the first clique, and a negative index requires the opposite sign. For example, the additional list for class `f87` is $-16,26,47,55,61,67$. The verifier checks that every one of the 350 surviving orbits has a canonical labeling satisfying its entire list. [Signed lists](../../scripts/type5_rectangles/hex_angle_certificates.json)

For sufficiency, suppose a disjoint edge and face cross transversely in general position. The signed affine dependence of their five vertices has the edge endpoints on one side and the face vertices on the other. The verifier asks whether any such dependence can occur subject to the Grassmann–Plücker signs, the mixed signs of each affine dependence, the 23 clique signs, and the additional list. It replays a propositional refutation in each of the twelve cases. This implication also holds if some untested determinants vanish. At a contact, choose points in the relative interiors of the edge and face arbitrarily close to the contact point. Translate the edge to make those points coincide and, if necessary, rotate it slightly about that point to make the crossing transverse. Their vertex sets are disjoint, so these perturbations are independent. Transverse crossing persists on an open set containing general-position placements, and the stipulated strict signs persist there as well. This would contradict the refutation. [Separation verifier](../../scripts/type5_rectangles/hex_angles.py)

The intrinsic polynomial test imposes those signs on the homogeneous rows, all strict Voronoi comparisons and positive orientation of the 16 intrinsic faces. The marked area formula identifies the resulting development with the hexagonal torus. Conversely, any embedding admits a general-position perturbation at these periods and a relabeling into one of the verified cases. [Fixed-period perturbation](Type5Regularity.md) · [Quotient and separation arguments](Type5Rectangles.md#from-signs-to-a-torus)

Consequently **Type 5 is universal if and only if at least one of these twelve real polynomial systems is feasible**. With the optional Python package `z3-solver`, export their disjunction or substitute a class identifier for `all` to export just that case. The exporter only constructs the formulas. Feasibility remains open. [Intrinsic-coordinate exporter](../../scripts/type5_rectangles/hex_metric.py)

```sh
python -m scripts.type5_rectangles.hex_metric all
```
