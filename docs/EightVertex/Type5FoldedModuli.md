# Type 5 embeds every reduced flat torus off the sharp ray

**Type 5 embeds the flat torus for every reduced modulus \(x+iy\) with \(0\le x<1/2\), \(y>0\) and \(T=x^2+y^2\ge1\).** The spatial map is affine and isometric on each of the 16 triangles. This covers all flat tori up to similarity except the sharp ray \(x=1/2,\ y\ge\sqrt3/2\). A second rational family embeds every point of that ray above its hexagonal endpoint. Together these constructions cover every nonhexagonal flat torus. [Sharp-ray embedding theorem](Type5SharpEmbeddings.md)

For the embedding, the periods are \(A=(1,0)\) and \(B=(x,y)\). A single nonplanar family works throughout the stated domain. The proof checks exact bivariate polynomials for the intrinsic triangles and the spatial determinant signs, then verifies a finite implication from those signs to injectivity. Given a lattice with this reduced modulus, the similarity from the normalized intrinsic torus extends the construction to that lattice by rescaling the spatial coordinates by the same length factor. Reflection and rotation preserve every face distance. These certificates run in Python. A separate Lean theorem gives a planar facewise isometry whenever \(0<x\le1/2\), including the entire sharp ray. [Embedding verifier](../../scripts/type5_rectangles/projections.py) · [Lean planar folding](../../OrigamiTorus/EightVertex/Type5/PlanarFold.lean)

## Planar folding on the oblique moduli

Write the representatives in coordinates \((a_i,b_i)=(p_i\cdot A,p_i\cdot B)\). Thus \(p_i=(a_i,(b_i-xa_i)/y)\). Set \(r_i=(p_i,0)\) and use the integral square marking.

| \(i\) | \(a_i\) | \(b_i\) |
| --- | --- | --- |
| 0 | \(3/8\) | \(-T/2+1/4+3x/4\) |
| 1 | \(0\) | \(0\) |
| 2 | \(3/8-3x/4\) | \(-T/2+1/4\) |
| 3 | \(3/8\) | \(1/4\) |
| 4 | \(-1/8+x/4\) | \(1/4\) |
| 5 | \(-1/8\) | \(-T/2+1/4\) |
| 6 | \(1/8\) | \(1/4\) |
| 7 | \(-1/8\) | \(1/4-x/4\) |

For a marked shift \(mA+nB\), equality of spatial and intrinsic squared lengths is the linear equation
\[
2m(a_j-a_i)+2n(b_j-b_i)+m^2+2mnx+n^2T=0.
\]
The table solves every equation. The determinant in dual coordinates is \(y\) times the physical determinant. Lean computes all 16 dual determinants and proves them strictly positive from \(0<x\le1/2\) and \(T\ge1\). The marked area sum gives degree one, hence the source triangles triangulate the required lattice quotient. The resulting map has planar image. [Coordinate identities and positive areas](../../OrigamiTorus/EightVertex/Type5/PlanarFold.lean) · [Degree-one development](../../OrigamiTorus/EightVertex/Type5/ContinuationTorus.lean)

## A nonplanar construction for \(x<1/2\)

Put \(d=1/2-x\), \(U=1/T\), \(w=d-9d^2/32\), \(q=w-1/2\), and \(D=7d/16\). The domain is the whole rectangle \(0<d\le1/2,\ 0<U\le1\). Choose \(p_1=0\) and use the following dual coordinates.

| Vertex | \(p_i\cdot A\) | \(p_i\cdot B\) |
| --- | --- | --- |
| 2 | \(w-d^3 U^2/32\) | \(-T/2+d^{10}U^5/2048\) |
| 3 | \(1/2-d^9 U^5/256\) | \((-q-d^5U^2/64)/(1-2DU)\) |
| 5 | \(q\) | \(-T/2+D\) |

Choose the fourth point by the reflected height-zero leaf equation described for the equal-length arc. Set its first coordinate to \(-3/32\) and add \(d^4/(1024y)\) to the second coordinate obtained from that equation. Place anchors 1, 2, 5 in the horizontal plane, and take positive height at 3 and negative height at 4. The verifier works in the scaled coordinates \((h,yk)\) for a physical point \((h,k)\). Both horizontal coordinates and both squared heights are rational functions of \(d,U\). It checks nonzero denominators for the reduced coordinate formulas, both positive squared heights, all nine core edge equations, and positive area on the anchor face 152. In particular anchors 1, 2, 5 and root 3 span three-space. [Fourth-point equation](Type5Rhombic.md#choosing-the-core) · [Core formulas](../../scripts/type5_rectangles/reduced.py)

### The two choices at each leaf

Fix a leaf \(j\in\{0,6,7\}\). For its five core neighbors let \(K_i=(r_i,p_i-K_{ij})\in\mathbb R^{3,2}\), where \(K_{ij}\) in the second component denotes the marked period shift. Use the quadratic form \(Q(r,p)=\lVert r\rVert^2-\lVert p\rVert^2\). A simultaneous spatial and intrinsic leaf position \(Z\) must satisfy \(Q(K_i-Z)=0\) for every neighbor. Write \(S_{ik}=-Q(K_i-K_k)/2\). This construction uses the positive five-cycle completion argument from the archived Type 5 research. [Positive completion theorem and proof](https://github.com/vltanh/lean4-origami-torus/blob/fe5a6eee0cf14dc8cfb0614505d63812f1bbfa25/research/type5_completion/leaf_geometry.md)

The verifier proves that \(S\) is supported on the five-cycle with the indicated order, with each weight strictly positive.

| Leaf | Order of neighbors in the positive cycle |
| --- | --- |
| 0 | 2, 3, 4, 1, 5 |
| 6 | 5, 3, 4, 2, 1 |
| 7 | 1, 3, 4, 5, 2 |

The entries on the actual link are zero. For the root pair the deficit is \(H-\sqrt{h_3^2 h_4^2}\), where \(h_i\) is the signed root height and \(H\) is rational in \(d,U\). The checker verifies \(H>0\) and \(H^2-h_3^2h_4^2>0\). Each claimed rational sign is established by converting its numerator and denominator separately to tensor-product Bernstein coefficients on the single closed rectangle. All coefficients have the required weak sign and the coefficient at the upper right corner has strict sign. Its basis function is strictly positive at every \(d,U>0\), including along the upper and right edges. The conversions use integer matrices with positive common scaling. [Bernstein conversion](../../scripts/type5_rectangles/bernstein.py)

For completeness, a positive weighted five-cycle is \(S=DCD\) for a positive diagonal matrix \(D\) and the unweighted adjacency matrix \(C\). The five equations for the diagonal entries of \(D\) have a unique positive solution because the cycle has odd length. The inertia of \(C\) is \((3,2)\) and \(H_0=2C^{-1}\) has diagonal and cycle entries \(+1\), other entries \(-1\), and row sums 1. For \(v\ge0\),
\[
v^T H_0v=(\textstyle\sum_i v_i)^2-4\!\sum_{ij\text{ in the complementary cycle}}v_i v_j\ge0.
\]
To see this, normalize the entries to sum to 1 and maximize the edge sum, choosing a maximizer of smallest support. Mass at two nonadjacent supported vertices can be moved to the one with larger neighbor sum without decreasing the objective. Hence the support is a clique, of size at most two, with edge product at most \(1/4\). For strictly positive \(v\), subtract its smallest entry times the all-ones vector. The row sums of \(H_0\) then make the displayed quadratic strictly positive. Taking \(v=D^{-1}\mathbf1\) proves \(c=\mathbf1^T S^{-1}\mathbf1>0\).

Set \(w=S^{-1}\mathbf1/c\) and \(Z_0=\sum_i w_i K_i\). The hyperplane of coefficient vectors with sum zero is \(S\)-orthogonal to \(w\), and its restriction has signature \((2,2)\). On this hyperplane \(Q(\sum_i v_iK_i)=v^TSv\), so the four core differences span a nondegenerate four-space of the same signature. Its normal is spacelike. One continuous nonzero choice of normal \(N\) comes from the signed maximal minors of the four differences, with the signs of the metric applied. Expanding the squared differences gives \(Q(K_i-Z_0)=-1/c\) for all five \(i\). Thus the two solutions are
\[
Z_0\ \pm\ \frac{N}{\sqrt{cQ(N)}} .
\]
They are continuous throughout the parameter rectangle. The four subtracted equations specify the affine normal line, so these are all solutions. Different leaves have no edge in common with one another and their choices are independent.

### Why the chosen faces stay positive

For either choice, the five vectors \(Y_i=K_i-Z\) have signed Gram matrix \(S\). Its determinant is twice the product of the five positive weights, so the vectors are linearly independent. For consecutive neighbors in the *link*, the two intrinsic difference vectors have the same Euclidean Gram matrix as the two spatial difference vectors. This follows from \(Q(Y_i)=Q(Y_k)=0\) and \(S_{ik}=0\). If their intrinsic triangle were degenerate, a nonzero linear combination of the two intrinsic vectors would vanish. The equality of Gram matrices would force the same combination of spatial vectors to vanish, contradicting independence of \(Y_i,Y_k\).

At \((d,U)=(1/4,1/2)\) the checker verifies a choice with all faces positive and all 138 disjoint edge–face pairs separated. Continue each of its three leaf choices by the signed-normal formula. Each leaf face retains its orientation throughout the connected rectangle because its signed area never vanishes. Face 152 was checked separately. This proves positive orientation on all faces and gives the facewise-isometric map on the lattice quotient. The following argument extends spatial separation from that point over the full rectangle. [Quotient and metric argument](Type5Rectangles.md#from-signs-to-a-torus)

## Spatial separation over the full rectangle

Write \([abcd]\) for the oriented spatial tetrahedron determinant in increasing label order. The 17 signs below imply the alternating-minor separation test for every disjoint edge–face pair.

| Kind of tetrahedron | Signed brackets |
| --- | --- |
| Four core vertices | \(1234-,\ 1235+,\ 1245-,\ 1345-,\ 2345+\) |
| One leaf | \(0125+,\ 0135-,\ 0234-,\ 0245+,\ 1236-,\ 1247+,\ 1357-,\ 2357-,\ 2456-\) |
| Two leaves | \(0246+,\ 0456+,\ 2367-\) |

The verifier reads these signs at the base point and allows each of the other tetrahedron determinants to have either strict sign or to vanish. For any pair of common columns, the three signed products in the Grassmann–Plücker relation sum to zero. For any five homogeneous affine points, the five alternating four-point determinants also sum to zero by expansion along a repeated row of ones. Each zero sum containing a strict sign must contain the opposite strict sign. The verifier encodes these necessary conditions, the 17 signs, and the assertion that at least one of the 138 separation tests fails. It checks a resolution refutation by reverse unit propagation. Thus throughout any region with these 17 signs, every disjoint edge–face pair is separated. The finite incidence and barycentric argument then gives spatial injectivity. [Sign implication and replay](../../scripts/type5_rectangles/separation.py) · [From disjoint pairs to an embedding](Type5Rectangles.md#from-signs-to-a-torus)

To show the brackets keep their base-point signs, it suffices to exclude their zeros throughout the connected parameter rectangle. Scale the spatial coordinates to \((r_x,yr_y,r_z/h_3)\), where \(h_3>0\). All core coordinates lie in \(\mathbb Q(d,U)(g)\), with \(g=\sqrt{h_4^2/h_3^2}\). The five core brackets are computed directly. For an element \(a+bg\) the signs of the rational functions \(a,b\), or of \(a^2-b^2g^2\) and the dominant term, suffice on the cells checked here. All rational sign checks cover the full rectangle. [Core and one-leaf signs](../../scripts/type5_rectangles/projections.py)

### Planes containing a leaf

Fix a spatial plane through a core vertex \(a\), with nonzero covector \(n\) in scaled coordinates, and write \(t_i=n\cdot(r_i-r_a)\) for the five core vertices. Suppose the completion \(Z\) of leaf \(j\) lies spatially in this plane. The signed rays \(K_i-Z\) are a basis with Gram matrix \(S\), and the inner products of the metric dual of \((n,0)\) with this basis are precisely the five values \(t_i\). Consequently
\[
t^T\operatorname{adj}(S)t-\det(S)
 \left(n_x^2+y^2n_y^2+n_z^2/h_3^2\right)=0.\tag{1}
\]
This necessary condition holds for either completion of the leaf.

In cyclic order, write \(w_i=S_{i,i+1}\) and \(m_i=w_{i+1}w_{i+3}\), with indices modulo five. The diagonal scaling of \(C\) above gives \(\det S=2\prod_i w_i\) and \(\operatorname{adj}(S)_{ik}=(H_0)_{ik}m_i m_k\). For three core vertices and one leaf, take the plane of the core triple. Its three entries in \(t\) vanish, so the first term of (1) reduces to the square of \(m_i t_i+(H_0)_{ik}m_k t_k\) for the other two indices. For each of the nine one-leaf brackets the verifier shows that the left side of (1) is nonzero on the full rectangle. This also excludes collinearity of the core triple, which would give zero for its cross-product covector and the entire expression.

### Planes through two leaves and a core edge

For each of the final three brackets, let \(e\) be the difference between its two scaled core points. One is an anchor and the other is a root of nonzero height. Thus \(e_z\ne0\), and \((e_z,0,-e_x)\), \((0,e_z,-e_y)\) span the covectors annihilating \(e\). Substituting their linear combination with coefficients \(s,t\) into (1) gives a homogeneous binary quadratic for each leaf. A common plane requires a common projective root of the two quadratics. That implication also holds if a leaf lies on the core edge.

For coefficients \((A,B,C)\) and \((D,E,F)\) of \(s^2,st,t^2\), the resultant is
\[
(AF-CD)^2-(AE-BD)(BF-CE).
\]
A nonzero resultant excludes a common root, including one at infinity. The verifier clears denominators and removes common polynomial factors after certifying their nonvanishing. It takes the quadratic-field norm of the remaining resultant. The final norms for \(0246,0456,2367\) have bidegrees \((1528,824),(1472,796),(1352,744)\) respectively. Each has a strict sign throughout the parameter rectangle.

For a norm polynomial \(P\) of bidegree \((m,n)\), the checker expands
\[
 [2(1+r)]^m(1+s)^n P\left(\frac1{2(1+r)},\frac1{1+s}\right).
\]
The coefficients all have one weak sign and the constant term has that strict sign. Since \(r,s\ge0\) parametrize the whole domain, this proves the norm never vanishes. The expansion uses two exact integer polynomial shifts. This establishes the last three signs and finishes the embedding proof. [Binary pencils, resultant and exact sign check](../../scripts/type5_rectangles/two_leaves.py)

## Why the construction stops at the sharp ray

At \(d=0\) the prescribed horizontal coordinate of vertex 5 is \(q=-1/2\). Edge 15 has zero shift and starts at the origin. Its displacement and the alternative obtained by adding \(A=(1,0)\) then have exactly the same squared length, for every vertical coordinate of vertex 5. In an embedded facewise-isometric torus, every edge is strictly shorter than each of its alternative lifts. Thus no assignment to the three leaves can turn these limiting core coordinates into an embedding. This leaves the sharp ray as a separate existence problem. [Strict period comparison](../../OrigamiTorus/Winding/ShortestWinding.lean)

## Sixteen nonplanar completions on the sharp ray

For each sharp modulus, a different core gives sixteen nonplanar maps, each facewise isometric on the actual lattice quotient. **Every one of these sixteen maps has a transverse intersection between a disjoint edge and triangle.** This excludes this choice of four intrinsic vertices on the entire ray, including at the hexagon.

Fix $x=1/2$, $T=x^2+y^2\ge1$, and use the square marking. The entries are the intrinsic coordinates $(p_i\cdot A,p_i\cdot B)$.

| Vertex | Dual coordinates |
| --- | --- |
| 1 | $(0,0)$ |
| 2 | $(-1/12,-T/2+1/12)$ |
| 3 | $(5/12,1/6)$ |
| 4 | $(-1/6,T/3-1/6)$ |
| 5 | $(-5/12,-T/2+1/12)$ |

Place the three anchors in their intrinsic plane and choose positive spatial height at vertex 3 by reflection. The same rational sign tests used above prove nonzero anchor area, positive squared root heights, and positivity of the smaller root-pair deficit $H-|h_3h_4|$ for each link. Thus both choices of height at vertex 4 give positive five-cycles. The two continuous completions at each of the three leaves give all $2\cdot 2^3=16$ normalized possibilities. The independence of the five null vectors keeps every leaf face nondegenerate. Direct sign checks give positive orientations for all sixteen branches, so all of these intrinsic triangulations develop to the prescribed torus.

For the intersection check, use the five-point alternating cofactors introduced above. If, after reversing the face signs, all five cofactors have the same strict sign, the unique affine dependence has strictly positive coefficients on the edge and strictly negative coefficients on the face, up to reversal. Normalizing the coefficients on each side gives an intersection in the relative interiors.

Six intervals $(l,r]$ cover $0<U=1/T\le1$, with successive endpoints $0,1/2,3/4,7/8,15/16,31/32,1$. On each interval the verifier retains the four-core and one-leaf brackets whose zeros it can exclude throughout that interval. For a four-core bracket it tests its quadratic-field norm. For a one-leaf bracket it tests the norm of (1); nonvanishing excludes coplanarity for either leaf choice. Both norms cover the two choices of sign at vertex 4 by conjugation. Exact Bernstein coefficients after the substitution $U=l+(r-l)s$ supply these tests. At the interval midpoint, each of the sixteen completions has a crossing witnessed by five retained brackets. Continuity carries that particular crossing throughout the interval. The witnessing pair can differ between branches and intervals. At each fixed sharp modulus the positive deficits and strict crossing signs persist under small perturbations of the core coordinates. Taking the intersection of the sixteen branch neighborhoods therefore excludes an open neighborhood of this core at that modulus. [Sharp-ray core and crossing certificate](../../scripts/type5_rectangles/sharp.py)

At each fixed sharp modulus, every possible embedding can be perturbed at that same modulus to one with a rational intrinsic core and no four coplanar spatial vertices. The resulting strict feasibility test includes embeddings that initially have an unfolded hinge. [Fixed-period regularity and the sharp-ray test](Type5Regularity.md)

## Replay

From the repository root, with a built Lean checkout, CaDiCaL from the Lean toolchain, and Python with `python-flint` and SymPy, run

```sh
python3 -m scripts.type5_rectangles separation
```

The `opening` and `height-cones` arguments verify the embedded sharp-ray family with one prescribed edge-length error and the exclusion of exact embeddings near its planar limit. [One-edge construction](Type5Opening.md)

The `core-bounds` argument verifies the 39-vertex polytope and the uniform area bounds for its three leaf stars. The `generic` argument checks the 70 coprimality tests used in the fixed-modulus perturbation. The `sharp` argument verifies the sixteen nonplanar sharp-ray folds and their crossings. The `reduced` argument independently checks the edge equations, intrinsic orientations and embedded base point. The `rhombic` argument checks the separate equal-length construction. [Rhombic arc and punctured hexagonal sector](Type5Rhombic.md)
