# Type 5 with one prescribed edge-length error

Fix a sharp torus with periods $(1,0),(1/2,y)$, where $y\ge\sqrt3/2$. There is a number $\eta(y)>0$ such that **every** $0<e<\eta(y)$ occurs as follows. The intrinsic triangles triangulate this particular torus, the spatial triangles form an embedded Type 5 torus, and their squared edge lengths satisfy
\[
 |r_j-r_i|^2=|p_j-p_i+K_{ij}|^2-e\,\mathbf 1_{\{i,j\}=\{0,1\}}.
\]
In particular the fourteen faces outside 012 and 031 are exactly isometric. Together with the exact embeddings for reduced $x<1/2$, this gives embeddings matching at least 23 edge lengths on every flat torus, at any scale. The construction below approaches a planar configuration with coincident vertices 3 and 4. A different construction matches all 24 lengths at every sharp modulus above the hexagon. [Sharp-ray embedding proof](Type5SharpEmbeddings.md) [Off-ray embedding theorem](Type5FoldedModuli.md) · [Exact certificate](../../scripts/type5_rectangles/sharp_opening.py)

## Planar positions and the length equations

Write $L=4y^2\ge3$ and use coordinates $(x,h)$ for the physical point $(x,h/\sqrt L)$. The inner product multiplied by $L$ is $B(u,v)=Lu_xv_x+u_hv_h$. A marked period $(m,n)$ becomes $(m+n/2,nL/2)$ in these coordinates. Use the square marking. Set
\[
 b=9/20,\quad s=1/10,\quad a=-(L+2)/8,\quad T=(L+1)/4,\quad
 w=\frac{25L^2-44L+16}{4(25L-18)}.
\]

| Vertex | Intrinsic position $p_i$ | Spatial horizontal position $r_i$ at the planar configuration |
|---|---|---|
| 0 | $(s,(1-4b)s)$ | $(-s,(1-4b)s)$ |
| 1 | $(0,0)$ | $p_1$ |
| 2 | $(0,a)$ | $p_2$ |
| 3 | $(b,T-b)$ | $(b-1/2,T-b-L/2)$ |
| 4 | $(-b,T-b)$ | $r_3$ |
| 5 | $(-1/2,1/2-2b)$ | $p_5$ |
| 6 | $(0,T)$ | $( -1/2,T-L/2)$ |
| 7 | $(-1/2,w)$ | $2B(p_7,p_5)p_5/B(p_5,p_5)-p_7$ |

Lean verifies all 24 planar squared edge lengths and all sixteen strictly positive intrinsic orientations. [Planar lengths and orientations](../../OrigamiTorus/EightVertex/Type5/SharpOpening.lean)

Keep vertex 1 at the origin and the two other spatial anchors 2 and 5 equal to their intrinsic positions, with height zero. This leaves 24 horizontal coordinates, fourteen intrinsic and ten spatial. Fix the intrinsic coordinates $p_{0x},p_{2h},p_{3x}$ at their tabulated values. For the 21 remaining coordinates use the 21 edge equations outside the anchor triangle. The verifier computes the determinant of their Jacobian at the planar configuration,
\[
 \frac{81 L^{18}(5L-13)(5L-4)(25L+16)(75L+14)}
 {3125000000(25L-18)} > 0.
\]

For $t>0$, prescribe physical heights $\sqrt t(H_i+t k_i)$. Set $H_3=H_4=1$, $H_7=3$, $H_6=\det(r_5,r_6)/\det(r_5,r_3)$, and the four other $H_i=0$. Only $k_0,k_4,k_6$ vary. Prescribe a spatial-minus-intrinsic squared length $tD$ on edge 01 and zero on every other edge. After multiplying by $L$, the equations are polynomial in $t$ and in the horizontal coordinates, also for negative $t$ in the implicit-function argument. For fixed $L,D,k$, the invertible Jacobian gives horizontal coordinates depending smoothly on $t$ throughout an interval about zero.

If $u_i,v_i$ are the intrinsic and spatial horizontal velocities, their equations are
\[
 2B(r_j-r_i,v_j-v_i)-2B(p_j-p_i+K_{ij},u_j-u_i)
 =L\big(D\,\mathbf 1_{\{i,j\}=\{0,1\}}-(H_j-H_i)^2\big).
\]
The verifier solves this linear system for the constant and linear coefficients in $D$. Positive intrinsic orientations persist. With the same cocycle the development still has degree one, hence identifies the intrinsic triangulation with the prescribed lattice quotient. [Degree and quotient argument](Type5Rectangles.md#from-signs-to-a-torus)

## Separating the triangles

For $t>0$ multiply the spatial second coordinate by $\sqrt L$ and divide the height by $\sqrt t$. This invertible transformation preserves all intersections. The resulting spatial points extend smoothly to $(r_i,H_i)$ at zero. Of the 70 increasing-label tetrahedron determinants, 44 have a nonzero value there. Seventeen more have the following signed derivatives, where the displayed sign times the derivative must be positive.

| Positive | Negative |
|---|---|
| 0125, 0134, 0136, 0157, 0347, 1347, 1356, 2345, 2346, 3457 | 0146, 0156, 0345, 1346, 1456, 2347, 3456 |

Each signed derivative is affine in $(D,k_0,k_4,k_6)$. On $3\le L\le6$, set those for 0146, 0156, 2345, 2347 and 1356 equal to a common unknown. On $L\ge6$, use 1347 in place of 1356. The two rational solutions specialize everywhere on their respective intervals. In both, $D<0$ and all seventeen signed derivatives are positive. These assertions, the 44 constant signs, the intrinsic orientations and all divisor checks use exact univariate polynomial root counts.

For sufficiently small positive $t$, the 61 known signs give both required signs in the alternating-cofactor separation test for each of the 138 disjoint edge–face pairs. The nine unassigned brackets have no effect on this check. Cancellation of common barycentric coefficients then gives an injective spatial map. The 23 matching lengths make each of the fourteen unaffected triangles isometric by polarization. Since $D$ is fixed and negative at each modulus, setting $t=e/(-D)$ realizes every sufficiently small prescribed error. A similarity scales the squared error by its squared scale factor. [Separation criterion](Type5FoldedModuli.md#spatial-separation-over-the-full-rectangle)

## Why setting the error to zero fails here

The scaled signed double area $A=\det(r_5,r_0)$ of triangle 015 vanishes at the planar configuration. When the leading heights at 0, 1, 2 and 5 are zero, nine first-order edge equations give
\[
 5(75L+14) A'+9(75L+14)D+100(L+2)H_4^2=0 .
\]
This computation permits arbitrary horizontal velocities at the three coordinates frozen above. It uses the actual marked edges 01, 02, 03, 04, 05, 13, 24, 35 and 45. [Lean area identity](../../OrigamiTorus/EightVertex/Type5/SharpOpening.lean)

Consider the six strict signs 1245+, 0245+, 0124−, 1257−, 0257−, 0127− that hold in the rescaled limit. For a generic embedding the separation tests for 04 against 152 and 15 against 024 force 0125+: assuming its opposite would require both signs for 0145. The test for 02 against 175 then forces 0157+. A small generic spatial perturbation preserves embeddedness and the six strict signs, so both conclusions also hold weakly for a possibly nongeneric embedding.

For any nearby spatial configuration with the anchors horizontal, write $R_i$ for its scaled horizontal positions and $Z_i$ for its normalized heights. Expansion in the height coordinate gives the exact identity
\[
 c[0125]+[0157]=Z_7\det(R_5,R_0),\qquad
 c=-\frac{\det(R_5,R_7)}{\det(R_2,R_5)}.
\]
Here $R_1=0$. The coefficient at the base is $2(5L-4)(25L+16)/(5(L+2)(25L-18))>0$, and $Z_7$ is near 3. Embeddedness therefore requires $\det(R_5,R_0)\ge0$.

Along the displayed differentiable opening, the derivative at zero of the left side of the volume identity is
\[
 -\frac{60(L+2)}{75L+14}-\frac{27}{5}D.
\]
The derivative of $c$ makes no contribution because $[0125]=0$ at the base. The two strictly positive bracket derivatives used by the construction therefore require $D<-100(L+2)/(9(75L+14))$. The three separation tests alone give the weak version of this bound for a differentiable opening with the same leading heights. In particular $D=0$ is impossible.

## Excluding a neighborhood of the planar configuration

**At every sharp modulus the tabulated 24-length vector has positive distance from the set of length vectors of all exact flat embedded Type 5 tori, even when their periods can vary.** This is a statement about labeled lengths at the scale in the table. The 23-edge construction converges to this vector through embedded polyhedra.

Suppose exact embeddings have length vectors converging to the tabulated one. Normalize intrinsic rigid motions using the nondegenerate triangle 152. In the universal cover, a developed oriented triangle depends continuously on its three lengths and the developed positions of two adjacent vertices. One can reach the eight chosen lifts and two period translates by a finite chain of adjacent triangles. All the limiting triangles are nondegenerate. The intrinsic positions and periods therefore converge to the tabulated ones, up to the initial rigid motion. Identify the spatial anchors with their intrinsic horizontal positions by a spatial rigid motion. Each of the other five vertices is joined to all three anchors. Subtracting the squared-distance equations to the anchors determines its two horizontal coordinates continuously. The remaining height squared tends to zero because the tabulated spatial position is planar.

Every vertex of an exact flat embedding has a strict supporting plane among its neighbors. Both embeddedness and these support conditions persist under sufficiently small spatial perturbations. Consequently each embedding is in the closure of a general-position sign pattern satisfying the spatial clauses below. Quartet 0125 is a clique, so its volume at the original embedding is already nonzero. Reflect the spatial heights to make $[0125]>0$, choose such an adjacent pattern, and pass to a subsequence with a single pattern $\sigma$. At each original embedding, its brackets have the indicated signs weakly, including any bracket that was zero. Write $z_i$ for the physical heights and divide them by their largest absolute value. A subsequence converges to a vector $h$ with maximum absolute coordinate one. For each quartet $q$ let $W_q(h)$ be its determinant at the limiting horizontal positions and these heights. Expansion along the height column makes $W_q$ linear, and $\sigma_q W_q(h)\ge0$. Normalize the vertices other than 7 by their own largest absolute height to obtain a second nonzero limit $u$. The same inequalities hold for $u$ on quartets omitting 7. Both normalizations have nonzero denominators because tetrahedron 1235 is nondegenerate. [Strict support and affine independence of cliques](../../OrigamiTorus/EightVertex/Type5/StrictSupport.lean)

The following finite implication holds for the entire ray. Use coordinates for heights in vertex order $0,3,4,6,7$, and number the increasing quartets $1,\ldots,70$ in lexicographic order. A signed index specifies the sign of its determinant. All the signs in both rows of the table, together with the positive sign of 0157, are forced in the general-position pattern.

| Signed indices | Consequence for normalized heights |
|---|---|
| $-66,-43,-15,-9,+40$ | $h_7>0$ |
| $-11,+3,+49,+57$ | $u_0=0$ and $u_4\ne0$ |

To verify the implication, start with the spatial Grassmann–Plücker relations, the affine cofactor sign tests, the disjoint edge–face tests and strict support of every vertex among its neighbors. Each list in the certificate is a further impossible combination of signs. Its signed rows $W_q$ have rank five, and the cone where all rows are weakly nonnegative contains only zero. Indeed a nonzero pointed polyhedral cone has an extreme ray. In dimension five this ray annihilates four independent active rows. The checker considers every choice of four. If they are independent, two of the signed rows lie on opposite sides of their span, which excludes both normal directions. All tests use polynomial determinants in $L-3$ of degree at most ten. The verifier reconstructs them by exact interpolation and certifies strict signs by coefficient bounds. CaDiCaL refutes the spatial clauses and conflict exclusions together with the denial of the indicated signs. The verifier replays each inference. [Conflict lists](../../scripts/type5_rectangles/height_conflicts.json) · [Determinant and refutation checks](../../scripts/type5_rectangles/height_cones.py)

For the first row of the table the five signed forms are independent. The coordinate $h_7$ is a strictly positive linear combination of those forms. For the second row the four signed forms, restricted to vertices 0 through 6, have rank three and a strictly positive linear dependence. Each must vanish at $u$. The verifier computes their one-dimensional kernel and checks that every nonzero vector in it satisfies the displayed conditions. Thus $z_7>0$ eventually. In the original embeddings $[0125]>0$ and $[0157]\ge0$, so the exact volume identity gives $A>0$ along the sequence.

Now discard vertex 7 and its five incident edge equations. After the anchor normalization there are twenty horizontal coordinates. The sixteen remaining nontrivial edge equations have independent horizontal Jacobian rows at the planar base. They are a subset of the original 21 independent rows, and their entries in the four discarded columns were all zero. Solve for sixteen horizontal coordinates, keeping the other four and both intrinsic period vectors as parameters. Write $t$ for the square of the seven vertices' largest absolute height and use their normalized heights as additional parameters. At $t=0$ the spatial orientations of triangles 012, 024 and 045 are negative, and those of 053 and 031 are positive throughout the nearby planar graph. Develop the star of vertex 0 in the intrinsic plane. Consecutive face isometries with the same orientation agree on their common edge, so they agree on the plane. Each of the two runs therefore uses one planar isometry. Those isometries have opposite orientation and agree at the three developed vertices 0, 1 and 5. Their images are collinear, so $A=0$ throughout the planar graph. At the base with limiting heights $u$, the area derivative is strictly negative by the Lean identity, since $D=u_0=0$ and $u_4\ne0$. The identity uses only edges of this seven-vertex subcomplex. By continuity the derivative stays negative near the base, so every sufficiently late term of the sequence has $A<0$. This contradicts $A>0$ and proves the neighborhood exclusion.

The arithmetic can be replayed from the repository root with SymPy, python-flint and a built Lean checkout.

```sh
python3 -m scripts.type5_rectangles opening
python3 -m scripts.type5_rectangles height-cones
```
