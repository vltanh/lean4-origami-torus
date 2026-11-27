# Type 6 universality

Every flat two-torus has an eight-vertex origami realization on Lutz Type 6. For each marked modulus the construction gives an embedded configuration of rank nine for the map consisting of seven angle deficits and the two modulus coordinates. This proof uses the two flattened families and the rank-seven calculation in [Doyle, Lander, Schwartz and Trettel, §§3 and 5](https://arxiv.org/abs/2611.21909). Their §6 also reports a second universal candidate of the same degree sequence. The explicit face list and flip below identify the triangulation used here.

## The planar flip

A lattice has a basis which, after scaling and perhaps reflection, is $1,x+iy$ with $0\le x\le 1/2$, $y>0$, and $x^2+y^2\ge1$. Indeed, choose a shortest nonzero lattice vector, which is primitive and extends to a basis. Subtract a multiple of it from the other basis vector to reduce the first coordinate, and use reflection and basis signs to arrange the stated signs. The bound on squared length follows from the choice of the shortest vector.

Use the published labeling. The first chart has $0\le x\le1/6$ and takes $(u,k,\lambda)=(3/128,11/32,13/32)$. The second has $1/6\le x\le1/2$ and takes $(u,k,\lambda)=(x/2-1/2048,1/16,1/2)$. Both have $y^2\ge1-x^2$. Put $b=1-x-2k$. For the sign calculations use the coordinates $(p_i^x,yp_i^y)$, with $w=y^2$, as follows.

| $i$ | First coordinate | Scaled second coordinate |
|---|---|---|
| 0 | $0$ | $0$ |
| 1 | $u$ | $u(b+2k/\lambda)$ |
| 2 | $u-1/2$ | $(1-2u)x/2$ |
| 3 | $-k-b\lambda$ | $(\lambda(w-b^2)-2bk)/2$ |
| 4 | $x+k-1/2$ | $(w+bx)/2$ |
| 5 | $u-1/2$ | $(w+b(b+2u-1))/2$ |
| 6 | $u-k$ | $b(u-k)$ |
| 7 | $u$ | $(w+b^2+2bu)/2-(2u-2x-2k+1)/(2(1-\lambda))$ |

The signed areas of $120,125,051,052$ have signs $+,-,-,+$ in both charts. Thus the diagonals $12$ and $05$ cross in their relative interiors, and the cyclic quadrilateral $0,1,5,2$ is strictly convex. In the intrinsic triangle table in §3.1, the four vertices have the same lifts as their unscaled planar images and the two triangles $012,152$ use the same lifts on the common edge. Replacing those triangles by $015,052$ is a retriangulation of the same intrinsic planar quadrilateral. In particular, all moduli are unchanged by the flip. The Type 3 faces are

```text
012 031 024 043 152 136 145 174
167 264 257 276 347 356 375 465
```

Relabel the flipped faces by $0,\ldots,7\mapsto3,7,0,6,1,5,2,4$ to obtain the Type 6 list. The edge $05$ was absent in Type 3.

## An embedded lift

Use the heights $z$ in the table. The auxiliary heights $z'$ will be used only to avoid coplanar quadruples.

| Chart | $z$ | $z'$ |
|---|---|---|
| 1 | $(0,0,-11,-1,-3,-15,0,977)$ | $(0,0,-11,-1,-3,-15,0,977)$ |
| 2 | $(0,-361,2527,2525,5105,2527,1,19639)$ | $(0,-2017,0,-2,-1,-3,0,1430)$ |

For an ordered edge and disjoint face $a,b,c,d,e$, let $V_i$ be the affine determinant obtained by deleting position $i$, starting from 0. In general position the unique affine dependence has coefficients proportional to $(V_0,-V_1,V_2,-V_3,V_4)$. If the edge and triangle meet, convex weights on the edge and the negatives of convex weights on the triangle supply such a dependence. With all minors nonzero, each coefficient is nonzero. The first two signs must agree, and the last three signs must agree. Any one of the strict tests
$$
V_0V_1>0,\qquad V_2V_3>0,\qquad V_3V_4>0,\qquad V_2V_4<0
$$
therefore excludes intersection. The arithmetic below supplies a test for every disjoint edge–face pair. All 70 sorted determinants for $z'$ are nonzero. At a fixed modulus each determinant at $z+\epsilon z'$ is affine in $\epsilon$ with nonzero slope. Choose a sufficiently small positive $\epsilon$ avoiding the finitely many roots. Strict separation survives this change. The resulting lift is in general position and has no disjoint edge–face intersection.

Two triangles in distinct planes meet along subsets of the intersection line. If they share an edge, the portions of that line in the triangles are exactly the shared edge. If they share at most one vertex, any unwanted intersection has some endpoint on an edge of one of the triangles outside their common vertices. An edge incident to the common vertex cannot meet the other plane again, by general position. Thus there would be a disjoint edge–face intersection. Lean proves the embedding by subtracting common barycentric weights and reducing the size of the two disjoint supports with Carathéodory’s theorem. In Euclidean coordinates the resulting map is a closed embedding of the labeled triangle complex. [Geometry/SpatialRealizations.lean](../../OrigamiTorus/Geometry/SpatialRealizations.lean)

## Inflation and rank

The fixed-period length equations below have an invertible derivative in the
twenty-four chosen horizontal coordinates at the planar base. The implicit
function theorem keeps the equations exact for small positive heights.
Continuity keeps this derivative invertible at the corrected placement.

For a Euclidean triangle, give each of its labeled vertices a weight $u_i$
and vary its squared lengths by
$\dot{l}_{ij}=(u_i+u_j)l_{ij}$. If $A_i$ denotes the corner angle at $i$,
differentiating the cosine rule gives
$$
\dot A_i=\tfrac12\bigl((u_j-u_i)\cot A_k+(u_k-u_i)\cot A_j\bigr).
$$
The quadratic form $-\sum_i u_i\dot A_i$ is nonnegative, with equality
exactly when all three weights agree. In Lean this follows by completing the
square with the positive Gram determinant of the two sides at a corner.
Sum over faces. The edge graph is connected, so the kernel consists of
constant weights. Fixing the weight at vertex 0 gives an invertible
seven-by-seven derivative for the other seven cone angles.
[Geometry/MetricAngleVariation.lean](../../OrigamiTorus/Geometry/MetricAngleVariation.lean) ·
[Geometry/MetricAngleRank.lean](../../OrigamiTorus/Geometry/MetricAngleRank.lean)

To recover the marked modulus from the lengths, develop two fixed strips,
one for each period. Their common starting face is $167$, with vertices 1
and 7 at 0 and 1 in the development. Each new triangle is placed on the
other side of its shared edge. The displacements on an oriented periodic
sheet with periods $U,V$ are $U/(p_7-p_1)$ and $V/(p_7-p_1)$. Their ratio
is $V/U$ and depends smoothly on the lengths near the given oriented sheet.

On every nearby positively oriented intrinsic sheet, the angle sum at each
vertex is a positive integer multiple of $2\pi$. The total over all
sixteen faces is $16\pi$, so every vertex sum is $2\pi$. With first period
1, varying the second period therefore gives the two independent modulus
directions while all cone angles stay constant. Together with the
seven angle directions, the joint angle and modulus map on squared lengths
has rank nine. [Type6/MarkedShape.lean](../../OrigamiTorus/EightVertex/Type6/MarkedShape.lean) ·
[Type6/MetricAngles.lean](../../OrigamiTorus/EightVertex/Type6/MetricAngles.lean) ·
[Type6/LengthChart.lean](../../OrigamiTorus/EightVertex/Type6/LengthChart.lean)

Write $E$ and $I$ for the spatial and intrinsic squared lengths in Euclidean
units, and let $D$ be the derivative of the joint map at their common value.
The fixed-period intrinsic variations satisfy $D\,dI=0$. The derivative
of the length residual is $y^2(dE-dI)$. It is invertible at the positive-height
solution, so its composition with the surjective $D$ is surjective. It
follows that $D\,dE$ is surjective, and hence so is the differential of the
joint map on the full spatial vertex coordinates. Common rescaling
preserves the map and its rank. The universal theorem gives this rank on
the very vertices that realize the metric of the requested lattice.
[Type6/Regularity.lean](../../OrigamiTorus/EightVertex/Type6/Regularity.lean) ·
[Type6/Universal.lean](../../OrigamiTorus/EightVertex/Type6/Universal.lean)

The implicit function theorem then gives local dimensions 17 for the flat
locus and 15 for a fixed-modulus fiber. Quotienting by similarities
subtracts seven from each dimension. A local slice puts vertex 0 at the
origin, vertex 1 at $(1,0,0)$, and vertex 2 in the half-plane $z=0$, $y>0$.
Its two planar coordinates remain free. If reflections are included,
choose the side of the plane that contains vertex 3. General position
ensures that the labeled configuration has trivial stabilizer. The
resulting dimensions are 10 and 8. The Lean theorem certifies rank nine,
which is the input to this dimension argument.

## Arithmetic certificate

For the scaled planar coordinates write
$$
A_{abc}=X_b(Y_c-Y_a)+X_c(Y_a-Y_b)+X_a(Y_b-Y_c).
$$
The sorted determinant is $-z_a A_{bcd}+z_b A_{acd}-z_c A_{abd}+z_d A_{abc}$. To check a sign on $[l,r]$, put $x=l(1-t)+rt$, $h=w-(1-x^2)$. Each $X$ is linear in $t$, and each $Y$ is quadratic in $t$ plus a constant multiple of $h$. Thus $A$ and the determinants are a cubic in $1-t,t$ plus $h$ times a linear polynomial in $1-t,t$. A cubic here may be obtained by degree elevation from a lower degree. Multiply by the proposed sign. Strictly positive coefficients of the cubic and nonnegative coefficients of the linear part prove the sign over the whole strip, since $0\le t\le1$ and $h\ge0$.

Here are the sorted-quadruple signs, in lexicographic order, split by smallest vertex $0,1,2,3,4$. A question mark means that the coefficient test supplies no sign.

```text
1 z and z' +++++--++-+++++++--+----+++-+-+++++ ++--+----+++-+-+++++ +---+-++-- -+-- +
2 z'       +++++++++-++++-----+-----++-+---+-- -+--+----++----+++++ -+-++--+-- -+-- +
2 z        -?-+?+-++-++++--+--+----?++-----+-- -+--+----++----+++++ -+--+--+-- -+-- +
```

For an independent check of the arithmetic, the minima of the signed Bernstein coefficients of the base polynomials are $76311/3407872$ and $1304567/33554432$ for the four planar areas in the two charts. For the displayed volume rows, ignoring question marks, the minima are $347/3407872$, $265/33554432$, and $470677/16777216$, respectively. The minimum coefficients of the corresponding $h$ polynomials are zero in every group. These numbers use the conventional Bernstein basis with the binomial coefficients included.

To check the separation counts, list the edges from the flipped faces and pair each edge with the sorted faces avoiding its endpoints. Convert each needed determinant to sorted order by permutation parity and read its sign from the table. The numbers of pairs resolved by their first successful test, in the displayed test order, are $90,36,14,0$ and $96,33,10,1$. In each chart the total is 140. See [Type6/Signs.lean](../../OrigamiTorus/EightVertex/Type6/Signs.lean) for the coefficient identities, sign checks, and separation tests in Lean.

## Fixed-period edge equations

The inflation step also has a formulation entirely in squared lengths. It is the route used by the Lean development. Keep the two periods and the heights fixed while varying the sixteen horizontal planar coordinates on each of the folded and intrinsic sheets. For a sorted edge $ab$, write $d_{ab}$ for the period translation of the second endpoint relative to the first. The table in [Defs.lean](../../OrigamiTorus/Defs.lean) comes from the intrinsic triangle table of the preprint after the flip. In the scaled coordinates, the intrinsic squared length is
$$
w(Q_b^x+d_{ab}^x-Q_a^x)^2+(Q_b^y+d_{ab}^y-Q_a^y)^2.
$$
The folded expression has $P$ in place of $Q$, no period translation, and the additional term $wt^2(z_b-z_a)^2$ for the vertical scale $t$. These twenty-four differences vanish at $t=0$ and the planar base coordinates.

For the square Jacobian use both coordinates at folded vertices 0 through 5 and the first at folded vertex 6. On the intrinsic sheet use both coordinates at vertices 0 through 3 and 5, and the first at vertex 4. Half a row of the derivative is the difference of the two weighted dot products of the edge vectors with their respective endpoint motions. Set $h=w-1+x^2$. Fraction-free elimination of these rows in both charts is recorded in [Type6/Rank.lean](../../OrigamiTorus/EightVertex/Type6/Rank.lean). Each row update is a polynomial identity and each common factor cancelled in an update is strictly signed by the strip bounds. The remaining equations successively force all twenty-four selected motions to vanish. This gives an invertible derivative and the implicit function theorem yields a small correction of both sheets for positive $t$.

The oriented edge pairings are opposite in the periodic face list, each corrected triangle has positive area, and the sum of twice the scaled triangle areas is $2w$, twice the area of a period cell. The directed shifts on the lifted sides are exactly those in the squared-length equations. The affine maps into the lattice quotient agree along common faces because their planar lifts differ by a single lattice translate there. [Type6/Periods.lean](../../OrigamiTorus/EightVertex/Type6/Periods.lean) · [Type6/IntrinsicMap.lean](../../OrigamiTorus/EightVertex/Type6/IntrinsicMap.lean)

On the interior of a face the affine development is locally open. At an edge the incident triangles fill both sides locally. At a vertex lift all incident faces with the central corner at the same point. The closed sectors between consecutive rays form a closed union. Away from the center this union is also open, since the two sectors at any boundary ray fill both sides of that ray locally. The punctured plane is connected, so the sectors cover every direction. In each sector the two coefficients along its bounding rays are linear in the planar displacement. They can be made uniformly small across the finite fan, so any neighborhood of the center in the abstract triangulation maps onto a neighborhood in the plane. The quotient map is therefore open. Its image is also compact and nonempty, so it is the whole connected quotient. [Geometry/PlanarFan.lean](../../OrigamiTorus/Geometry/PlanarFan.lean)

Use lattice coordinates, so the half-open unit square is a fundamental cell. Clip the translated lifted triangles to that square. There are finitely many pieces, and their measures sum to one because the translates of the square partition the plane and the triangle double areas sum to two. The pieces cover the square by surjectivity. If two distinct points had the same image, disjoint neighborhoods of those points would have images overlapping in an open set. Choose a point in the overlap off all projected edges and off the cell boundary. It has two preimages in triangle interiors, so two distinct translated triangles overlap on an open set inside the cell. This gives a positive-area overlap, contradicting the equality of the sum of the piece areas with the area of their union. Thus the continuous map from the compact triangulation onto the quotient is a homeomorphism. Matching all edge lengths makes the affine map on each corresponding pair of triangles an isometry. The spatial embedding then gives the prescribed origami torus.

Lean carries out the openness and area argument and constructs the intrinsic homeomorphism. For an arbitrary complex period basis $a,b$, it applies the modular fundamental-domain theorem to $b/a$, with a change of generator sign when necessary. The resulting complex similarity carries the reduced period subgroup onto the original subgroup and descends to a homeomorphism of the quotients. Scaling the folded spatial coordinates by the absolute value of the similarity's multiplier preserves the face distance equalities. The statement quantifies over the actual quotient by $\mathbb Z a+\mathbb Z b$ and uses Euclidean distances on the affine face lifts. [Type6/Tiling.lean](../../OrigamiTorus/EightVertex/Type6/Tiling.lean) · [Type6/Universal.lean](../../OrigamiTorus/EightVertex/Type6/Universal.lean)
