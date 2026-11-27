# Type 4 near-universality

Write the normalized modulus as \(x+i\sqrt w\), with \(0\le x<1/2\) and \(w\ge 1-x^2\). The two families in the [PR certificate](../research/torus_near_universal_certificate/torus_near_universal_certificate/README.md) use \((H,c)=(33/(20+26x),1/3)\) up to \(x=9/20\) and \((1+3(1-2x)^2/2,2/3)\) from \(9/20\) onward. Here \(c\) is the positive ratio \(-r/(H-1+Hx)\). Both have \(H>1\), and the second has \(H\le6/5\).

Use \(a=Hx\), \(D=H-1+a\), and \(Q=D^2+H^2w\). Set

\[
T=a^2-a+H^2w-D,\qquad
(1-c)S=a^2-a-(1-c)H^2w-D(2a-cD-1).
\]

Multiplying every planar point by \(Q>0\), the four points of the flip become

\[
P_2=(Q/2,0),\quad P_6=(aQ,HQ),\quad P_3=P_6+S(D,H),\quad P_5=(Q,0)+T(D,H).
\]

The modulus bound gives \(a^2+H^2w\ge H^2\), so

\[
T\ge (H-1)^2+H(1-2x)>0.
\]

Expanding \(D\) and using \(a^2+H^2w\ge H^2\) again gives

\[
(1-c)S\le (H-1)+c(H-1)^2-(1-c)H^2-2(1-c)(H-1)a<0.
\]

The strict inequality follows for \(c=1/3\) from \(H^2-H+2>0\), and for \(c=2/3\) from \(H^2-H-1<0\) when \(1<H\le6/5\). Finally, expanding gives

\[
(1-c)\bigl(Q+(2H-1)T+S\bigr)=(1-c)(2H-1)T+H(H-1)>0.
\]

The oriented double areas of \(356,352,623,625\) in these scaled coordinates are respectively

\[
-SH^2Q,\qquad -\tfrac12HQ\bigl(Q+(2H-1)T+S\bigr),\qquad SHQ(H-\tfrac12),\qquad
\tfrac12HQ\bigl(Q+(2H-1)T\bigr).
\]

Their signs are \(+,-,-,+\), so the two diagonals cross in their relative interiors. The shared quadrilateral is strictly convex on the entire open strip. Flipping the diagonal \(35\) to \(26\) gives the Lutz Type 4 face list using the relabeling \((2,1,4,0,3,7,5,6)\). Lean verifies these formulas and strict inequalities. [Type4Strips.lean](../OrigamiTorus/Type4Strips.lean)

## The two circles and the cone angles

Use the unscaled PR coordinates \(P_i=(X_i,Y_i)\), and let \(Z_i=X_i+i\sqrt wY_i\). Let \(q=H/D\), \(\tau=x+i\sqrt w\), and \(R=1+i\sqrt w q\). Write \(U\sim V\) when \(U,V\ne0\) and \(U/V\) is real, so the two complex numbers have the same unoriented line direction. Write \(s=DT/Q\), \(t=DS/Q\), and \(r=-cD\). In these coordinates \(P_3=P_6+t(1,q)\) and \(P_5=P_4+s(1,q)\).

The auxiliary point \(Z_{1'}=1-\overline{Z_1}\) has scaled coordinates \((a+r,H+qr)\). The identity \((1-c)(Q+S)=H(H-1)\) gives \(t<r\) when \((1-c)^2Q>H(H-1)\). In the first chart \(H\le33/20\), and in the second \(H\le203/200\). The lower bound \(Q\ge H^2+(H-1)^2+2a(H-1)\) proves the inequality in both charts. For \(c=1/3\), the difference \(9H(H-1)-4Q\) is bounded above by \(H(H-1)-4-8a(H-1)<0\). For \(c=2/3\), \(9H(H-1)-Q\le7H(H-1)-1-2a(H-1)<0\). Also \(a<1/2\) follows from the first formula for \(H\) and, in the second chart, from \(2a=(1-\delta)(1+3\delta^2/2)<1\) for \(\delta=1-2x\in(0,1/10]\). Thus \(X_3<X_{1'}<1/2<X_1\), \(0<Y_3<Y_1<H\), and \(X_5>1\). The relation \(Z_5-Z_6\sim\tau R\) follows from the crease formulas in the next section and gives \(0<Y_5<H\). These inequalities keep the points in each circle argument distinct.

Vertices \(0,4,5,6,7\) lie on the circle with scaled equation

\[
X^2+wY^2-X-\frac{a^2-a+H^2w}{H}Y=0.
\]

For vertex 5 the left side factors as \(s[1+(1+wq^2)s-q(a^2-a+H^2w)/H]\), which vanishes by the formula for \(s\). The other four substitutions are immediate from their coordinates. A second circle through \(0,4,1,1',3\) has equation \(X^2+wY^2-X-\lambda Y=0\), where

\[
\lambda=\frac{(a+r)^2-a-r+w(H+qr)^2}{H+qr}.
\]

Substituting \((a+u,H+qu)\) gives a quadratic in \(u\) with leading coefficient \(1+wq^2\). One root is \(r\). Substituting \(\lambda\) in the sum of the roots and subtracting \(r\) gives \(t\). The points 1 and \(1'\) have the same \(Y\) and their first coordinates sum to one, so 1 lies on this circle as well.

The face orientation signs of the trapezoidal base in the shared Type 7 labeling are

```text
356 325 364 302 341 310 506 524 547 570 674 601 617 214 207 271
 +   +   −   +   +   −   −   +   −   +   −   +   +   −   −   −
```

To check the cone angle at a vertex, take its oriented cyclic link and form the product of successive ratios of the vectors from that vertex, using the negative faces only. Consecutive terms cancel in blocks. Put \(Z_{ij}=Z_i-Z_j\).

| Vertex | Product over the negative blocks |
|---|---|
| 0 | \(Z_1Z_5Z_2/(Z_3Z_6Z_7)\) |
| 1 | \(Z_{31}Z_{71}/(Z_{01}Z_{41})\) |
| 2 | \(Z_{42}/Z_{02}\) |
| 3 | \(Z_{43}Z_{03}/(Z_{63}Z_{13})\) |
| 4 | \(Z_{14}Z_{54}/(Z_{34}Z_{24})\) |
| 5 | \(Z_{75}Z_{65}/(Z_{45}Z_{05})\) |
| 6 | \(Z_{06}Z_{36}/(Z_{56}Z_{76})\) |
| 7 | \(Z_{67}Z_{07}/(Z_{57}Z_{17})\) |

For points on a circle, ratios of two chords seen from two other points give the same unoriented complex direction. Read the ratio \(Z_{34}/Z_{14}\) from \(1'\) on the second circle. The first chord there is parallel to \(R\) and the second horizontal, giving \(Z_{34}/Z_{14}\sim R\). Reading other angles on that circle gives \(Z_1/Z_3\sim1/R\), \(Z_{31}/Z_{01}\sim Z_{34}\), and \(Z_{03}/Z_{13}\sim1/Z_{14}\). The first circle gives \(Z_{75}/Z_{05}\sim1/\tau\), \(Z_{07}/Z_{57}\sim1/R\), and \(Z_5/Z_7\sim\tau R\). Combine these with \(Z_{17}\sim\overline R\), \(Z_{36},Z_{54}\sim R\), \(Z_{56}\sim\tau R\), \(Z_6\sim\tau\), and the horizontal edges. The products in the table all have real direction.

The unit phases of the successive ratios over the full link multiply to one by telescoping. Each ratio for a negative face must be conjugated when computing the positive interior angle of that face. The product of the corrected phases is therefore the inverse square of the negative-block product's phase, hence one. Each cone angle is a positive multiple of \(2\pi\), and the sixteen Euclidean triangles contribute \(16\pi\) altogether. All eight cone angles are exactly \(2\pi\). The same holds after the convex flip, which preserves the total angles of its quadrilateral.

Every four projected vertices contain a noncollinear triple. The only points at height zero are \(0,2,4\). For four vertices that omit 2, a line would have to contain exactly two points of each circle, with none in their shared pair \(0,4\). It would therefore contain 1 and 3 and at least one of 6 and 7. The line through 1 and 3 increases with \(X\), while 6 and 7 are both left of 1 and higher than it. For four vertices that include 2, the other three must lie off the horizontal axis. Three points from \(5,6,7\) cannot be collinear because they lie on the first circle. The line through 1 and 3 has positive height at the first coordinate of 2. The same holds for the line through 5 and 6, since 2 lies horizontally between them. The line through 6 and 7 is horizontal at positive height, and the line through 5 and 7 increases in height to the left of 7, including at the first coordinate of 2. This proves the noncollinearity condition for an arbitrarily small perturbation of a strict lift direction.

## The marked periods

Start the development at face 325. Faces 524, 302, and 356 have the same orientation sign and can share its planar coordinate map. Face 364 is read by reflecting across edge 36, and face 506 by reflecting across edge 56. These continuations form a subtree of the dual graph, so the developed vectors along the marking loops \(4\to2\to3\to4\) and \(5\to2\to0\to5\) can be read from these six faces. The loops meet only at vertex 2, with alternating branches in its link. They give a lattice basis, and the flip preserves both loops. [Lander, §3.1](https://arxiv.org/abs/2609.10703v1)

Retain the common scale \(Q\). Put \(\rho=(D,H)\), \(\nu=(-wH,D)\). The crease axes of 36 and 56 are parallel to \(\rho\) and \(x\rho+\nu\), respectively. This follows from \(P_3-P_6=S\rho\) and \(P_5-P_6=-H^2(x\rho+\nu)\) for the points in the common scale. For the physical metric in these scaled coordinates use \(\langle U,V\rangle_w=U_XV_X+wU_YV_Y\). Reflecting a direction \(u\) across an axis \(e\) gives \(2\langle e,u\rangle_w e/\langle e,e\rangle_w-u\). Summing the three developed directions in each loop yields

\[
U=2H^2\nu,\qquad V=2H^2(x\nu-w\rho).
\]

Since \(\rho\) and \(\nu\) are orthogonal in this metric and \(\langle\nu,\nu\rangle_w=wQ\), the ratio \(\langle U,V\rangle_w/\langle U,U\rangle_w\) is \(x\). The scaled cross product ratio is one, so the physical cross product ratio is \(\sqrt w\). This is the marked modulus \(x+i\sqrt w\). Lean checks the periods and the cone angles on the trapezoidal charts and on the rectangular specialization. [Type4Periods.lean](../OrigamiTorus/Type4Periods.lean) · [Type4Angles.lean](../OrigamiTorus/Type4Angles.lean) · [Type7Angles.lean](../OrigamiTorus/Type7Angles.lean)

## Horizontal rank on the strip

The inverse-chord balance equations from the [rectangular rank proof](Type7.md) also give a hand proof of rank seven on both Type 4 charts. In the unscaled coordinates put \(b=1-2a>0\), \(h=\sqrt wH\), \(k=\sqrt wq=h/D\), \(d=1+k^2\), and \(e=Hq/d>0\). Use \(r,t,s\) for the cut, the displacement of vertex 3, and the displacement of vertex 5, respectively, as above. Then

\[
Z_6=H\tau,\quad Z_7=1-a+ih,\quad Z_1=H-(D+r)\overline R,\quad
Z_3=Z_6+tR,\quad Z_5=1+sR,\quad Z_5-Z_6=-e\tau R.
\]

Normalize \(\lambda_0=0\) and set \(u=\lambda_6\), \(A=\lambda_4\), \(X=\lambda_3-u\), and \(Y=\lambda_1-\lambda_7\). The circle projections of \(B_5=0\) and \(B_3=0\) give \(u+\lambda_7=A\) and \(Y=-(r/t)X\), respectively. For vertex 3, the only neighbor off the second circle is 6, whose power divided by \(|Z_6-Z_3|^2\) is \(r/t\), as in the rectangular proof. The imaginary part of \(R\tau B_6=0\), divided by \(\sqrt w\), gives

\[
A=2u+\frac{b}{1+xq}\left(\frac{u}{D}+\frac Xt\right).
\]

Normalize the inverse chords in \(B_1\) as in the rectangular proof. The identity \(Z_3=(H-1)Z_1/(H-Z_1)\) follows from \(t=-D+H(H-1)/[(D+r)d]\) and gives \(m_3=-(H-1)\). Since \(Z_7-Z_1=r\overline R\), we have \(\operatorname{Re}m_7=1-a+M/r\), where \(M=[a(1-a)+h^2+hkb]/d>0\). The real part of the normalized equation, with the above substitutions, is \(Lu+KX=0\), where

\[
L=\frac{2aH}{D+a}\ge0,\qquad K=D+r+\frac{Dr-M-(H-1)b D/(D+a)}{t}>0.
\]

The real part of \(R\tau B_6=0\) gives

\[
\lambda_5=-\frac b{D+a}u-P\frac Xt,\qquad P=\frac{e q(x^2+w)}{1+xq}>0.
\]

At vertex 5 the same inverse-chord normalization gives \(m_6=-Hs/e\) and \(m_7=-ds/(1+xq)\). For the second identity use \(Z_7-Z_5=(1+xq)Z_7R/d\), which follows from the formula for \(s\). Hence, with \(C=Hs/e>0\) and \(B=ds/(1+xq)>0\), the normalized equation is \((1+B+C)\lambda_5=A+B\lambda_7+Cu\).

If \(u>0\), then \(X\le0\), so \(X/t\ge0\) and \(\lambda_5<0\). The right side is positive since \(A>2u\) and \(\lambda_7=A-u>0\). Reversing all signs excludes \(u<0\). Thus \(u=X=0\), giving \(A=\lambda_1=\lambda_3=\lambda_5=\lambda_7=0\). The horizontal chords at vertex 2 give \(2\lambda_2=A=0\). The only original dependence was constant, so the horizontal rank is seven. Convex diagonal exchange preserves the angle sums on an open planar neighborhood, and thus preserves this rank. Using \(x\) and \(w+x^2-1\) as parameters gives a product domain with a unique derivative even at its included endpoints. The two chart directions give independent modulus derivatives in the kernel, proving joint rank nine. [Type4Rank.lean](../OrigamiTorus/Type4Rank.lean) · [Type4StripRank.lean](../OrigamiTorus/Type4StripRank.lean)

## Marking after the flip

The shape map uses the new diagonal \(26\) as its unit edge, with \(2=0\) and \(6=1\). It develops \(632\) and \(625\) on opposite sides of that edge. The branches through \(524\) and \(302\) continue alongside the original positive planar faces. The branches through \(364\) and \(506\) reflect across \(36\) and \(56\). The developed copies of vertices \(4\) and \(0\) give the same displacement formulas as before the flip, divided by the new complex unit edge \(Z_6-Z_2\). The quotient of those displacements stays equal to \(x+i\sqrt w\) throughout both trapezoidal charts.

The strict signs hold on a planar neighborhood of every base. Lean uses the equality of the two angle and shape maps on that neighborhood to transfer rank nine at each base of the two charts. The implicit function theorem gives a closed spatial embedding with the new diagonal, preserving the local displacement ratio and all cone angles. Developing its triangles gives two marked translations and a degree-one map to their lattice quotient. Lean verifies that the metric on every developed face agrees with the spatial triangle and rescales to the requested lattice. The theorem uses the flipped chart labels, with the relabeling to the standard Type 4 face list checked separately. [Type4MarkedShape.lean](../OrigamiTorus/Type4MarkedShape.lean) · [Type4Periodic.lean](../OrigamiTorus/Type4Periodic.lean) · [Type7Tiling.lean](../OrigamiTorus/Type7Tiling.lean)

The spatial lift uses five closed height cells through \(x=9/20\) and one cell with \(9/20\le x<1/2\). In each cell let \(t\) parametrize the interval for \(x\) and write \(w=1-x^2+h\), \(h\ge0\). After clearing positive denominators, the determinants are rational polynomials in \(t,h\). For \(t<1\), substitute \(t=u/(1+u)\) and multiply by a power of \(1+u\) to clear the denominator. Nonnegative coefficients with a strictly positive constant term prove the desired strict sign for all \(u,h\ge0\). Each closed cell also checks the polynomial at \(t=1\). Lean checks the rational coefficients, the noncollinearity of a projected triple in each quadruple, and a strict separating minor-product witness for each disjoint edge and face. Generic perturbation of the heights preserves these strict inequalities. The proof replays within Lean. [StripPolynomial.lean](../OrigamiTorus/StripPolynomial.lean) · [Type4StripLift.lean](../OrigamiTorus/Type4StripLift.lean) · [PR lift certificates](../research/torus_near_universal_certificate/torus_near_universal_certificate/README.md)

Applying fixed-modulus inflation to those lifts gives the Type 4 embedding for every reduced modulus in the open strip. The quotient proof identifies the developed faces with the marked flat torus and verifies their distances. [Type4StripInflation.lean](../OrigamiTorus/Type4StripInflation.lean) · [Type4WideLift.lean](../OrigamiTorus/Type4WideLift.lean)

The full spatial differential is surjective at the planar base because its restriction to the horizontal directions is surjective. A right inverse and openness of invertibility show that surjectivity persists near the base. The implicit-function solutions approach the base as the height scale tends to zero, so a sufficiently small positive lift has rank nine. The same solution satisfies flatness, the prescribed modulus, and embeddedness. A common rescaling preserves the cone angles and marked ratio, so the chain rule preserves rank at the actual spatial coordinates of the piecewise-isometric realization. [Inflation.lean](../OrigamiTorus/Inflation.lean) · [Type4StripInflation.lean](../OrigamiTorus/Type4StripInflation.lean) · [Open-strip regularity theorem](../OrigamiTorus/Type4WideLift.lean)

## Fixed-marking reconstruction for Types 4 and 7

Translate the intrinsic representative of vertex 0 to the origin. The other
seven planar representatives give fourteen real parameters. For each marked
edge its exact squared length is the norm squared of the difference of its
two endpoint representatives with the specified period shift.

The five four-vertex anchor sets for Type 4 are (0245,0345,1245,1246,2457).
For Type 7 they are (0123,0136,0127,0235,1234). Each anchor is a complete
subgraph, and every outside vertex has three distinct anchor neighbors. The
first two anchors in each list share a filled triangle, (045) for Type 4
and (013) for Type 7. If both anchors were planar, the common
noncollinear triangle would place them in the same plane. Their two
remaining vertices would lie outside the filled triangle by injectivity.
The planar complete-graph obstruction with one edge omitted excludes that
configuration. Thus at least one listed anchor is a nondegenerate
tetrahedron in every embedding. [TetrahedralAnchors.lean](../OrigamiTorus/TetrahedralAnchors.lean)

The six marked anchor lengths give a canonical tetrahedron by radicals.
Place the first anchor at the origin and the second on the positive
horizontal axis at the specified distance. Subtracting the first two
squared-distance equations gives the first coordinate of the third anchor.
Its positive height in the horizontal plane is the square root of the
remaining squared length. The fourth anchor has two signed heights above
or below that plane. Reflecting the spatial realization in the plane
interchanges the two choices and fixes the first three anchors.

For an outside vertex with sphere centers $A,B,C$, write $u=B-A$,
$v=C-A$, and $N=u\times v$. Let $d_A,d_B,d_C$ be the specified
squared distances. Subtract the equation at $A$ from the equations at
$B$ and $C$. The resulting dot products determine a unique planar
displacement $P$, because the Gram determinant is $\lVert N\rVert^2>0$.
The two possible positions are

$$
A+P\pm\sqrt{\frac{d_A-\lVert P\rVert^2}{\lVert N\rVert^2}}\,N.
$$

Lean verifies that these formulas include every solution, including
tangencies when the two candidates coincide. [ThreeSpheres.lean](../OrigamiTorus/ThreeSpheres.lean) ·
[TetrahedronFromDistances.lean](../OrigamiTorus/TetrahedronFromDistances.lean)

There are at most $5\cdot 2^4=80$ branches per choice of the fourteen
parameters and the marked shifts. Lean proves that every embedded spatial
placement with those lengths occurs on the list up to rigid motion. It
also proves the converse after exact validation of every edge length and
every convex-hull intersection between disjoint labeled subfaces. This
intersection test applies to coplanar and other nongeneric configurations.
The reconstruction takes the intrinsic representatives and shifts as input.
[Reconstruction and spatial tests](../OrigamiTorus/TetrahedralReconstruction.lean)
