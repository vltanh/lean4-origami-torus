# The Type 7 rectangular and open-strip families

For a rectangle of aspect ratio \(y\ge1\), set \(w=y^2\), \(H=33/20\), and \(q=33/13\). Scaling and exchanging the two sides put any rectangular torus in this form. At \(x=0\), the trapezoidal formula of [Type 4](Type4.md) with \(c=1/3\) gives the original Type 7 face list. The [Lean rectangular coordinates](../OrigamiTorus/Type7/Rectangular.lean) multiply all these points by the same positive factor \(1+q^2w\). The physical plane has coordinates \((X,yY)\).

Lean verifies all sixteen planar orientation signs. At each vertex, the product of the six complex corner factors is real. It is positive at \(w=1\) and remains positive on \([1,\infty)\), since the factors stay nonzero. Taking arguments gives a positive multiple of \(2\pi\) at each vertex. The sixteen triangle angle sums add to \(16\pi\), so all eight vertex sums are \(2\pi\). The [Lean angle calculation](../OrigamiTorus/Type7/Angles.lean) proves these equalities for Euclidean angles.

Start with face 325. Read the adjacent same-sign faces 524, 302, and 356 in the same planar chart. Reflect across 36 for face 364 and across 56 for face 506. With the same common scale as in Lean, the marking loops \(4\to2\to3\to4\) and \(5\to2\to0\to5\) have vectors

\[
U=2Hq(-wq,1),\qquad V=-2Hqw(1,q).
\]

The periods are orthogonal in the metric \(dX^2+w\,dY^2\), and the oriented cross product in scaled coordinates is \(\langle U,U\rangle_w\). The physical period ratio is therefore \(iy\). The loops give the marking specified in [Lander, §3.1](https://arxiv.org/abs/2609.10703v1). The [Lean period calculation](../OrigamiTorus/Type7/Periods.lean) verifies the reflection and metric identities. The interpretation as periods of the flat lattice quotient uses the usual development of the flat triangulated torus.

The height direction \((3/13,-3/8,-3/7,12/13,1,-1,1,0)\) satisfies the strict determinant tests for every disjoint edge and face throughout \(w\ge1\). Each quadruple has a noncollinear projected triple, so a small perturbation of the heights can achieve general position without losing separation. Lean checks both facts and constructs such generic heights. The same tests hold for the flipped Type 4 face list on rectangles.

The [inflation proof](../OrigamiTorus/Type7/Inflation.lean) keeps the modulus fixed by adjoining two marking equations to the seven independent angle equations. The planar family extends into the Type 4 strip near \(x=0\) with the same Type 7 faces before the flip. The two parameter velocities preserve the angle sums and give independent derivatives in \(x\) and \(y\) of the marking. At the strip boundary one can take these derivatives from within the strip using smoothness of the local maps. The hand calculation below proves the rank by elimination for all rectangular bases.

## A hand proof of horizontal rank seven

The following calculation replaces the designated minor with a proof about the left kernel of the full horizontal angle derivative. Use unscaled physical complex coordinates and put

\[
D=H-1,\quad h=yH,\quad k=h/D,\quad R=1+ik,\quad d=1+k^2,\quad
r=-D/3,\quad s=-D+\frac{HD}{(D+r)d},\quad t=\frac{hk-1}{d},\quad j=\frac{h+k}{d}.
\]

Here \(s<r<0<t\) and \(j>0\) throughout \(y\ge1\). The coordinates are \(Z_0=0\), \(Z_2=1/2\), \(Z_4=1\), \(Z_6=ih\), \(Z_7=1+ih\), \(Z_1=1-r+i(h+kr)\), \(Z_3=ih+sR\), and \(Z_5=1+tR\). In particular \(Z_5-Z_6=-ijR\). These formulas follow from the displayed planar family by undoing its common scale.

Let \(\lambda_v\) be a left dependence among the horizontal cone-angle differentials. Differentiating each block of turning angles gives the imaginary part of the logarithmic derivative of its chord ratio. Since the direction of a vertex motion is arbitrary in the plane, the condition at each vertex is the complex equation

\[
B_v=\sum_b\frac{\epsilon_{vb}(\lambda_v-\lambda_b)}{Z_b-Z_v}=0.
\]

Here \(\epsilon_{vb}\) is \(+1\) at the exit ray of a block of negative faces, \(-1\) at its entrance, and zero elsewhere. The signs at the other endpoint satisfy \(\epsilon_{bv}=-\epsilon_{vb}\). They can be read from the negative-block table in the [Type 4 flatness proof](Type4.md). In the following calculation the positive neighbors are \(7,6\) at vertex 5, \(4,0\) at vertex 3, \(0,3\) at vertex 6, and \(3,7\) at vertex 1. Their respective negative neighbors are \(4,0\), \(6,1\), \(5,7\), and \(0,4\). Subtract a constant so that \(\lambda_0=0\), then set \(A=\lambda_4\), \(u=\lambda_6\), \(X=\lambda_3-u\), and \(Y=\lambda_1-\lambda_7\).

For a vertex \(v\) on a circle with center \(C\), project the equation \(B_v\) by taking \(2\operatorname{Re}((Z_v-C)B_v)\). The chord coefficient equals \(-1\) for another point on the circle. For a point off it the coefficient is \(-1\) plus its power with respect to the circle divided by \(|Z_b-Z_v|^2\). This is the expansion of \(|Z_b-C|^2-|Z_v-C|^2\). At vertex 5 all four crease neighbors lie on the first circle, giving \(u+\lambda_7=A\). At vertex 3 only neighbor 6 lies off the second circle. Its power is \(drs\), from the quadratic \(d(z-r)(z-s)\) along the line \(ih+zR\), and \(|Z_6-Z_3|^2=ds^2\). The projection gives \(Y=-(r/s)X\).

The real part of \(R B_6=0\) gives

\[
A=(2+1/D)u+X/s.
\]

At vertex 1 set \(C_b=(Z_b-Z_1)^{-1}\), and normalize by \(C_4-C_0\). Then \(C_0/(C_4-C_0)=Z_1-1\) and

\[
m_b=\frac{C_b-C_0}{C_4-C_0}=\frac{Z_b(1-Z_1)}{Z_b-Z_1}.
\]

The identity \(Z_3=DZ_1/(H-Z_1)\) gives \(m_3=-D\). Since \(Z_7-Z_1=r\overline R\), \(\operatorname{Re}m_7=1+M/r\), where \(M=h(h+k)/d>0\). The real equation after normalization is

\[
0=rX-D(\lambda_1-\lambda_3)-(r+M)X/s-(\lambda_1-A).
\]

Substitute \(\lambda_1=A-u-(r/s)X\), \(\lambda_3=u+X\), and the equation for \(A\). The \(u\)-terms cancel and the remaining coefficient of \(X\) is

\[
D+r+\frac{D(r-1)-M}{s}>0.
\]

Thus \(X=Y=0\). The imaginary part of \(RB_6=0\) now gives \((u-\lambda_5)/j=du/h\), so \(\lambda_5=-u/D\).

At vertex 5 use the same inverse-chord normalization with center vertex 5 in place of 1. Write \(B=dt>0\) and \(C=ht/j>0\). The two normalized coefficients are \(m_7=-B\) and \(m_6=-C\), using \(Z_7-Z_5=Z_7R/d\) and \(Z_6-Z_5=ijR\). The real equation is

\[
(1+B+C)\lambda_5=A+B\lambda_7+C u.
\]

Because \(\lambda_5=-u/D\), \(A=(2+1/D)u\), and \(\lambda_7=(1+1/D)u\), this forces \(u=0\). The horizontal chords at vertex 2 give \(2\lambda_2=A=0\). All normalized \(\lambda_v\) vanish. Before subtracting the constant, the only dependence was the sum of the eight cone angles, so the horizontal derivative has rank seven.

Lean verifies the inverse-chord elimination and the surjectivity of the seven-angle derivative. The two marking components come from developing six triangles by their squared edge lengths, using the cosine rule for the coordinate along each edge and the positive square root for the height. Lean verifies smoothness near the rectangular chart and the exact ratio \(V/U=x+iy\) on the unflipped trapezoidal family. Taking derivatives within \(x\ge0,\ y\ge\sqrt w\) gives two independent marking velocities with zero angle derivative, including at the square. The resulting rank-nine derivative gives a positive-height embedded realization preserving all eight cone angles and the marked displacement ratio \(i\sqrt w\). The eighth angle follows from the sixteen triangle angle sums. [Type7/Rank.lean](../OrigamiTorus/Type7/Rank.lean) · [Lattice/MarkedShape.lean](../OrigamiTorus/Lattice/MarkedShape.lean) · [Type7/MarkingRank.lean](../OrigamiTorus/Type7/MarkingRank.lean) · [Type7/Inflation.lean](../OrigamiTorus/Type7/Inflation.lean)

## Interpreting the marked displacements

Develop the positively oriented faces, starting with \(356\) normalized so that \(3=0\) and \(5=1\). Across each edge of the following dual tree, put the new triangle on the opposite side of the shared edge. The branches through \(325,364,506,302,524\) use the same development as the six-triangle formula.

| Parent | Children |
| --- | --- |
| \(356\) | \(325,364,506\) |
| \(325\) | \(302,524\) |
| \(364\) | \(674,341\) |
| \(341\) | \(310\) |
| \(524\) | \(214,547\) |
| \(547\) | \(570\) |
| \(674\) | \(617\) |
| \(617\) | \(601,271\) |
| \(271\) | \(207\) |

For an oriented edge \(ij\), let \(g_{ij}\) be the direct isometry taking the shared edge in its left-face coordinates to the edge in its right-face coordinates. It takes both endpoints to their corresponding copies. Then \(g_{ji}=g_{ij}^{-1}\) and all dual-tree transitions are the identity. Write \(a,b,c,d,e,f,g,u,v\) for the remaining transitions in the directions \(01,02,03,05,06,07,14,12,47\), with products acting rightmost first.

Around each vertex use its positive cyclic link \(n_0,\ldots,n_5\), with incident faces ordered as \((i,n_j,n_{j+1})\). The transition \(g_{i n_j}\) takes the \(j\)-th face to the preceding one along their shared edge. Their product fixes a copy of \(i\). Its complex multiplier is the product of the ratios of the outgoing to the incoming ray in each face. The ray lengths telescope across shared edges and the arguments sum to \(2\pi\), so the product is the identity. In order from vertex \(0\) through vertex \(7\) the words are

\[
bcaedf,\quad gua^{-1},\quad b^{-1}u^{-1},\quad c^{-1},\quad
vg^{-1},\quad d^{-1},\quad e^{-1},\quad f^{-1}v^{-1}.
\]

It follows that \(c=d=e=1,\ g=v,\ a=vu,\ b=u^{-1},\ f=v^{-1}\) and \(u,v\) commute. If either generator is a nontrivial rotation, it has a unique center \(C\). Every commuting transition fixes \(C\). The doubled oriented area of each developed face is the sum of \(\det(A-C,B-C)\) over its three boundary edges \(A\to B\). Each edge occurs twice in opposite orientations, with its two copies related by a rotation about \(C\). Their contributions cancel. The doubled areas of the sixteen faces are positive, a contradiction. Thus every transition is a translation.

The difference between the copies of vertex \(4\) in \(364\) and \(524\) is the translation of \(v\), read along \(524\to214\to341\to364\). The difference between the copies of vertex \(0\) in \(302\) and \(506\) is the translation of \(u\) plus that of \(v\), read along \(506\to570\to207\to302\). These are \(U,V\) from the six-triangle formula. They generate the full translation group since the change from \(u,v\) is unimodular. The ratio \(V/U=i\sqrt w\) makes them linearly independent.

Taking the copies in \(302,341,325,356,524,356,356,207\) as representatives of vertices \(0\) through \(7\) gives the integer shifts in the Lean table. Their doubled face areas sum to twice the period-cell area. The compatible positive triangles therefore develop to the quotient with degree one, by the same periodic-area argument used for Type 6. In the unit-root-edge chart all lengths are scaled by the reciprocal of the spatial length of \(35\). After dividing complex coordinates by \(U\), the spatial placement is rescaled by that reciprocal and by \(1/|U|\) to match the torus with first period one. Lean checks the entire argument and the further scaling to an arbitrary rectangular lattice. The theorem gives a closed embedding of the actual lattice quotient, with a lift of each labeled face on which all distances agree. [Type7/Periodic.lean](../OrigamiTorus/Type7/Periodic.lean) · [Type7/IntrinsicLifts.lean](../OrigamiTorus/Type7/IntrinsicLifts.lean) · [Type7/Tiling.lean](../OrigamiTorus/Type7/Tiling.lean)

## Fixed-marking reconstruction

The Type 7 graph supports the same fourteen-parameter reduction as Type 4.
Lean verifies an exact list of at most 80 spatial candidates per marking and
the edge-length and intersection tests for the list.
[Fixed-marking reconstruction for Types 4 and 7](Type4.md#fixed-marking-reconstruction-for-types-4-and-7)

## The full open strip

The same unflipped construction works for every reduced modulus with
\(0\le x<1/2\) and \(y^2\ge1-x^2\). Use the six chart cells from the
Type 4 proof. Put \(h=y^2+x^2-1\). In the second cell
\([1/10,1/5]\), evaluate the first cell's height polynomial at the
corresponding first-cell parameter \(10x=1+t\). In the third cell
\([1/5,3/10]\), add \((1+h)/100\) to the cleared height at vertex 3.
The other cells use their Type 4 heights. Lean checks every Type 7
edge–face separation. In the endpoint cell it reuses the checks for
pairs common to Types 4 and 7 and checks the 24 additional pairs.
The generic perturbation, regular inflation, and intrinsic development
apply on all six cells. The spatial rank is nine on the full included region,
including the lower arc \(y^2=1-x^2\). The theorem also permits any
similarity carrying the normalized lattice to the requested lattice.
[Wide-lift theorem](../OrigamiTorus/Type7/WideLift.lean)
