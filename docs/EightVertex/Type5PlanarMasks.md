# Type 5 planar folding masks at the hexagon

**Only mask 11149 of the 62 archived classes passes the necessary tests for an embedded lift of the exact projection. Its strict projected signs preclude a fixed-period opening at the hexagon.** The assumption is that the unit hexagonal torus has a planar facewise-isometric Type 5 map with nondegenerate triangles and both face signs at every vertex, and that the **exact projected vertices of this map** admit heights giving a simplicial embedding in three-space. The test concerns this construction route. An arbitrary-height lift of mask 11149 and a general Type 5 embedding at the hexagon both remain open.

The input is the sharp Type 5 marking with basis-cycle periods ((−1, 0), (−1, 1)) at τ = (1 + i√3)/2. Face bits, starting at bit zero, follow the order `012 031 024 053 045 152 136 164 147 175 263 237 274 256 357 465`. Global reversal sets bit 15 to zero. The 62 representatives and their multiplicities are the pinned ledger's `OPEN` list after the six face-list symmetries. Each bit encodes the orientation of its projected face up to common reversal. [Archived ledger and 14 earlier exclusions](https://github.com/vltanh/lean4-origami-torus/blob/fe5a6eee0cf14dc8cfb0614505d63812f1bbfa25/research/type5_completion/saturated_routes.md) · [Exact marking and representatives](https://github.com/vltanh/lean4-origami-torus/blob/fe5a6eee0cf14dc8cfb0614505d63812f1bbfa25/research/type5_completion/verify_saturated_routes.py)

| Result | Symmetry classes | Masks |
| --- | ---: | ---: |
| Archived input | 62 | 343 |
| Excluded by the signed crease count | 22 | 114 |
| Further exclusions by determinant signs | 39 | 223 |
| Remaining | 1 | 6 |

The representative **11149** accounts for all six remaining labeled masks.

## Signed crease turns

A crease is an edge between faces of opposite projected orientation. In the oriented link of a vertex, each projected sector sweeps azimuth through an angle strictly between zero and π, with sign prescribed by its face. The total variation is 2π by intrinsic flatness. The signed sum is a multiple of 2π and is zero because both signs occur. Consequently azimuth has a real-valued lift on the entire link, of range at most π.

Intersect the lifted star with a sufficiently small vertical cylinder centered on its vertex. Its link is an embedded simple closed curve on the cylinder. In unwrapped coordinates, it is a simple closed plane curve with coordinates (azimuth, height). Scaling all heights by ε > 0 preserves the embedding. Each face contributes a graph arc whose tangent tends to horizontal and whose total turning tends to zero as ε tends to zero. At a crease the azimuth reverses and the signed exterior turn tends to +π or −π. The two incident planes have different transverse slopes. They agree along the edge, so equal slopes would make them coincide on the overlap of their projected faces. At all other corners the turn tends to zero. The total turning number of a simple closed plane curve is ±1, so the sum of the signed crease turns in units of π is ±2 at each star.

Orient a crease edge from v to w, with the faces written (v,a,w) and (v,w,b) in the global surface orientation. Rotate horizontal coordinates so w is to the right of v. The other two projected vertices lie on the same side of the line through vw. Subtracting the common height slope along vw, the sign of the spatial determinant [vwab] is the sign of the transverse slope on (v,w,b) minus that on (v,a,w). The incoming and outgoing tangents traverse azimuth in opposite directions, so the signed turn has the opposite sign to that determinant. Reversing the edge exchanges both v,w and a,b and leaves the determinant unchanged. Thus there is a single sign per crease, subject to the ±2 sum at each endpoint, and that sign agrees up to a fixed global reversal with the spatial four-point determinant.

## Angular orders and supporting lines

The azimuth bounds give strict projected determinant signs as well. Along a run of faces of one sign the rays are strictly monotone. The determinant from its first to its last ray has that sign whenever their angle is less than π. The exceptional case is a star with exactly two creases, at the two extreme rays. Here the two crease neighbors a,b have v strictly between them in projection. For any other point w the oriented triangles (a,v,w), (v,b,w), (a,b,w) have equal signs when any of them is nonzero. These strict signs can be propagated before perturbation.

We may require every projected vertex to have a strict supporting line among its neighbors after an arbitrarily small perturbation. At a star with at least four creases the azimuth range is strictly less than π since the closed walk has more than a single monotone ascent and descent. At a star with two creases all other rays lie strictly inside the halfplane bounded by the two opposite rays. Each maximal chain through two-crease vertices lies on a straight line and advances strictly monotonically along it, so it cannot close. All the inward halfplanes of its interior vertices are on the same side because successive stars share an incident projected triangle with a third vertex strictly on that side. Keep the endpoints fixed. For a vertex at distance s along a chain of length L, displace its projection outward by εs(L−s) normal to the line. Strict concavity places each interior vertex strictly outside the chord joining its two neighbors. The tangent to the perturbed arc strictly supports it against those neighbors. The other neighboring rays remain on its interior side for sufficiently small ε, even when other chains are perturbed. Distinct chains share at most their higher-crease endpoints as indexed paths. This construction gives all vertices strict planar support simultaneously. An arbitrarily small further generic perturbation in three-space retains the embedding, the strict cone support (hence also spatial support), the signs propagated above, and every crease determinant sign. It makes all projected triples and spatial quadruples nondegenerate. The perturbed points serve only as a necessary sign test and need no longer be isometric.

## Two forced coincident projections

For masks 3948 and 4012, a connected group of equally oriented faces develops by one plane isometry. If two such groups develop vertices a and b with different relative lattice shifts k and l, their common projected distance gives the affine equation

$$N(p_b-p_a+k)-N(p_b-p_a+l)=0,\qquad N(x,y)=x^2+xy+y^2.$$

Here the intrinsic coordinates use the basis $(1,\tau)$, with $p_0=0$. The verifier develops the equally oriented face groups using the pinned integer marking. Exact rational elimination of their equations gives three identities in each mask. Writing $p_i=(x_i,y_i)$, these are

$$x_7=-1,\qquad x_2+2y_2=y_7,\qquad x_5+2y_5=y_7-1.$$

The shifts on edges 02 and 05 vanish, while those on 27 and 57 are (1,0) and (1,−1). The identity $N((0,t)-p_i)-N(p_i)=t(t-x_i-2y_i)$ therefore proves equality of the projected lengths 20 and 27 and of the projected lengths 50 and 57. The angular-order checks put vertices 0 and 7 strictly on the same side of the projected line 25. Distances to the two distinct points 2 and 5 uniquely determine a point on that side. Thus vertices 0 and 7 have the same projection.

Their heights must differ in an embedding. For any i,j such that the projected triangle 0ij has a certified strict sign, 7ij has the same sign. The spatial determinant on 0,7,i,j equals that oriented projected area times the vertical separation of 0 and 7, up to a fixed orientation convention. These strict signs persist under all sufficiently small perturbations and give the two additional refutations.

## A forced triangle orientation in mask 11124

For mask 11124 the same equal-radius equations determine six intrinsic positions up to three parameters. Use coordinates in the hexagonal lattice basis, subtract the intrinsic position of vertex 1, and multiply coordinates and shift vectors by three. The left column below follows by exact linear elimination. In terms of its entries the parameters are $a=P_{2x}$, $b=(P_{6x}+1)/2$ and $t=(a+1-P_{3x})/6$.

| Vertex | Intrinsic $P_i$ | Projected $R_i$ in an isometric copy of the anchor face |
| --- | --- | --- |
| 1 | $(0,0)$ | $(0,0)$ |
| 2 | $(a,a)$ | $(a,a)$ |
| 3 | $(a+1-6t,a+3t-2)$ | $(a+3t-2,a+1-6t)$ |
| 4 | $(2a+1,1-a)$ | $(2a-2,1-a)$ |
| 5 | $(2,-1)$ | $(-1,2)$ |
| 6 | $(2b-1,-b-1)$ | $(2b-1,2-b)$ |

The negatives of the oriented intrinsic determinants of faces 152, 164, 465 and 136 are $3a$, $3(1-a)$, $3b$ and $3(1-3t-(1-a)b)$. The first two add to 3. Consistent orientation therefore makes all four positive, giving $0<a<1$, $b>0$ and $1-3t>(1-a)b>0$.

The right column gives the required distances to all three anchors 1, 2, 5. The nonzero anchor area makes these projected positions unique after aligning the anchor triangle. The squared length of edge 36 in the right column minus its marked squared length in the left column is $9(3t-a+b(1-3t))$. Equality of these lengths forces $3t-a=-b(1-3t)<0$. Consequently the projected determinant of 346 is $3(3t-a)(a-b-1)>0$, whereas the determinant of 152 is $-3a<0$. The ratio of their signs is independent of the isometry used to align the anchors. The mask prescribes a positive sign for 152 in the Boolean convention, so 346 must have negative sign. Adding this single sign gives a verified refutation.

## A forced triangle orientation in mask 3981

In coordinates with squared norm $x^2+3y^2$, put $P_1=0$ and absorb the marking shifts on its incident edges into the vertex coordinates. The basis change from the preceding lattice coordinates is $(u,v)\mapsto((u-v)/2,-(u+v)/2)$. The marked signed double areas now sum to 1, so every consistently oriented intrinsic face has positive area. Exact elimination of the equal-radius equations gives the following table. Here $b=P_{2y}$, $d=P_{5y}$, $t=P_{0y}$ and $h=P_{7y}$. Write $D=(1/2,1/2)$ and $S(x,y)=((x-3y)/2,-(x+y)/2)$.

| Vertex | Intrinsic $P_i$ | Projected $R_i$ after aligning face 152 |
| --- | --- | --- |
| 0 | $(1/2,t)$ | $P_0-(1,0)$ |
| 1 | $(0,0)$ | $P_1$ |
| 2 | $(0,b)$ | $P_2$ |
| 4 | $(0,1/3)$ | $P_4-D$ |
| 5 | $(-3d,d)$ | $P_5$ |
| 6 | $((1-6t)/4,(1+2t)/4)$ | $P_6-D$ |
| 7 | $(-(6t+1)/4,h)$ | $SP_7$ |

The three distances to the noncollinear anchors determine $R_0,R_4,R_6$ uniquely. The two distances to 1 and 5 determine $R_7$ once face 175 is required to have orientation opposite to 152. The verifier checks all these distances and the reflected orientation by polynomial identities.

Write $A_{ijk}$ for a marked intrinsic double area and $[ijk]$ for the projected double area in the aligned coordinates. Here $A_{012}=-b/2>0$. Substituting the table and using the equality of the two squared lengths of edge 27 gives
\[
  (9b^2+3b+1)[067]=-3b A_{274}.
\]
The coefficient on the left is $(3b+1/2)^2+3/4>0$, so $[067]>0$. The aligned face 152 has positive orientation and mask 3981 prescribes a negative bit for it. Hence 067 must have a negative bit as well. Adding that single strict sign gives a checked propositional refutation. Lean checks the resulting strict inequality, including when other projected triples are collinear. [ProjectedFaces.lean](../../OrigamiTorus/EightVertex/Type5/ProjectedFaces.lean) · [Exact elimination, area identity and refutation](../../scripts/type5_planar_masks.py)

## Incompatible projected turns in mask 3501

The crease and separation conditions for this mask require $[034]<0<[347]$. In fact the metric forces $[034]>0$ or $[347]<0$, a strict condition that persists under perturbation. The verifier adds this disjunction and replays the refutation. Use the aligned coordinates of the preceding section. Equal-radius elimination gives

| Vertex | Intrinsic coordinates |
| --- | --- |
| 0, 1, 2 | $(c+1/2,h)$, $(0,0)$, $(c,b)$ |
| 3, 4, 5 | $(1/2,k)$, $(c,(c+1)/3)$, $(c,d)$ |
| 6, 7 | $(x+1/2,(x-c+1)/3+h)$, $(x,y)$ |

The island of faces 012, 024 and 152 gives $R_0=P_0$, $R_4=P_4+(1/2,-1/2)$ and aligned anchors. Faces 175 and 357 reflect $P_7$ and $P_3-(1,0)$ across line 15. The island containing 045, 256 and 465 reflects the coherent copy $P_6-(1/2,1/2)$ across the vertical line through 25. These formulas determine all eight projections.

Every marked edge is shortest because its image has the same length as the edge and the map is distance nonincreasing. Thus each marked displacement $(s,t)$ satisfies $|2s|\le1$ and $|s\pm3t|\le1$. Applying these bounds to edges 10 and 12 gives $-1/2\le c\le0$ and $b\ge-1/3$. The intrinsic area $A_{152}=c(b-d)>0$ then gives $c<0$ and $b<d$. Put $v=c-3d$. The marked displacement on 54 is $(-1/2,v/3-1/6)$, giving $v\ge0$ and $d<0$. In particular $1+3(b-d)>0$. Edge 15 gives $1+c+3d\ge0$.

If $v=0$, the length equations on 23 and 27 give $k=1/6$ and $3y=x+1$. Edge 03 then gives $h=-d-1/6$, and edge 16 gives $(6d+1)(x-3d)=0$. The possibility $d=-1/6$ would give $c+3b<c+3d=-1$, contrary to shortestness of edge 12. Hence $x=c$ and $P_7=P_4$. The two marked shifts from 2 to 7 and 4 agree, contradicting $A_{274}>0$.

Suppose $v>0$. Define
\[
 N=c^2+3d^2,\quad L=4c^2+v,\quad D=6bc-2c^2+c+3d,\quad E=4(b-d)c^2+N.
\]
Here $N,L>0$ and $E>3d^2-c^2/3\ge0$. The four edge equations on 23, 47, 27 and 16 successively determine $k,y,x,h$, with $y=(4cd+c+d)x/L$ and $2Dx=(3b-c+1)L$. If $D=0$, the latter equality gives $3b=c-1$, which makes $D=-v\ne0$. Substitution gives $6D A_{274}=-v((3b-c+1/2)^2+3/4)$, hence $D<0$.

For
\[
 f=4bc^2+bc-3bd-4c^2d+c^2+cd+c-d,\qquad g=f+3(b-d)(c-d),
\]
the same edge equations give the two area identities
\[
 E[034]=2cg A_{024},\qquad N(1+3(b-d))[347]=-vf A_{357}.
\]
The verifier checks the equal-radius consequences, the pivots, both area identities and the exceptional case by exact polynomial arithmetic. [Verifier](../../scripts/type5_planar_masks.py)

If $[034]\le0\le[347]$, then $f\le0\le g$. Write $u=-c$ and $d=(-u-v)/3$, so $0<u\le1/2$ and $2u+v\le1$. Since $g-f=(b-d)(v-2u)$, we obtain $v\le2u$. Hold $u,v$ fixed and regard $g$ as an affine function of $b$. Its values at $d$ and at $l=-(2u^2+2u+v)/(6u)$ are
\[
 g(d)=(2u-v)(2u+v-1)/3\le0,\qquad
 g(l)=-v(1-u)(4u^2+v)/(3u)<0.
\]
The identity $D=-6u(b-l)<0$ and $b<d$ put $b$ strictly between these endpoints. Thus $g(b)<0$, a contradiction. The aligned face 152 has the positive sign prescribed by mask 3501, so the turn disjunction also holds in the verifier's coordinates. [Lean affine sign proof](../../OrigamiTorus/EightVertex/Type5/ProjectedFaces.lean)

## A planar folding family for mask 21683

On a dense set of planar folds of this mask the metric forces $[267]<0$, equal signs for $[034],[347]$, and equal signs for $[134],[346]$. Adding those five clauses gives a checked refutation. Density suffices for an embedded lift of the exact projected points because an embedding persists under small changes to its vertices.

Write $P_2=(a,b)$, $P_5=(c,d)$, $P_1=0$, $u=a-c$. The equal-radius equations give
\[
 P_0=(c+1/2,h),\qquad P_3=(c+1/2,b+u/3+1/6),\qquad P_4=(a,d+(1-u)/3).
\]
The anchor island gives $R_0=P_0$, $R_3=P_3$. The island through 1 and 5 reflects $P_4,P_7$ across line 15. The island through 2 and 5 reflects $P_6-(1/2,1/2)$ across line 25. Write $A$ for intrinsic marked double area and brackets for the aligned projection, as above.

Set $s=c+3d$ and $H=2s(h-d)+c-d$. The length equation at 04 and the equal signed areas at face 045 give $JH=KH=0$, where $J=(4u-1)c+3d$ and $K=(4u-1)d-c$. Their squared norm is $J^2+3K^2=((4u-1)^2+3)(c^2+3d^2)>0$. Thus $H=0$. Taking $s=0$ would force $c=d=0$, collapsing edge 15. Write $t=c/s$. Then $c=st$, $d=s(1-t)/3$, $h=d+(1-4t)/6$. Set
\[
 D=4tu-2t+1,\qquad T=4t^2-2t+1,\qquad U=4u^2-2u+1 .
\]
The last two quadratics are strictly positive, and $A_{045}=D/6>0$. The squared-length residual on 24 is affine in $b$ with nonzero coefficient $-3D/T$. This determines the six points with labels 0 through 5 from $s,t,u$.

For generic parameters, the equations on 16 and 36 determine $P_6$ linearly, and the equations on 27 and 37 determine $P_7$ linearly. The verifier solves these two systems over the rational function field, verifies every edge length, and checks the signed area equality on every face.

To see that this chart approximates every nondegenerate fold of the given mask, consider a fold at arbitrary parameters. The isometry on face 136 is reflection across line 13, since its endpoints stay fixed. The orientation-preserving isometry on 164 agrees with that reflection at 1, and the one on 263 agrees at the coherent copy of 3. In intrinsic coordinates translated to the lift of vertex 6 these two agreements cut out lines through 1 and 3, respectively. They meet at 6 and are transverse because face 136 is nondegenerate. The same construction for 7 starts from reflection across 15. The orientation-preserving isometries on 357 and 274 agree with the reflection at the coherent copies of 5 and 4, respectively. These copies are $P_5,P_4$ since edges 57 and 47 have zero shift. The strict projected turn $[457]$ ensures these lines meet transversely at 7. All the isometries here are determined by two distinct known points and an orientation. Hence both intersections depend continuously on the three parameters near the fold. At generic nearby parameters the rational function solution satisfies the signed face isometries and must give these same intersections. Strict face signs persist. An embedded choice of heights at the fold would therefore give an embedded choice at generic parameters.

On the chart $A_{175}=-sT/6$, $A_{152}=-suT/(3D)$, $A_{237}=-t(2t-1)U/(3D)$ and $uT A_{263}=(t-u)D A_{256}$. Their positivity gives $s<0$ and $0<u<t<1/2$. Let $F=4tu-4t+2u+1$, $P=sT+U$, and $C=(1-2t)^2+4tu(1-2u)>0$. The verifier checks
\[
\begin{aligned}
 [267]&=(2t-1)A_{256}, &
 T[034]&=-(2t-1)F A_{053},&
 T[347]&=2tF A_{274},\\
 6TD[134]&=-(2t-1)FP,&
 DP^2[346]&=2(t-u)UC[134].
\end{aligned}
\]
Taking generic parameters with $FP\ne0$ gives the claimed strict signs. [Exact rational identities and refutation](../../scripts/type5_planar_masks.py)

## A height obstruction for mask 11116

Normalize the periods, shifts and anchor as above. Write $P_2=(a,b)$, $d=P_{5y}$, $w=a+3b$ and $\omega=6d+1$. Equal-radius elimination gives
\[
\begin{aligned}
 P_0&=(3h+1,h), &P_3&=(w+1-3k,k), &P_4&=(a-3b-1)(1/2,-1/6),\\
 P_5&=(-3d-1,d), &P_6&=(1-3j,j), &P_7&=(a-3b+3l-1,l).
\end{aligned}
\]
Here $h,k,j,l$ are the second coordinates of the indicated vertices. The anchor island fixes vertices 4 and 7 and translates 6 by $-B$, with $B=(1/2,1/2)$. The opposite island through 1 and 2 reflects $P_0,P_3$ across line 12. Another opposite island through 1 sends $P_5+B$ to $P_5$, so it reflects across the perpendicular bisector direction $B^\perp$. It sends $P_0+(-1/2,1/2)$ to $R_0$. If $w=0$, line 12 is $B^\perp$ and the two reflected copies of 0 cannot agree. The equality of their second coordinates gives $2wh+a+b=0$.

Set $x=w+1$ and $y=2a/w$. Then $P_0=((1-y)/2,-(1+y)/6)$, $R_0=(-1/2,(2y-1)/6)$ and $P_3=(x-3k,k)$. The squared-length residual of edge 53 is affine in $k$ with coefficient $-6(y^2-\omega)/(y^2-y+1)$. Shortestness of edge 15 gives $P_{5x}\ge-1/2$, so $\omega\le0$. If $y=\omega=0$ then $P_0=P_5+(1,0)$ and the marked edge 05 has zero length. Thus the coefficient never vanishes in a nondegenerate fold.

Let $O$ be the rotation taking $P_3$ to $R_3$. The signed face isometry on 136 gives $(I-O)P_6=B$. Similarly let $U$ be the rotation taking $P_3+K_{23}-P_2$ to $R_3-R_2$. The isometry on 237 gives $(I-U)(P_7-P_2)=U K_{27}$. Both right sides are nonzero. A plane rotation different from the identity has invertible $I-O$, so these equations determine both vertices. All three reconstructions continue near every nondegenerate fold in the parameters $w,y,\omega$. At generic parameters put $z=-\omega/x$. The verifier reconstructs the eight vertices over $\mathbb Q(x,y,z)$ and checks all 24 marked squared lengths and all 16 signed face areas. Hence an embedded height lift at any original fold would persist on a generic member of this chart. Heights can also be perturbed to make all spatial brackets strict. [Chart and identities](../../scripts/type5_planar_height.py)

On the chart $A_{256}=x A_{465}$, $A_{024}=(1-y)(x^2-x+1)/6$ and $A_{274}=(1-x-y)/6$. Thus $x>0$, $y<1$, $x+y<1$. The identities $[047]=x(1-y)(1-x-y)/6$ and $[057]=x(xz+y^2)/6$ give two further positive projected signs.

There is one projected sign word to test arithmetically: $\mathtt{93cff3f81e4ce6}$, with bit zero for the first of the 56 increasing triples in lexicographic order. In this word no height assignment can have the following five spatial signs, up to common reversal,
\[
 [0135]>0,\quad [0237]<0,\quad [1347]<0,\quad [1357]>0,\quad [2457]>0.
\]
Subtract the affine height of the anchor plane. These five signed volumes are five linear forms in the heights at $0,3,4,7$. For their $5\times4$ coefficient matrix the alternating maximal minors give a linear dependence. The checker verifies the dependence identically and proves its five coefficients have the same strict sign. Their weighted sum vanishes, so the five forms cannot all be positive.

To check the cofactor signs, factor the intrinsic double areas and projected brackets as rational functions of $x,y,z$. Multiplication of signs gives linear equations modulo two in the signs of the irreducible factors. One additional polynomial has certified positive sign because it is a sum of seven products with positive coefficients. The checker verifies positivity of every factor in those products from the area signs, expands the sum, and uses its factorization to determine the signs of the cofactor ratios. The final propositional refutation checks that the two extra projected signs together with this conditional height obstruction exclude the entire mask, including all other projected sign words. [Seven-product certificate](../../scripts/type5_planar_height.py) · [Propositional replay](../../scripts/type5_planar_masks.py)

## Exact verification

From the repository root, with SymPy installed, run

```sh
python3 scripts/type5_planar_masks.py
```

The verifier assigns one Boolean to each projected triple and spatial quadruple with increasing labels. It imposes the three-term Grassmann–Plücker relations, both in each separate dimension and for the spatial homogeneous points with the vertical point at infinity added. Brackets involving the latter agree with projected three-point brackets up to one fixed sign. The signed cofactors of four planar or five spatial points sum to zero, so both signs occur. A spatial edge cannot intersect a disjoint face, which forbids the corresponding cofactor sign partition. Nor can a strictly supported vertex lie in the convex hull of three planar or four spatial neighbors. Finally the strict projected signs and crease determinant sums above are imposed. A simultaneous negation of all spatial signs, if needed, is achieved by reversing the heights. The Python verifier regenerates the clauses, exhaustively tests the crease-sign assignments, and invokes CaDiCaL to produce proof traces. A separate check within the script replays each reverse-unit-propagation step leading to the empty clause. It also tests the surviving Boolean assignment against every generated clause. The script accepts CaDiCaL from the executable path or the Lean toolchain. [Verifier](../../scripts/type5_planar_masks.py)

## A planar limit excluded by the hexagonal anchor face

**Mask 11149 cannot be the limit of embedded Type 5 realizations at the fixed hexagonal periods if all its projected faces have positive area in absolute value.** This excludes the last representative for this construction. It uses the strict supporting plane of face 125 at every hexagonal embedding. The projected turn arguments for mask 11149 force the following nine strict signs, up to a common reversal of the plane orientation,
\[
 [012],[013],[023],[016],[056],[125],[256]>0,\qquad [035],[126]<0.
\]
Here brackets are signed projected double areas. The signs persist near the planar map. The hexagonal verifier checks that all nine occur among the strict signs obtained from the mask. [Hexagonal support theorem](Type5HexagonalAngles.md) · [Verifier](../../scripts/type5_rectangles/hex_angles.py)

To see the geometric obstruction, normalize the projected points $0,1,2$ to $(0,0),(1,0),(0,1)$ by an affine map. Write $A,B,U,V$ for the projected rays from vertex 2 to vertices $1,5,0,6$, respectively. The signs $[125],[256]>0$ and $[126]<0$ put $A$ strictly inside the cone on $B,V$. If $x_5\le0$, the signs $[013],[023]>0$ and $[035]<0$ give $y_5>0$. The signs $[016],[056]>0$ then give $x_6<0$. A positive combination of $B,V$ could not have the positive first coordinate of $A$. Thus $x_5>0$, and
\[
 B=x_5 A+(1-x_5-y_5)U
\]
puts $B$ strictly inside the cone on $A,U$.

Subtract the affine height function of the anchor plane, then reverse the vertical axis if needed. The anchors have height zero, and vertices 0 and 6 have positive heights. Near vertex 2, on ray $A$, face 012 has height zero and face 256 has positive height. On ray $B$ the order reverses. The two affine height functions therefore agree strictly between those rays. The relative interiors of faces 012 and 256 intersect, although the faces share only vertex 2. Lean verifies the cone memberships and gives positive barycentric coefficients for the intersection. [ProjectedFaces.lean](../../OrigamiTorus/EightVertex/Type5/ProjectedFaces.lean)

Consequently none of the 62 archived classes yields a hexagonal embedding by first finding an embedded height lift of the exact planar projection and then opening it at fixed periods. The proofs for 11116 and 21683 perturb within the planar family. A singular opening whose limiting projection has no embedded height lift remains a separate possibility. For masks 3501, 3981, 11116 and 11149 every vertex has at least four creases, hence strict projected support at the limit. The strict projected signs persist for nearby embeddings. On each limiting crease the adjacent projected faces still lie to the same side; their distinct slopes have a signed exterior turn tending to $+\pi$ or $-\pi$ on the unwrapped cylinder link. On same-sign edges it tends to zero. Thus the signed crease counts used in the refutations also apply to a convergent sequence, after taking a subsequence fixing the crease signs.
