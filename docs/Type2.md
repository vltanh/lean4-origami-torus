# Type 2 nonexistence

No embedded polyhedral realization of Lutz Type 2 has cone angle $2\pi$ at all eight vertices. This answers the question in [Lander, §6](https://arxiv.org/abs/2609.10703). The proof below gives the geometric reduction by hand and uses an explicit finite propositional refutation for its final step.

In this proof the faces are

```text
046 047 056 057 135 136 145 147
167 234 237 245 256 267 346 357
```

The map from the data file's labels $0,\ldots,7$ to these labels is $0,4,7,6,5,1,3,2$. Substitution in the face lists verifies the relabeling. The graph is $K_8$ with $01,02,03,12$ deleted. In particular, $4,5,6,7$ are adjacent to every other vertex.

## Flat stars have strict support

For a vertex $v$, intersect its star with a sufficiently small sphere centered at $v$ and rescale to the unit sphere. The result is a simple closed polygon of shorter great-circle arcs. Its length is the sum of the face angles at $v$, hence $2\pi$. Its polygon vertices are the unit directions from $v$ to its neighbors. We show that the directions lie in an open hemisphere.

If the origin is in their convex hull, choose a minimal set of directions whose convex hull contains it. The associated relation has all coefficients positive. There are at most four directions, and every proper subset is linearly independent. Indeed, a linear dependence on a proper subset could be subtracted from the positive relation, with the sign and scale chosen so that one positive coefficient first becomes zero. The result would be a strictly smaller convex representation after renormalization.

If there are four directions, name them $a,b,c,d$ in link order. The positive relation gives a unit direction $r$ on the interior of the shorter arc $ab$ whose antipode $-r$ lies on the interior of $cd$. The perimeter of $abcd$ is the sum of the lengths of the broken arcs $rb c(-r)$ and $(-r)da r$. Each is at least $\pi$. Equality in the first would put $r,b,c$ in one plane through the origin, so $a,b,c$ would lie in that plane as well. Thus the perimeter exceeds $2\pi$, whereas shortening the four subpaths of the link gives perimeter at most $2\pi$.

If there are three directions, they lie on a great circle and their three shorter arcs partition that circle. Their perimeter is $2\pi$. Every subpath of the link between successive directions must therefore be the unique shorter arc between them, so the whole star is planar. A planar star is impossible. If $v$ is among $0,1,2,3$, its vertices include the complete graph on $v,4,5,6,7$. If $v$ is among $4,5,6,7$, they include the complete graph on $3,4,5,6,7$. For the elementary straight-line obstruction, no three of the five points can be collinear because all pairs are edges. If at least four points are on their convex hull, their diagonals cross. Otherwise the hull is a triangle. Joining one of the two interior points to the three corners partitions the triangle into three subtriangles. The other interior point lies strictly in one of them, and its edge to the opposite corner crosses a partition edge.

It remains to consider two antipodal directions, coming from neighbors $a,b$. The two parts of the link from $a$ to $b$ both have their minimal possible length $\pi$. Split either part at one of its interior directions. The distances from the split point to the two antipodes sum to $\pi$, so both shorter subpaths are their unique minimizing arcs. Together they give a geodesic semicircle. The edge $ab$ would pass through $v$, so $ab$ is absent and both endpoints are among $0,1,2,3$. At least three of the universally adjacent vertices are neighbors of $v$. None has the same direction as $a$ or $b$, so two of them, $w,x$, lie on the interior of the same semicircle. In that semicircle, order the four rays as $a,w,x,b$. The ray from $v$ through $w$ meets the relative interior of segment $ax$. The edge $vw$ must stop before that intersection, since $ax$ is also an edge. The intersection has strictly smaller height above the line $ab$ than $x$, so $w$ has strictly smaller height than $x$. Now the ray through $x$ meets segment $wb$, and the same argument makes $x$ strictly lower than $w$. This is a contradiction.

This excludes all possible minimal sets. Strict separation of the origin from the convex hull of the directions supplies the required hemisphere. Lean proves this conclusion for an embedded Type 2 star with cone angle \(2\pi\) in `strictSupport_of_flat_embedding`. The formal proof uses two algebraic arguments for the final exclusions. [Type2Links.lean](../OrigamiTorus/Type2Links.lean) · [Type2StrictSupport.lean](../OrigamiTorus/Type2StrictSupport.lean) · [Schwartz, §2.1](https://arxiv.org/abs/2507.14998v9)

For the antipodal exclusion, put the star center at the origin and use the same ray order \(a,w,x,b\). Equality in angular path shortening yields \(w=p a+r x\) and \(x=s w+t b\) with nonnegative coefficients. If \(p+r\ge1\), the point \(w/(p+r)\) lies on both \(vw\) and \(ax\). The embedding therefore gives \(p+r<1\), and likewise \(s+t<1\). Substitution gives \((1-rs)w=p a+rt b\). Since \(rs<1\) and \(a,b\) are antipodal, \(w\) would lie on their line, contradicting distinct rays.

For the planar complete-graph exclusion, the affine dependence space of five planar points has dimension at least two. Every nonzero dependence has at least three coefficients of one strict sign if all disjoint sets of at most two vertices have disjoint convex hulls. Otherwise the normalized positive and negative coefficients give a common convex combination of two such sets. Choose independent dependences \(u,w\) and take \(u+t w\) over all real \(t\). This line avoids zero. The sets of \(t\) with three positive and with three negative coefficients are open and disjoint. Each is nonempty because the two tails have opposite signs on every nonzero coefficient of \(w\). These two sets cannot cover the real line. [PlanarCompleteGraph.lean](../OrigamiTorus/PlanarCompleteGraph.lean)

## Each flat star has a mixed-side face

Project the link radially from the open hemisphere to the affine plane $n\cdot q=1$, where $n$ is its supporting normal. The projected link is a simple polygon. If no incident face has neighboring vertices strictly on both sides of its plane, every edge of this polygon lies on a supporting line of the convex hull of the projected vertices. The convex hull boundary is homeomorphic to a circle, and removing any omitted point would put the simple closed polygon into an open interval. Thus the polygon is the entire boundary.

A convex spherical polygon in an open hemisphere has perimeter less than $2\pi$. To see this, enclose its planar projection in an ordinary triangle and lift that triangle back to the sphere. If $a,b,c$ are its spherical vertices, then $d(a,b)+d(a,c)=2\pi-d(-a,b)-d(-a,c)$. The triangle inequality for $b,-a,c$ is strict, since the shorter arc $bc$ lies in the open hemisphere and $-a$ lies outside it. Thus the enclosing triangle has perimeter less than $2\pi$. Cut this triangle by the planar supporting half-planes, one at a time. Under the inverse radial projection each cut replaces a boundary path by a shorter great-circle arc or leaves the polygon unchanged. The perimeter cannot increase. This contradicts the length of the link.

We use the mixed-side witnesses only at $0,1,2$.

Lean checks that central projection preserves angles and determinant side signs. Projected segments meet exactly at their shared labeled endpoints. The no-mixed-face hypothesis puts each edge on the relative boundary of the projected hull. If the link omitted a boundary point, the punctured boundary would map injectively and continuously into the real line. At a link vertex of maximal image, the images of its two incident segments would both contain the intervening interval up to that maximum, contradicting the segment intersection rule. Lean therefore identifies the entire boundary and proves that the supporting half-planes cut out the projected hull in its affine plane. [Type2Projection.lean](../OrigamiTorus/Type2Projection.lean) · [PlanarBoundary.lean](../OrigamiTorus/PlanarBoundary.lean)

Lean gives an enclosing triangle with angular perimeter below \(2\pi\) and clips it by the supporting half-planes of the projected hull. Each cut preserves that perimeter bound. The clipped boundary and the original link admit a common refinement obtained by inserting vertices into their edges. These insertions preserve angular length. Once the lists share all vertices, connectedness puts each open edge in a single edge of the other list, so their unordered edges agree. Lean therefore proves the mixed-side witness for every embedded flat Type 2 star in `mixedFace_of_flat_embedding`. [PlanarPolygonCut.lean](../OrigamiTorus/PlanarPolygonCut.lean) · [PolygonPerimeter.lean](../OrigamiTorus/PolygonPerimeter.lean) · [Type2Projection.lean](../OrigamiTorus/Type2Projection.lean)

## Passage to determinant signs

Strict support and the mixed-side inequalities survive small perturbations. Embeddedness also survives. For any two faces, consider all pairs of convex weights supported on the respective faces whose supports are disjoint. This is a compact set, since both sets of weights lie in a closed simplex and disjointness is expressed by coordinatewise zero products. The images of the two combinations have positive distance throughout this compact set by embeddedness. There are finitely many face pairs. A small vertex perturbation therefore preserves disjointness of all such convex combinations. Subtracting common weights and renormalizing reduces any unwanted coincidence to one with disjoint supports, so this proves openness. For a generic perturbation, move vertex $i$ by $t(i,i^2,i^3)$ with $t$ small. The determinant of any four distinct vertices is a cubic in $t$ whose leading coefficient is a nonzero Vandermonde determinant, so we can avoid all its roots for every quadruple. We may also reflect to make $[0123]>0$. [Type2Perturbation.lean](../OrigamiTorus/Type2Perturbation.lean)

Write $[abcd]$ for the determinant with rows $(1,p_i)$ in the listed order. The following sign restrictions are now necessary.

1. For a sorted pair $S$ and distinct $a<b<c<d$ outside it, the products in
   $$
   [Sab][Scd]-[Sac][Sbd]+[Sad][Sbc]=0
   $$
   cannot have one strict sign when the indicated minus is included. This identity is the two-dimensional bracket identity after quotienting the homogeneous row space by the two rows indexed by $S$.
2. For an increasing five-tuple $C$, the five numbers $(-1)^i[C\setminus C_i]$ are the coefficients of an affine dependence by cofactor expansion. They sum to zero. The positive and negative parts give equal convex combinations after each part is divided by its total absolute weight. If the two parts are an edge and a complementary face, the embedding is contradicted. If one part is a singleton and all four other vertices are its neighbors, strict support is contradicted.
3. At each of $0,1,2$ mark one incident face $abc$ that has neighbors strictly on both sides of its plane. At least one of the ordered brackets $[abcw]$ for the other neighbors $w$ is positive and at least one is negative.

The first rule supplies 16 forbidden sign patterns per Plücker relation. The second and third rules give clauses by the indicated sign partitions and face choices. These rules produce 7,464 clauses, including the normalization, in the order specified in [Defs.lean](../OrigamiTorus/Defs.lean).

## Finite refutation

The refutation uses 741 input clauses and 363 inferences. The predecessor lists and conclusions are in [Type2Certificate.lean](../OrigamiTorus/Type2Certificate.lean). The rule for checking a line is elementary. Temporarily assume that every literal in its conclusion is false. Read the predecessor clauses in the listed order and delete literals already known to be false. If one literal remains, it must be true. When no literal remains, the temporary assumptions have led to a contradiction, so the conclusion follows. The last conclusion is empty. Each step follows from its predecessors, independently of the SAT search that found the certificate.

For example, line 741 has the signed literals `[-61, 18, -39, -19, -38]`. Its predecessors are line 0, containing `[1]`, and line 49, containing `[-1, -61, 18, -39, -19, -38]`. Temporarily falsifying the five conclusion literals and using line 0 falsifies all of line 49. This is the first inference. The other lines use the same rule, sometimes propagating several singletons before reaching the empty clause.

The contradiction applies to any flat embedding of the given face list, including one whose original vertex positions have coplanar subsets. The perturbation is used solely to derive signs, so its perturbed angles can differ from the original angles.

Lean proves that the normalized generic placement obtained by perturbation and reflection satisfies the three clause families. It derives the orientation of each bracket atom from the parity of the swaps in the sort, then uses the Plücker identity, the signed supports of affine dependences, and the selected mixed-side witnesses. The theorem `Type2.type2_nonexistence` applies the refutation directly to an embedded placement with angle sum \(2\pi\) at each vertex. The SAT search found the certificate. Checking the theorem requires only Lean and Mathlib. [Type2BracketSigns.lean](../OrigamiTorus/Type2BracketSigns.lean) · [Type2Nonexistence.lean](../OrigamiTorus/Type2Nonexistence.lean)
