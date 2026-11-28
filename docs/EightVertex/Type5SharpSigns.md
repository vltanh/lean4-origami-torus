# Seventeen spatial signs on the open sharp ray

For periods \(1,1/2+iy\) with \(y>\sqrt3/2\), write \(t=y^2-3/4\) and \(u=t/(1+2t)\). The same seventeen signed tetrahedra certify the spatial embedding for every \(0<u<1/2\). Here \([ijkl]=\det(r_j-r_i,r_k-r_i,r_l-r_i)\). The signs refer to the sharp family with positive root heights at vertices 3 and 4 and the leaf branches chosen at the base point below. [Core coordinates](Type5SharpEmbeddings.md) · [Exact verifier](../../scripts/type5_rectangles/sharp_signs.py)

| Vertices in the tetrahedron | Signed brackets |
|---|---|
| Four core vertices | \(1234+,1245+,1345-,2345+\) |
| Three core vertices and one leaf | \(0125+,0134-,0234-,1236-,1237+,1356+,1357-,1456+,2347-,2456-\) |
| Two core vertices and two leaves | \(0126+,0136-,2467-\) |

## The core and the five-point Gram matrix

Use \(t=u/(1-2u)\). The program reads the square shifts and oriented faces from Lean and uses the same core coordinate function as the direct radical construction. Represent a planar coordinate \((X,Y)\) by \((X,yY)\). The inner product has matrix \(\operatorname{diag}(1,1/y^2)\), so the anchor projections and the squared heights \(H_3,H_4\) are rational functions of \(u\). The verifier checks all coordinate denominators, \(y^2>0\), positivity of the marked anchor face, \(H_3,H_4>0\) and equality of the nine core lengths. In spatial coordinates \((X,yY,Z/\sqrt{H_3})\), root 3 has third coordinate 1 and root 4 has third coordinate \(g=\sqrt{H_4/H_3}\). This coordinate change preserves the signs of spatial determinants. [Projection and sign formulas](../../scripts/type5_rectangles/projections.py)

Around each leaf, take the five mixed vectors \(Y_i=(r_i-r,p_i-p)\), using the intrinsic lifts at that leaf. At a completion the Gram matrix \(S\), for the form \(\|r\|^2-\|p\|^2\), has zero diagonal. Its off-diagonal entries are half the intrinsic squared distances minus half the spatial squared distances of the corresponding pairs. The verifier checks that the link entries vanish and the complementary five entries are strictly positive. In particular the entry for pair 34 includes \(+H_3g\), since both root heights are positive. The five positives give two distinct continuous completions and keep every incident triangle nondegenerate throughout \(0<u<1/2\). [Five-cycle proof](Type5PositiveCycle.md)

At \(u=1/4\), equivalently \(t=1/2\), the verifier reconstructs the leaves in order \(0,6,7\) with quadratic-formula signs \(+,-,+\). Outward rational enclosures verify the seventeen displayed signs and all sixteen positive marked face areas. Continue these three choices of leaves along the interval. Continuity and nondegeneracy give the same marked face orientations everywhere.

## Excluding a zero of each bracket

Compute the four core brackets directly in \(\mathbb Q(u)(g)\). For each of the ten one-leaf brackets, fix the plane through its three core points. Let \(n\) be its spatial covector and \(v_i=n(r_i-r_a)\), with \(r_a\) on the plane. If the leaf were on this plane, these would be the five evaluations of \((n,0)\) on the mixed basis \(Y_i\). Thus

\[
 v^T\operatorname{adj}(S)v=\det(S)\,\|n\|_*^2 .
\]

The dual norm in scaled coordinates is \(n_x^2+y^2n_y^2+n_z^2/H_3\). The difference of the two sides has strict sign for each tested triple. This rules out coplanarity for either completion. In particular the chosen covector cannot vanish. Lean proves the mixed Gram identity for five arbitrary rows, and specializes it to the five null rays and an incident spatial plane in `leafPlane_eliminant_eq_zero`. [Leaf plane eliminant](../../OrigamiTorus/EightVertex/Type5/LeafEliminant.lean)

For a two-leaf bracket, allow the plane to vary through its two core points. Write \(e\) for their difference. On edges 13 and 24 the covectors \((e_z,0,-e_x),(0,e_z,-e_y)\) span the normals because \(e_z\ne0\). Edge 12 is horizontal and has distinct endpoints. Its normal basis is \((-e_y,e_x,0),(0,0,1)\). For a linear combination of the basis covectors, the preceding Gram identity is a homogeneous binary quadratic. A common plane would give a common projective zero of the two leaf quadratics. For coefficients \((A,B,C)\) and \((D,E,F)\), including the mixed coefficients as written, the necessary resultant equation is

\[
 (AF-CD)^2-(AE-BD)(BF-CE)=0.
\]

Lean proves the projective-root implication in `binaryQuadratic_resultant_eq_zero`. The verifier certifies the nonvanishing of every common factor it removes. It then checks the norm of the resultant in the quadratic algebra. A nonzero norm excludes a zero for either choice of the conjugate and for either completion at each leaf. The largest polynomial degrees checked in the three binary calculations are 220, 342 and 392 for \(0126,0136,2467\), respectively. [Binary pencils and rescalings](../../scripts/type5_rectangles/two_leaves.py) · [Gram and adjugate formulas](Type5FoldedModuli.md#planes-containing-a-leaf)

Every rational sign test uses the following elementary calculation. For a nonzero polynomial \(p\) of degree \(n\) and rational \(l<r\), expand
\[
 (1+z)^n p\!\left(\frac{l+rz}{1+z}\right).
\]
If every nonzero coefficient has the same sign, then \(p\) has that strict sign at every point of \((l,r)\). The initial interval is \((0,1/2)\). When a sign requires subdivision, the test checks the midpoint separately. This permits zeros at the excluded endpoints. For a quadratic expression \(a+bg\), the signs of \(a,b\) suffice when they agree. Otherwise the norm \(a^2-b^2g^2\) determines the dominant term. The global nonvanishing results carry each of the seventeen base-point signs along its continuous branch.

## From signs to embedding

The alternating sum of the five core brackets gives \(1235+\). Twelve three-term Grassmann–Plücker identities then establish the strict sides in the following table. Each plane row covers support sets lying in the union of its three labels and the labels on its indicated side.

| Plane through | Positive side | Negative side |
|---|---|---|
| 126 | 3457 | 0 |
| 127 | 4 | 036 |
| 134 | 026 | 57 |
| 136 | 0 | 245 |
| 145 | 26 | 37 |
| 234 | 05 | 167 |
| 246 | 15 | 037 |

Each pair of disjoint subfaces fits on opposite sides of one row, allowing either order. A convex combination on the plane can use only its plane labels. The three plane points are affinely independent since each row has a strictly positive fourth point. Hence disjoint supports have disjoint closed hulls even when they both meet the plane. Lean checks the determinant implication, the finite coverage and the closed-embedding conclusion in `OrigamiTorus.Type5.SharpRay.spatial_embedding`. The transfer of the parameter formulas to those seventeen hypotheses above uses the exact Python verifier. [Sharp-ray sign theorem](../../OrigamiTorus/EightVertex/Type5/SharpRaySeparation.lean) · [Closed-hull argument](../../OrigamiTorus/EightVertex/Type5/BracketEmbedding.lean)

From a built checkout with python-flint installed, run

```sh
python -m scripts.type5_rectangles sharp-signs
lake build OrigamiTorus.EightVertex.Type5.SharpRaySeparation
```
