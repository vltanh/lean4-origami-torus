# Types 4 and 7: an unbounded certified strip of flat-torus moduli

## Theorem

For each modulus tau = x + i y with 0 <= x <= 1/200 and y > 0, x^2+y^2 >= 1, both the Lutz Type 7 and Type 4 eight-vertex torus triangulations have an embedded, intrinsically flat realization of this similarity class in R^3. Scaling produces any desired overall size. In particular both realize every rectangular flat torus. The realizations obtained by the argument are regular points of the seven flatness and two marked-shape equations.

This is a computer-assisted partial result on universality, **not** a complete classification of universal triangulations. The previous Type 2 and Type 6 certificates are not required here and are not independently audited by this package.

## Reproduction

Python 3 and SymPy are required. From this directory, run `python verify.py` (without `-O`). The verifier contains all data. It uses rational function identities, integer/rational polynomial coefficients, and exact comparisons only; no numerical optimization or floating-point checks are used. `verification.txt` records a successful run.

## Construction

Set w=y^2, H=33/20, r=-13/60, a=Hx, D=H-1+a, q=H/D. Define

    T5 = ((a^2-a+H^2*w)*q/H-1)/(1+q^2*w)
    T3 = -(-a^2*q+2*a*H+a*q+H^2*q*w+H*q^2*r*w+H*r-H)/((H+q*r)*(q^2*w+1))

The planar points (X,Y), written in coordinates with physical position (X,yY), are

    P0=(0,0), P1=(1-a-r,H+q*r), P2=(1/2,0),
    P3=(a+T3,H+q*T3), P4=(1,0), P5=(1+T5,q*T5),
    P6=(a,H), P7=(1-a,H).

All displayed denominators are positive on the domain: D>0, H+qr=H(D+r)/D>0 and 1+q^2*w>0. These are flattened bases, not themselves embedded tori. The Type 7 face list is

    356 325 364 302 341 310 506 524 547 570 674 601 617 214 207 271

Replace 356,325 by 632,625 for Type 4. The script checks the relabeling to Lutz Type 4 and that the shared quadrilateral is strictly convex in the planar base. In a neighborhood of this base in horizontal coordinates, diagonal exchange preserves the intrinsic metric and all cone angles.

## Why the exact checks suffice

1. **Signs on an unbounded domain.** For a rational expression, check numerator and denominator separately after substituting w=1-x^2+h, x=t/200. This makes 0<=t<=1, h>=0. Express each coefficient of h as a polynomial in t in the Bernstein basis. Nonnegative Bernstein coefficients for all powers of h, with strictly positive coefficients for h^0, imply strict positivity on the entire domain. Reverse all signs for strict negativity. The verifier returns 0 for expressions it cannot sign-certify; this is not a claim that they vanish. The denominators of the base coordinates were justified above. Other rational formulas in the development and Jacobian have denominators given by nonzero edge lengths or those same base denominators.

2. **Flatness.** All triangles are nondegenerate by strict signed areas. With u and v the planar edge vectors at a corner, the complex number u dot v + i |det(u,v)| has argument equal to the corner angle in (0,pi). In the scaled coordinates, the actual imaginary part includes sqrt(w). The product of these numbers around each vertex is real and nonzero by exact rational-function identities; at the square base its real part is positive. Connectedness and continuity make the product positive throughout. An exact comparison with multiples of pi/4 bounds every cone-angle sum at the square base strictly below 4pi. The sums are positive multiples of 2pi, hence equal 2pi at that base and, by continuity, everywhere. The same holds after the convex diagonal flip.

3. **Modulus.** A primal spanning tree and disjoint dual spanning tree give a tree-cotree decomposition, with two leftover edges. Develop the oriented faces along the dual tree using Euclidean isometries, in the scaled planar coordinates. Since the closed oriented surface is intrinsically flat and homeomorphic to a torus, its universal cover is the Euclidean plane and its holonomy is a lattice of translations. The two dual loops from the leftover edges give a lattice basis (tree-cotree presentation of H_1). The script obtains their translation vectors u,v and uses the unimodular change (u,v) -> (u,u+v). It verifies that in this new basis the dot-product ratio is x and the scaled cross-product ratio is 1. The physical cross-product ratio is sqrt(w). Thus the marked shape is x+i sqrt(w).

4. **Rank.** The script checks a nonzero 7x7 minor of the horizontal angle-sum Jacobian, with rows divided by sqrt(w). The angle equations are independent. The explicit two-parameter family supplies two tangent directions in their kernel giving independent shape derivatives (w>0). In taking these derivatives, the actual coordinates are (X,yY); the family extends smoothly to a neighborhood of each parameter point, and the flatness and shape identities continue locally, including at domain boundaries. Thus the seven angle equations and two local marked-shape equations have joint rank nine in the horizontal coordinates. The omitted eighth angle equation follows from the sum of all face angles (16*pi). Convex diagonal exchange preserves these equations in a neighborhood of the flattened base, so the rank is the same for Type 4.

5. **Lift.** Start with the heights (3/13,-3/8,-3/7,12/13,1,-1,1,0). For every quadruple the verifier finds a strictly noncollinear projected triple, so an arbitrarily small generic perturbation of the heights makes every affine 4-point determinant nonzero. For each disjoint edge ab and face cde, order the five points as a,b,c,d,e. Write V_i for the affine determinant obtained by deleting point i. In general position the affine dependence coefficients are proportional to (-1)^i V_i. An intersection would require the first two coefficients to have the same sign, the last three to have the opposite sign. In particular it requires V0*V1<0, V2*V3<0, V3*V4<0, V2*V4>0. The verifier finds at least one strict contradiction for every such edge/face pair (144 Type 7, 140 Type 4). Each strict witness survives a sufficiently small height perturbation. In general position a simplicial surface with nondegenerate triangles and no disjoint edge/face intersections is embedded: an unintended triangle intersection entails such a crossing (the coplanar and vertex-on-face degeneracies are excluded by general position). This is the embeddedness criterion used in the published universality approach.

6. **Inflation at fixed modulus.** For any fixed parameter, choose the generic perturbed heights Z. Apply the implicit function theorem to the seven flatness equations and two shape equations at the planar base, varying nine suitable horizontal coordinates as the vertical coordinates vary from zero to epsilon Z. This gives corrected horizontal coordinates P+delta(epsilon), with delta(epsilon)->0, keeping the same intrinsic shape and flatness. The local marked shape functions are smooth near the base, for example by developing along fixed dual paths and taking the indicated ratios of period displacement vectors, restricted to the flat locus. For all sufficiently small positive epsilon, the surface (P+delta(epsilon),Z) is embedded by openness of the strict generic embedding conditions. Its invertible vertical rescaling (P+delta(epsilon),epsilon Z) is likewise embedded. This latter surface is the exact flat torus supplied by the implicit function theorem. There is no claim that the uncorrected planar base or the uncorrected lift is isometric to the target.

## Sources and limitations

The planar square seed, its height direction and the Type 7 face labeling come from Fabian Lander's *The two most symmetric flat tori as eight-vertex paper tori*, arXiv:2609.10703, and its public verification data: https://github.com/FabianLander/eight-vertex-paper-tori-verification/blob/main/data.py . The inflation approach follows Doyle, Lander, Schwartz and Trettel, *A Universal 8-Vertex Origami Torus Triangulation*, arXiv:2611.21909. The Type 7 literature also includes Doyle and Schwartz, arXiv:2510.12623.

The new result is the rational extension and the exact unbounded-strip certificate, including the Type 4 flip. No independent mathematical audit has been performed. Wider-strip numerical lift searches were not successfully certified and are excluded. The sharp-rhombic ray for Type 7, the complement of the certified strip for Type 4 (apart from other existing results), and the universal classification for Type 5 are not resolved by this package. Failure to find other lifts does not prove nonuniversality.
