# Related work and attribution

The problem here fixes both the number of vertices and the labeled triangulation. An ordinary polyhedral embedding can have nonzero cone angles. An origami realization requires the intrinsic flat metric, and a universal triangulation realizes every such metric with the same face complex.

## Flat tori before the eight-vertex results

- Burago and Zalgaller gave early polyhedral realizations and proved that compact orientable surfaces with a polyhedral metric admit piecewise-linear isometric embeddings in $\mathbb R^3$. The general theorem allows subdivision. It already implies existence for every flat torus. [1995 paper, English translation 1996](https://www.mathnet.ru/eng/aa555)
- Zalgaller developed explicit isometric bends of polyhedral cylinders. Tsuboi later gave an explicit origami construction for every modulus and acknowledged the related diplotori of Arnoux, Lelièvre, and Málaga. These constructions supply the prescribed intrinsic metric without an eight-vertex bound. [Zalgaller, 1997/2000](https://doi.org/10.1007/s10958-000-0007-3) · [Tsuboi, 2024](https://www.ms.u-tokyo.ac.jp/journal/31-2-1.pdf) · [Diplotori, by the authors](https://www.math-communication-network.imaginary.org/hands-on/diplotori-flat-polyhedral-tori)
- Quintanar gave an explicit piecewise-linear isometric embedding of the square torus with 40 vertices and 80 faces. The Type 5 result here gives exact coordinates on a particular eight-vertex triangulation. [Quintanar, 2020](https://jocg.org/index.php/jocg/article/view/3114)
- Lazarus and Tallerie gave one universal triangulation with 2,434 triangles. This fixes a single combinatorial type for all flat tori, years before universality was proved at eight vertices. The count here refers to the final journal version. [Lazarus and Tallerie, 2024, Theorem 1 and §5](https://doi.org/10.1007/s00454-023-00598-7)

## The seven eight-vertex types

The underlying census comes from enumerations by Lutz and Sulanke. Hougardy, Lutz, and Zelke tabulate seven types on eight vertices and give integer-coordinate polyhedral embeddings for all seven. The labels used here match the face lists in Lander and Trettel's numerical dataset. The two types of degree sequence $55666677$ can be distinguished by their face lists. [Sulanke and Lutz](https://arxiv.org/abs/math/0610022v3) · [Hougardy, Lutz, and Zelke, §2](https://arxiv.org/pdf/0709.2794#page=2) · [Lander and Trettel's dataset](https://github.com/FabianLander/low-vertex-flat-tori)

Schwartz proved that no seven-vertex paper torus exists and constructed an eight-vertex one. Lander observed that flatness at the degree-three vertex of Type 1 permits removal of its star without changing the intrinsic surface. This gives Type 1 nonexistence from Schwartz's lower bound. Lander also reported numerical square realizations on five types and conjectured that the remaining type, with degree sequence $45567777$ (Type 2), admits no flat embedding at any modulus. [Schwartz, Theorems 1.1–1.2 and §2](https://arxiv.org/abs/2507.14998v9) · [PNAS account, 2026](https://doi.org/10.1073/pnas.2523301123) · [Lander, §6 and Appendix B](https://arxiv.org/html/2609.10703v1#S6)

Doyle and Schwartz proved near universality on the valence-regular Type 7. Their family reaches all moduli outside the rectangular and sharp-rhombic rays, including rhombi whose diagonal aspect ratio lies strictly between $1$ and $\sqrt3$. Lander proved exact existence on Type 7 at the square and on Type 3 at the hexagonal torus. His local submersion proof gives neighborhoods of those moduli and initial segments of their respective rays. The planar folded families in his §3 sweep the rays, and §6 records the remaining question of embedding them away from those neighborhoods. [Doyle and Schwartz, Theorem 1.1 and Remark 3](https://arxiv.org/html/2510.12623v4#S1.SS2) · [Lander, Theorems 1–2 and Corollary 1](https://arxiv.org/html/2609.10703v1)

Doyle, Lander, Schwartz, and Trettel proved Type 3 universality using two planar families, explicit height directions, and inflation. Their §6 also reports that a second family with degree sequence $55666677$ passed exact universality checks. The second family has no face list in that section. Their companion script supplies the face list for Type 3. The published information leaves the identification of their second family with Type 4 or Type 6 unresolved. [Theorem 1.1](https://arxiv.org/html/2611.21909v1#S1.SS1) · [§6](https://arxiv.org/html/2611.21909v1#S6) · [Companion face list](https://github.com/FabianLander/universal-8-vertex-origami-torus-triangulation/blob/main/UniversalityProof.m#L18-L22)

## Contribution of the formalization

| Type | Prior result | Verified here |
| --- | --- | --- |
| 1 | Nonexistence by Lander's star collapse and Schwartz's seven-vertex bound | The collapse and a kernel-checked determinant-sign obstruction for this specific collapsed face complex |
| 2 | Lander's nonexistence conjecture | Nonexistence for the entire type. The geometric reduction and propositional refutation both replay in Lean |
| 3 | Universality theorem of Doyle, Lander, Schwartz, and Trettel | Their planar data and height vectors with a fixed-period length proof of inflation and a degree-one quotient proof |
| 4 | Numerical square evidence and the unresolved identity of the second universal family | Regular embeddings for every reduced modulus with $x<1/2$, including every rectangle |
| 5 | Numerical square evidence on this type and explicit square constructions with more vertices | Exact radical coordinates on the labeled Type 5 square torus and a uniform closed nonrectangular box |
| 6 | Numerical square evidence and the unresolved identity of the second universal family | A face-identified universal construction by flipping the Type 3 diagonal, with rank nine at the spatial embeddings |
| 7 | Near universality and a neighborhood of the square | The entire rectangular ray and verification of the full $x<1/2$ region with rank nine |

For the seven-vertex problem, Bokowski and Eggert had already classified the oriented matroids of the Möbius triangulation. Schwartz explains how their convex-hull result implies his hull lemma and supplies a separate argument that combines a hull lemma with spherical link lengths. [Bokowski and Eggert, Theorem 3.7](https://www.iri.upc.edu/people/ros/StructuralTopology/ST17/st17-10-a7-ocr.pdf) · [Schwartz, §1.2 and §2](https://arxiv.org/html/2507.14998v9#S1.SS2)

The determinant-sign method has a precedent in Schewe's use of rank-four chirotopes and SAT to obstruct polyhedral realizations of triangulated surfaces. The Type 2 argument adds flatness-specific strict support and mixed-side constraints from spherical links. The resulting Boolean refutation obstructs flat embeddings of a type that already has ordinary polyhedral embeddings. [Schewe, §2.4](https://arxiv.org/html/0801.2582#S2.SS4) · [Type 2 proof](Type2.md)

The conformal length variation used for Type 6 gives the standard Euclidean cotangent Hessian. The rank proof here combines those angle directions with two independent period directions and transfers them to the spatial embedding through its squared-length equations. [Bobenko, Pinkall, and Springborn, Proposition 4.1.6](https://arxiv.org/html/1005.2698#S4.SS1) · [Type 6 proof](Type6.md)

For related work in proof assistants, Boulay, Chai, Chang, and Moulin formalize planar Huzita folds and constructions in Lean 4. Their origami formalization addresses a different set of theorems from piecewise-isometric embeddings of flat tori. [A Lean Paper About Paper, 2026](https://arxiv.org/abs/2609.14912)

The literature check covered arXiv versions, author pages, journal records, and the numerical and verification repositories linked by the papers as of November 27, 2026. It found no earlier exact Type 2 obstruction, Type 5 radical construction on this face list, or full Type 7 rectangular coverage in those sources. Priority for the universal Type 6 construction and the overlap with the Type 4 strip remain qualified by the unnamed second family in the universality preprint.
