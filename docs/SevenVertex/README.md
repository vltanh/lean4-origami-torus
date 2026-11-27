# Seven-vertex nonexistence

Lean proves that an embedded simplicial torus with seven vertices has a cone
angle different from \(2\pi\). This is the nonexistence statement of
Schwartz's Theorem 1.1. The Lean statement uses an unordered set of triangles
on `Fin 7` and the injectivity of the affine evaluation on their glued
barycentric simplices. [Lean theorem](../../OrigamiTorus/SevenVertex/Nonexistence.lean) · [Schwartz, Theorem 1.1](https://arxiv.org/html/2507.14998v9#S1.SS1)

For a simplicial torus, Euler characteristic zero gives \(7-E+F=0\).
Counting edge incidences gives \(3F=2E\), so \(F=14\) and \(E=21\).
The formal statement takes fourteen distinct triangular faces and requires
each edge that occurs to belong to two faces. Lean also derives the
fourteen-face condition from the Euler relation. It counts the incidences to
show that all \(\binom{7}{2}=21\) pairs occur and uses a finite search to
prove that every such face set is a relabeling of the Möbius triangulation.
The search assigns the two incident triangles at each pair, pruning only
incompatible assignments. Lean proves that this enumerates every candidate
and checks that every output is a relabeling. [Classification](../../OrigamiTorus/SevenVertex/Classification.lean)

The geometric proof uses the strict-support and determinant-sign argument
already developed for Type 1. Lean checks that relabeling preserves the
affine evaluation and the sum of the incident angles at each vertex. It
then applies the obstruction to the Möbius face list. Schwartz's argument
uses a convex-hull case enumeration and spherical Crofton's formula.
[Type 1 geometry and certificate](../EightVertex/Type1.md) · [Schwartz, §2](https://arxiv.org/html/2507.14998v9#S2)
