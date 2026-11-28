# Type 5 realizes every rectangular flat torus

For periods \(A=(1,0)\) and \(B=(x,y)\), the labeled Type 5 triangulation admits an embedded, facewise-isometric realization in \(\mathbb R^3\) on each of the following sets.

| Moduli | Certified range |
| --- | --- |
| Uniform strip about the rectangular ray | \(y\ge1,\quad \lvert x\rvert\le 2^{-120}\) |
| Wider strip in the cusp | \(y\ge32,\quad \lvert x\rvert\le 1/4096\) |
| Two additional closed boxes | Centers \((12/25,22/25)\) and \((7/16,1)\), with coordinate radii \(2^{-80}\) and \(2^{-52}\), respectively |

Every rectangular lattice has orthogonal generators. Rotating the shorter generator to the horizontal axis and dividing lengths by its length gives \(x=0,\ y\ge1\). Applying the inverse similarity to the intrinsic and spatial triangles gives the claim at the original scale. General Type 5 universality, including existence at the hexagonal endpoint, remains open.

## Core coordinates

Put \(t=1/y\), \(U=1/\lVert B\rVert^2\), and define
\[
Q=-b+2bdU-kU^2,\qquad P=Q+\tfrac12-\ell U^2,\qquad h=\tfrac12-e_3 U^5.
\]
Take \(p_1=0\). The following two projections determine each of the other four core vertices uniquely since \(y>0\).

| Vertex \(i\) | \(p_i\cdot A\) | \(p_i\cdot B\) |
| --- | --- | --- |
| 2 | \(P\) | \((-1/2+e_2U^6)\lVert B\rVert^2\) |
| 3 | \(h\) | \(b\) |
| 4 | \(C\) | \(\alpha \lVert B\rVert^2+\beta\) |
| 5 | \(Q\) | \(-\lVert B\rVert^2/2+d\) |

For \(0<t\le1/32\), take
\[
(b,d,k,\ell,C,\alpha,\beta,e_2,e_3)=
(3/32,15/64,3/256,1/65,-11/89,7/32,1/16,2^{-17},2^{-16}).
\]
For \(1/32\le t\le1\), take \(\beta=0, e_2=2^{-19}, e_3=2^{-18}\). Interpolate the other six parameters linearly in \(t\) between the rows below. The entries in the last six columns have common denominator \(10^6\). The two formulas give independent witnesses at \(t=1/32\).

| \(64t\) | \(b\) | \(d\) | \(k\) | \(\ell\) | \(C\) | \(\alpha\) |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 2 | 95875 | 232607 | 12172 | 16044 | −126775 | 219823 |
| 6 | 95973 | 233296 | 11928 | 15988 | −126698 | 221061 |
| 17 | 96417 | 240903 | 10566 | 16400 | −125395 | 235007 |
| 33 | 99033 | 266339 | 7106 | 17623 | −122513 | 277804 |
| 49 | 107926 | 301670 | 3394 | 18325 | −121085 | 339931 |
| 62 | 121403 | 291750 | 1336 | 13150 | −122116 | 375977 |
| 64 | 122993 | 285185 | 1146 | 11945 | −121602 | 379005 |

Use the integral marking of the square construction, with shift \((m,n)\) interpreted as \(mA+nB\). Place anchors 1, 2 and 5 at height zero. Solve for roots 3 and 4 using the positive and negative heights respectively. For leaves 0, 6 and 7 take the quadratic-formula signs \(+,-,+\). Subtracting the distance-to-origin equation from each other distance equation gives the four linear equations used in each leaf reconstruction. The remaining norm equation gives its quadratic. The marking and edge list ensure that these are all 24 edge equations. The checker establishes positive radicands and nonzero denominators on every parameter cell. The two additional boxes use the same reconstruction with their own rational cores. [Reconstruction derivation](Type5.md#the-coordinates) · [Core and reconstruction code](../../scripts/type5_rectangles/chart.py) · [Oblique box cores](../../scripts/type5_rectangles/__main__.py)

## From signs to a torus

The 16 marked intrinsic faces have positive signed areas. Their oriented double areas sum to \(2y\) because the same sum in lattice coordinates is 2 for *every* choice of vertex positions. Gluing the faces gives a locally open map to the lattice quotient. Its degree is one by the area sum, with every preimage of a regular value contributing positively. Compactness and local openness then give a homeomorphism. [Area identity and face gluing](../../OrigamiTorus/EightVertex/Type5/Periodic.lean) · [Quotient argument](Type5.md#the-geometric-conclusion)

For each of the 138 disjoint edge–face pairs, sort the five labels as \(q_0,\ldots,q_4\). Take the five alternating maximal minors of the matrix with columns \((1,r_{q_i})\), multiplying by \(-1\) on the face. The check requires at least one strictly positive and one strictly negative result. A nonzero minor gives rank four, so before the face signs are applied the alternating minors span the affine dependences. A common point of the edge and triangular face would give a dependence whose coefficients are nonnegative on the edge and nonpositive on the face. The two strict signs exclude both orientations of that dependence. Unresolved minors can be discarded in this test.

If two triangles intersect beyond a shared subface, subtract the common mass in their barycentric coordinates and renormalize. This gives equal convex combinations with disjoint supports. If all six coefficients are positive, the two separate sum conditions and three coordinate conditions give at most five independent linear equations. Vary the coefficients along a nonzero null vector until one reaches zero. The resulting disjoint supports have at most five labels in total. The checker verifies from the face list that every such pair of disjoint subfaces extends to a disjoint edge–face pair. Positive intrinsic face areas and the edge equations also make every spatial face nondegenerate. The spatial simplicial map is therefore injective and hence an embedding by compactness. Its corresponding triangles are congruent, giving the intrinsic metric.

## Checking the inequalities

On the compact band, the verifier subdivides each interval \([i/64,(i+1)/64]\) and writes \(t\) as an affine function of \(z\in[-1,1]\). Every intermediate expression has the form \(\sum_{j<n} c_j z^j+z^n R_n\), with interval enclosures for all coefficients and the remainder. Substituting the expansions into a product gives its remainder by convolution. Division follows from multiplication by the denominator. For a square root \(g^2=f\), the remainder equation for order \(j\ge1\) divides by \(g+g(0)\), bounded strictly above zero. The shear ranges over the whole closed interval in every subdivision. All endpoints and subsequent arithmetic are outward rounded to dyadics with denominator \(2^{256}\). The compact band takes 296 certified intervals. [Taylor arithmetic](../../scripts/type5_rectangles/taylor.py) · [Interval endpoints](../../scripts/type5_rectangles/interval.py)

In the cusp, face areas, volumes and radicands may tend to zero as \(t\to0^+\). For each expression the verifier factors out a power of \(t\), keeping exact coefficients in the shear variable \(x\). For order \(j\), it encloses the normalized remainder
\[
T_j(f)=t^{-j}\Bigl(f-\sum_{i<j}f_i t^i\Bigr).
\]
All operations propagate this identity for \(0<t\le1/32\). For example, if \(g\) has leading order \(k\) and \(h=f/g\) has lower order \(n\), then
\[
 T_j(h)=\frac{T_{j+k}(f)-\sum_{i=n}^{j-1} h_i T_{j+k-i}(g)}{T_k(g)}.
\]
Division checks that the whole denominator enclosure excludes zero. Square roots use the positive branch and the analogous recurrence from \(g^2=f\). These are finite remainder identities, so the sign conclusions require no numerical extrapolation or assumption about the convergence radius of an infinite series.

The leading coefficients are rational functions of \(x\) with successive positive square roots. Exact zero coefficients must be distinguished from functions that happen to vanish at a chosen shear. The checker tests identities in the ordered field of germs at the midpoint of each shear cell, extending the rational function field by the specified positive roots. A zero germ vanishes on the full cell by real analyticity. Every inverse and square root checks its domain over the full interval. The eight closed shear cells have endpoints \(j/16384\) for \(-4\le j\le4\). [Laurent remainder arithmetic](../../scripts/type5_rectangles/laurent.py) · [Algebraic coefficients](../../scripts/type5_rectangles/shear.py)

## Replay

From the repository root, with its Lean toolchain, built project, Python 3.10 or later and the Python package `python-flint` (tested with 0.9.0), run

```sh
python3 -m scripts.type5_rectangles
```

The arguments `finite`, `cusp` and `oblique` replay the three checks above separately. The default also runs the equal-length arc check (`rhombic`), the nonplanar core check (`reduced`), the global embedding certificate (`separation`), the sharp-ray folds (`sharp`), the fixed-modulus general-position certificate (`generic`) the sharp-ray core area bounds (`core-bounds`), the one-edge deformation (`opening`), the local obstruction (`height-cones`) and the open sharp ray (`sharp-embeddings`). The global check uses `python-flint` and CaDiCaL from the Lean toolchain. [Equal-length construction](Type5Rhombic.md) · [Global embedding proof](Type5FoldedModuli.md)

The verifier reads the labeled faces and signed shifts directly from Lean. These region certificates are computer-assisted proofs checked in Python. The square and the original near-square box also have Lean kernel proofs. [Lean input export](../../scripts/type5_rectangles/Inputs.lean) · [Lean near-square theorem](../../OrigamiTorus/EightVertex/Type5/ContinuationTorus.lean)
