# Type 5 embeds every nonhexagonal flat torus

**Every flat torus outside the hexagonal similarity class has a Type 5 piecewise-linear isometric embedding in three-space.** The off-ray theorem covers the reduced moduli with $0\le x<1/2$. The construction below covers the other nonhexagonal moduli, $x=1/2$ and $y>\sqrt3/2$. Rescaling both the source and the spatial coordinates gives the result at every scale. Type 5 universality is therefore equivalent to existence at the single modulus $(1+i\sqrt3)/2$. [Off-ray theorem](Type5FoldedModuli.md) · [Sharp-ray certificate](../../scripts/type5_rectangles/sharp_embeddings.py)

## The sharp-ray coordinates

Use periods $A=(1,0)$ and $B=(1/2,y)$ with the Type 5 square marking. Write $T=|B|^2$, $t=T-1=y^2-3/4>0$ and $u=t/(1+2t)$. In particular $0<u<1/2$. The pair $(X,D)$ in the table represents the physical point $(X,(D-X/2)/y)$, so $X=p\cdot A$ and $D=p\cdot B$. Set
\[
 s=-3/20,\qquad H=1/100,\qquad G=\frac{147}{62410}(1+u/4),
 \qquad b=u^2(H+2sG+9u/400),\qquad e=u^4/16384.
\]

| Vertex | $X$ | $D$ |
| --- | --- | --- |
| 1 | $0$ | $0$ |
| 2 | $s$ | $-T/2+e$ |
| 3 | $1/2-Gu^2$ | $b-s$ |
| 4 | $s-Hu^2$ | $T(1/2+s-u/10)$ |
| 5 | $u/36-1/2$ | $-T/2+3e$ |

Place vertices 1, 2 and 5 at their intrinsic coordinates in the horizontal plane. Take the **positive** root heights at both 3 and 4. For leaves 0, 6 and 7 take the quadratic-formula signs $+,-,+$, respectively, using the ordering of the linear equations in the reconstruction. Subtraction of the three anchor distance equations determines each root's horizontal projection. For each leaf, subtraction of its distance equation at 1 from those at its other four neighbors gives four linear equations in the two intrinsic and three spatial coordinates. The remaining norm equation restricts the resulting affine line to the two quadratic roots. This accounts for the nine core edges and the five incident edges at each of the three leaves. Equality of the three squared edge lengths of each triangle makes its affine map an isometry. [Radical reconstruction](../../scripts/type5_rectangles/chart.py) · [Derivation](Type5.md#the-coordinates)

Lean checks all 54 strict Voronoi inequalities for the nine core edges. Applying the sharp-core area theorem then gives strict area bounds for the anchor triangle and all three leaf polygons throughout $t>0$. [Lean core and area proof](../../OrigamiTorus/EightVertex/Type5/SharpFamily.lean)

## Verifying the embedding for all heights

The verifier reads the face orientations and the integer shifts from Lean. It checks positive radicands and nonzero divisors in the reconstruction, positive orientation of all 16 marked intrinsic triangles, and strict separation for every one of the 138 disjoint edge–face pairs. For each pair, the alternating four-point determinants give its affine dependence. After reversing the signs on the triangular face, two certified opposite signs exclude a common point. The incidence check reduces every excess triangle intersection to one of these pairs. The marked signed double areas sum to $2y$, so the positively oriented development has degree one and identifies the abstract surface with the prescribed lattice quotient. [Separation and quotient proofs](Type5Rectangles.md#from-signs-to-a-torus) · [Marked area identity](../../OrigamiTorus/EightVertex/Type5/Periodic.lean)

| Parameter range | Verified enclosure |
| --- | --- |
| $0<t\le 2^{-10}$ | Laurent series in $t$ with a bounded remainder |
| $2^{-10}\le t\le 2^{12}$ | 109 closed subintervals, using 448-bit Arb Taylor arithmetic of order 12 |
| $2^{12}\le t<\infty$ | Laurent series in $v=1/\sqrt{t}$ on $0<v\le1/64$, using $u=1/(2+v^2)$ and $y=\sqrt{1+3v^2/4}/v$ |

In each outer range, a sign is established after dividing by the leading power of the positive expansion variable and enclosing the normalized remainder on the whole range. The middle range starts with consecutive powers of two and bisects until each interval certifies. All shared endpoints are included. From a built checkout with python-flint installed, replay the three ranges together with the following command. [Taylor arithmetic](../../scripts/type5_rectangles/ball_taylor.py) · [Laurent arithmetic](../../scripts/type5_rectangles/laurent.py)

```sh
python -m scripts.type5_rectangles sharp-embeddings
```

At $t=0$ the table puts $p_2\cdot B=p_5\cdot B=-1/2$, and the spatial heights of both roots vanish. In fact their limiting projections coincide. Vertex 3 has projection $p_3-A$ and vertex 4 has projection $p_4-2(p_4\cdot B)B$. Both have dual coordinates $(-1/2,-s-1/2)$. Thus the limiting placement identifies vertices 3 and 4. At the endpoint the fixed-period test is an existential formula over the reals with rational coefficients. Its satisfiability would give universality, and its infeasibility would make the hexagonal class the unique exception. [Hexagonal fold with two crossings](Type5.md#a-hexagonal-fold-with-two-edgeface-crossings) · [Fixed-period test](Type5Regularity.md)
