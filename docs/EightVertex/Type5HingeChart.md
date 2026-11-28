# Two quadratic completions at the hexagon

If the hexagonal torus has a Type 5 embedding, it has one specified by eight rational numbers and two independent quadratic equations. Six of the eight vertices have rational coordinates in the scaled model below. The full intrinsic placement and the scaled spatial placement lie in a common number field of degree at most four over the rationals. Exact examples in eleven of the twelve candidate clique classes satisfy all the edge equations. Each still has crossings. [Reconstruction and checker](../../scripts/type5_rectangles/hex_hinge.py) · [Witness data](../../scripts/type5_rectangles/hex_hinge_witnesses.json)

## Place the faces on edge 16

First use ordinary Cartesian lengths. Translate vertex 1 to the origin and place the anchor face in the horizontal plane, with $r_j=(p_j,0)$ at vertices $j=2,5$. Write $p_6=\varepsilon e$ and $r_6=\varepsilon w$, where $\varepsilon>0$ and $e,w$ are unit vectors in the plane and space respectively. The marked shifts from 2 and 5 to 6 both equal $-B$ with $B=(1/2,\sqrt3/2)$. The two edge equations give the same line constraint on the anchors,
\[
 N=B+\varepsilon(w_{xy}-e),\qquad
 p_j\cdot N=\varepsilon B\cdot e-|B|^2/2.
\]
If $N=0$, the spatial horizontal projection of $r_6$ equals $p_6-B$. Its norm is at most $|r_6|=|p_6|$, contradicting strict shortestness on edge 16. Thus the line has one free parameter per anchor. [Anchor equations and marked shifts](../../OrigamiTorus/EightVertex/Type5/HingeChart.lean)

The faces 136 and 164 are coherent in the marking based at vertex 1. Let $f$ be the positive unit perpendicular to $e$. For each root $i=3,4$, choose a unit vector $n_i\perp w$. The face isometry sends $e,f$ to $w,n_i$. In these bases the same pair $x_i$ represents the intrinsic and spatial root. Let $U$ be this isometry, write $a=r_2$, $b=r_5$, and express $s=p_2-K_{2i}$ and $t=p_5-K_{5i}$ in the basis $e,f$. The two remaining root equations are linear,
\[
 (U^Ta-s)\cdot x_i=h,\qquad (U^Tb-t)\cdot x_i=k,\qquad
 h=(|a|^2-|s|^2)/2,\quad k=(|b|^2-|t|^2)/2.
\]
Both shifts are nonzero and they differ. Applied to edges 12, 15 and 25, strict shortestness gives $h,k<0$ and $|a-b|<|s-t|$. If the rows at a solution were dependent, taking $k$ times the first row minus $h$ times the second would give $U^T(ka-hb)=ks-ht$. But direct expansion gives
\[
 |ks-ht|^2-|ka-hb|^2=hk\bigl(|s-t|^2-|a-b|^2\bigr)>0,
\]
contradicting the contraction property of $U^T$. Each root position is therefore a rational function of the specified data. Lean proves nonsingularity at every solution satisfying the strict comparisons and verifies the recovered distances. [Root reconstruction](../../OrigamiTorus/EightVertex/Type5/HingeChart.lean)

## Rational coordinates and the last two vertices

Store the physical point $(x,\sqrt3 y,z)$ as $(x,y,z)$. The metric on triples is $\operatorname{diag}(1,3,1)$ and $B=(1/2,1/2)$ in scaled planar coordinates. A rational chart for $e$ is
\[
 (c(t),d(t))=\left(\frac{1-3t^2}{1+3t^2},\frac{2t}{1+3t^2}\right).
\]
A rational multiple of the positive quarter-turn is $J(x,y)=(-3y,x)$, of length $\sqrt3$ on unit vectors. The spatial unit sphere is parametrized by $w=((2-D)/D,2u/D,2v/D)$ with $D=1+3u^2+v^2$. Reflection in the line through $(1,0,0)+w$ takes the first coordinate vector to $w$. Let $F,H$ be the reflected second and third coordinate vectors. The two separately chosen scaled perpendiculars $c(t_i)F+3d(t_i)H$ have length $\sqrt3$ and are paired with $Je$. These formulas use eight scalars in total: $\varepsilon$, the three parameters for $e,w$, the two circle parameters for the face planes and the two anchor positions along their line.

For each remaining vertex $j=0,7$, subtract its distance equation at 1 from the equations at $i=2,5,3,4$. With $s_i=p_i-K_{ij}$ they become
\[
 r_i\cdot r_j-s_i\cdot p_j=(|r_i|^2-|s_i|^2)/2.
\]
They cut out an affine line in the five coordinates $(r_j,p_j)$ at a regular completion. The equation $|r_j|^2=|p_j|^2$ determines a point on that line by a quadratic equation. There is no edge between 0 and 7, so both equations have coefficients in the same rational field as the first six vertices.

Any hypothetical embedding can be perturbed at the fixed hexagonal periods so that all five-cycle weights are positive and all 70 spatial tetrahedron signs are strict. At a positive leaf the five null vectors to its neighbors have invertible Gram matrix. The five distance equations consequently have independent derivatives in its five coordinates. Subtraction gives four independent affine rows and the remaining norm equation has a simple root on the line. Each chosen root therefore continues under small perturbations of the eight hinge parameters. The circle and sphere charts cover dense subsets of their direction spaces, and the strict signs defining an embedding remain valid on a neighborhood. Rational parameters occur in that neighborhood. Conversely, verifying the edge lengths, oriented intrinsic faces and spatial separation gives an embedding by the marked area and simplex-intersection arguments. Thus a successful rational input would settle Type 5 universality. Returning to ordinary Cartesian coordinates requires at most one further square root, $\sqrt3$. [Fixed-period regularity](Type5Regularity.md) · [Quotient and separation](Type5Rectangles.md#from-signs-to-a-torus)

## Exact hexagonal examples

Run the following command from a built checkout with python-flint installed.

```sh
python -m scripts.type5_rectangles hex-hinge
```

For each stored input the checker verifies all 24 squared-length equations, positive orientation on all 16 faces, strict Voronoi comparisons on every edge and all 70 determinant signs. It counts the transverse disjoint edge–face crossings by the signed dependence on their five vertices. All comparisons use rational arithmetic and the sign of $a+b\sqrt d+c\sqrt e+f\sqrt{de}$, computed by at most two squared-norm comparisons. The recorded class and failed signs are checked after canonical relabeling.

For class `f87` the 23 clique determinants and five of the six additional separation determinants have the required signs. The exception is quartet 2367, the fold along edge 23. The examples in the other ten represented classes also fail at least one separation sign. The data contain no example in class `2e051`. Feasibility of a complete class at the hexagon remains open. [The twelve complete tests](Type5HexagonalAngles.md#twelve-feasibility-tests-in-intrinsic-coordinates)
