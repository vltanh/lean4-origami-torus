# Two collinear stretched caps cannot have exactly one collapsed edge

Consider an unbounded ray-3 sequence whose physical cap limits lie on
one common line. Suppose a transverse blow-up has two collinear caps on
different lines, and exactly one of the eight limiting physical short
weights is zero. This is impossible, with no restriction on the relative
rates of the edge collapse, transverse width, and `t=1/y²`.

This is an asymptotic research exclusion. It supplies no numerical
height threshold and is not a Lean theorem.

## 1. Complete finite reduction

The 5,476-order classification in `common_line_edge_collapse.py` leaves
624 zero-stress pairs when physical lengths use the seminorm `|dX|`.
Exactly sixteen have only one zero short weight. The accompanying
checker maps every one, using a checked phase symmetry and a single
common horizontal reflection, to

\[
 A=(0,0),(r,0),(r,0),(1/2,0),\qquad
 B=(0,0),(u,u),(v,v),(-w,-w),
\]

where the cyclic labels are `A=(0,1,4,5)`, `B=(2,3,6,7)` and

\[
 0<r<1/2,\qquad 0<u<v<1/2,\qquad w=1/2-v>0.
\]

The physical common-line coordinate is X. A shear of the stretched
normal coordinate makes A horizontal; a nonzero scaling makes B have
slope one. These operations preserve the physical limiting seminorm.
The two limiting ring perimeters give the displayed lengths `1/2`.
The collapsed edge is 14. All other physical short weights are positive.

The only nonzero point brackets in this picture have two vertices from
each cap. Their signs depend only on the displayed weak orders. With
those signs fixed, the necessary orientation and linking formula forces

\[
 [0124]\ge0,\qquad [1234]\ge0,\qquad
 [1247]\le0,\qquad [0145]\ge0.                  \tag{1}
\]

The checker allows either common orientation and fixes no zero limiting
bracket. Its CNF asks whether at least one required sign fails; independent
UNSAT replay certifies all four implications.

## 2. The signs determine the collapsed edge's scale and direction

Let `b=r4-r1`, `beta=h14>0`, and let delta be the vanishing normal width
used for the blow-up. Normalize its transverse coordinates by

\[
 m=\max(|\Delta X|,|\Delta Y|/\delta).
\]

The relative short-edge bounds give `m>=c beta` and a normalized axial
increment `O(t beta/m)`. A finite shear of the stretched normal
coordinate does not change these assertions. Pass to a subsequence
whose normalized transverse direction tends to `(b_x,b_y)`, with
maximum absolute coordinate one. The direction is nonzero and its
normalized axial component tends to zero.

Each of the first three brackets in (1) contains edge 14. Factor that
edge as an exact determinant row before passing to the limit. Apart
from the one positive common scale, the three limiting linear forms are

\[
 -r b_y,\qquad -u(b_x-b_y),\qquad -w(b_x-b_y).
\]

The first two must be nonnegative and the third nonpositive. Since
`r,u,w>0`, this implies `b_x=b_y<0`. The physical metric then gives

\[
 \Delta X/\beta\to-1,\qquad
 \Delta Y/(\delta\beta)\to-1.
\]

In particular the edge's stretched scale is comparable to beta. This
comparison follows from the signs, even when beta is arbitrarily small
relative to delta or t.

## 3. The metric forces a negative moving-frame height

Use the actual moving frame

```
0=(0,0,0), 2=(0,0,1), 5=(1,0,0), 3=(0,1,1).
```

Its transverse basis tends to `(1/2,0),(u,u)` and has positive
determinant. It is uniformly conditioned after the normal stretch. Write
vertex 1 as `a=(a_x,a_y,a_z)` and retain b for edge 14 in this frame.
The preceding direction conclusion yields

\[
 a_x\to2r,\quad a_y\to0,\quad
 b_x/\beta\to0,\quad b_y/\beta\to-1/u,
 \quad b_z=O(t\beta).                            \tag{2}
\]

The last bound follows from the relative axial bound for the actual
edge and the bounded transverse coefficients divided by beta.

To compute the height, use the face-023 chart with axial coordinate
`H_i=c_i-2t*zeta_i`. Its limiting transverse U coordinate is the negative
of the displayed physical X coordinate, plus `x2` on cap B. The sixteen
cross stresses and eight horizontal weights form a `24×14` affine
system of rank fourteen. Its unique intrinsic solution is

\[
\begin{aligned}
x={}&(0,-r,-r+v,-r-u+v,1/2-r,0,1/2-r,-r),\\
\gamma={}&(0,r/2,r/2+v/2-1/8,r/2-u/2+v/2-1/8,\\
&\hspace{18mm}r/2,1/4,r/2-1/8,r/2+1/8).
\end{aligned}
\]

The fourteen non-anchor cross-edge equations have rank five in the
five free zeta coordinates. Their unique solution is

\[
 (\zeta_1,\zeta_4,\zeta_5,\zeta_6,\zeta_7)
 =(r/2,r/2,2r-3/4,r/2-1/8,r/2+1/8).
\]

Both full ranks and all substitutions are checked symbolically. Thus
these are necessary limits, not a selected planar branch.

In the moving frame, the axial coordinate of a point with transverse
coefficients E,F is

\[
 \frac{H_i-EH_5-F(H_3-H_2)}{H_2}.
\]

For vertex 1, `E->2r`, `F->0`, and `H2->1`. Consequently

\[
 \frac{a_z}{t}\to-2\zeta_1+4r\zeta_5
 =4r(2r-1)<0.                                  \tag{3}
\]

Every coefficient being multiplied by t is bounded, so this passage
requires convergence only, with no rate relative to t.

## 4. The same-cap volume has the prohibited sign

The exact moving-frame identity is

\[
 [0145]=a_yb_z-a_zb_y.
\]

Using (2) and (3),

\[
 \frac{[0145]}{t\beta}\to \frac{4r(2r-1)}{u}<0.
\]

This contradicts the final necessary sign in (1), excluding all sixteen
orders. The other 608 zero-stress two-line orders have at least two zero
short weights; this theorem makes no claim about them.

## Reproduction

```sh
python3 research/type7_completion/remaining_two_line_blowup.py /tmp/type7-two-line-blowup
g++ -O3 -std=c++17 research/orientation_checkpoint/check_unsat.cpp -o /tmp/type7-sign-check
/tmp/type7-sign-check < /tmp/type7-two-line-blowup/two_line_required_signs.cnf
/tmp/type7-sign-check < /tmp/type7-two-line-blowup/two_line_model_coverage.cnf
```

Require explicit `UNSAT nodes ...` output. The coverage CNF is the same
complete 1,888-model formula already checked for the chamber compiler.
