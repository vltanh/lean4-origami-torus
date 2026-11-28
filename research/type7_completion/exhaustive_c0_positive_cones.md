# Convex reduction of the positive C0 mixed branches

The actual positive branch `[2345]>0` has a particularly small
necessary geometric model. Its reflected branch is `[4567]>0`.
This note proves the reduction to one precise endpoint inequality.
The [endpoint-bound companion](exhaustive_c0_endpoint_bound.md) now
proves that inequality and excludes both actual positive branches.
The algebraic checker here verifies the conditional reduction itself.

Use the regular ray-1 C0 notation from the
[turning theorem](exhaustive_c0_turning.md):

\[
\begin{gathered}
d_i=1/2-h_i\ge0,\quad\sum_i d_i=1/2,\quad d_1d_2d_6d_7>0,\\
L=d_1+d_2=|P_3|,\quad M=d_6+d_7=|P_6|,\quad
D=d_0+L+M,\\
E=P_3-P_2,\quad F=P_7-P_6,\quad
C_{ij}=\operatorname{cross}(P_i,P_j),\\
\ell_u=1-2u,\quad\ell_v=1-2v,\quad k=v-u,\\
Q_4=P_4-2uP_3-\ell_uP_6,\quad
Q_5=P_5-2vP_3-\ell_vP_6,\\
S=\ell_vQ_4-\ell_uQ_5,\qquad W=vQ_4-uQ_5.
\end{gathered}
\]

Here `P0=P1=0`, both cap areas `C23,C67` are positive, and
`P3=(L,0)`. The strict turn gives `cross(E,F)>0`. The exact metric
identities give

\[
|Q_4|=r=d_4+d_5+2uD.                         \tag{1}
\]

The [height-order bound](exhaustive_c0_height_order.md) already
implies `0<u<v<1/2` in either actual positive branch.

## 1. A strict cross product from three brackets

The companion exports one CNF proving all twelve generic consequences
listed in its `CONSEQUENCES` constant from the complete topology
formula, the regular cap units, the three strict turning signs, and
the positive generic sign of `[2345]`. Actual positivity fixes that
generic sign; every conclusion is retained as a weak actual sign.
Thus actual zeros remain covered.

In particular, `[2456]>=0` and `[3456]<=0`. Put
`A=cross(Q4,Q5)`. Direct determinant expansion gives

\[
\begin{aligned}
2[3456]&=-A,\\
2[2456]&=2\operatorname{cross}(E,W)-A,\\
2[2345]&=-\operatorname{cross}(E,S),\\
k\operatorname{cross}(E,Q_4)
 &=\ell_u A/2+\ell_u[2456]+2u[2345]>0.
\end{aligned}                                               \tag{2}
\]

The last strict inequality uses only `u>0`, `lu>0`, actual
`[2345]>0`, and the two weak conclusions. No angular branch or
nonzero assumption on `[2456]` or `[3456]` is needed.

## 2. The parallelogram, including its collapsed boundary

The same conditional signs give

\[
C_{34},C_{36},C_{46}\le0,\qquad
[0346]\ge0,\quad [1346]\le0.                 \tag{3}
\]

If `C36<0`, write `P4=a4 P3+b4 P6`. The determinant identities

\[
2[0346]=\operatorname{cross}(P_4-2uP_3,P_6),\qquad
2[1346]=-\operatorname{cross}(P_3,P_4-\ell_uP_6)
\]

show, together with (3), that

\[
0\le a_4\le2u,\qquad0\le b_4\le\ell_u.
\tag{4}
\]

Equivalently, `T=-Q4=a P3+b P6` with `0<=a<=2u` and
`0<=b<=lu`.

If `C36=0`, the conditional `C26<=0` and `C23>0` force
`P6=-(M/L)P3`; positive parallelism is impossible. The two opposite
signs on `C46` and `[0346]` force `P4` onto this same line.
Writing `P4=(x,0)`, the conditional signs `[0234]>=0` and
`[1246]<=0` give

\[
-\ell_u M\le x\le2uL.                       \tag{5}
\]

This is exactly the image of the closed parallelogram (4).
Thus no division by `C36` loses the collinear boundary.

Since `P3` and `P6` are never positively parallel, every point of
this parallelogram has norm strictly less than `2uL+lu M` after
the translation defining `T`. Equations (1), (4), and (5) imply

\[
(1-4u)M>d_4+d_5+2u d_0,\qquad u<1/4.         \tag{6}
\]

The strictness follows by maximizing the convex norm on the four
vertices: each endpoint has norm below the sum of the two positive
edge lengths, and the opposite corner has a strict triangle
inequality. This remains true when `P3` and `P6` are antiparallel.

## 3. Reduction to a single endpoint inequality

Let `c=cross(E,P6)`. The conditional sign `[0236]>=0` gives
`c>=0`. In fact `c>0` when `C36<0`: otherwise `P6` is a negative
multiple of `E`, since `E` has positive second coordinate and
`P6` has negative second coordinate. Then
`cross(P6,F)<0` by the strict turning sign, contradicting `C67>0`.

Consider the endpoint inequality

\[
D\operatorname{cross}(E,P_6)+h_2 C_{36}\ge0.
\tag{7}
\]

For `C36<0`, this is `R<=D`, where
`R=h2*(-C36)/c`. Under (7), the positive branch is impossible.
Indeed, (2) and `T=a P3+b P6` give

\[
0<-\operatorname{cross}(E,T)=aC_{23}-bc.
\]

Hence `a>0` and `theta=bc/(a C23)` lies in `[0,1)`. The
zero-safe vector identity

\[
C_{36}E=cP_3+C_{23}P_6
\]

then yields

\[
T=a\left((1-\theta)P_3+\theta\frac{C_{36}}{c}E\right),
\qquad
|T|\le a((1-\theta)L+\theta R)<2uD.            \tag{8}
\]

Here `a<=2u`, `L<D` since `M>0`, and the coefficient of `L`
is strictly positive. Equation (8) contradicts (1).

The boundary `C36=0` already closes without (7): (2) says that
`Q4` points along the negative first axis, while the lower bound
in (5) gives `|Q4|<=2uL<2uD`, again contradicting (1).

The [endpoint-bound companion](exhaustive_c0_endpoint_bound.md) proves
(7), with a strict sign, for the nonparallel endpoint configuration.
Together the two arguments exclude the actual positive branch.

## 4. Checked marked reflection

The relabeling `p(i)=1-i mod8`, followed by an axis reversal and
one transverse reflection, has positive three-dimensional
orientation and sends

\[
(u,v)\longmapsto(1/2-v,1/2-u),\quad
d_i\longmapsto d_{-i},\quad
[2345]\longmapsto[4567].                     \tag{9}
\]

Both new cap areas stay positive. The companion verifies the marked
cocycle gauges for both markings, the horizontal edge weights, the
exact height chart, and `Q4_new=R Q5_old` for the transverse
reflection `R`. Consequently every argument above transfers to the
actual `[4567]>0` branch. In particular, (6) becomes

\[
(4v-1)L>d_3+d_4+(1-2v)d_0,\qquad v>1/4.
\]

## Reproduction

```sh
python research/type7_completion/exhaustive_c0_positive_cones.py /tmp/c0-positive-cones
python research/type7_completion/solver_cnf_certificates.py /tmp/c0-positive-cones-rup \
  --checker /tmp/type7-rup-check /tmp/c0-positive-cones
```

The source checker verifies ten determinant identities, the planar
basis identity, and the marked reflection. The exported CNF must be
independently accepted before using its conditional signs.
