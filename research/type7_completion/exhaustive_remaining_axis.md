# A uniform bounded chart for markings 1 and 2

This is an exact necessary-system reduction for every **$y\ge32$**.  It
does not exclude either marking.  Unlike the local tetrahedron tests, it
uses one actual long edge and two actual faces to bound all eight spatial
vertices transverse to a common axis.  Six bounded product variables
retain every potentially nonzero small-vertical-product divided by
$t=1/y^2$.

The companion `exhaustive_remaining_axis.py` verifies both cocycles, all
eight cyclic rotations of each, the cancellation identities, and every
numerical bound below using exact integer/rational arithmetic.  It can
emit two complete necessary SMT systems.  They have 38 bounded real
variables, 24 quadratic edge equations, six quadratic product equations,
and direct affine minors of degree at most three.  All original shortest
lift, oriented area, nonedge contraction, weak generic sign, linking,
and actual affine circuit conditions remain.  No seven-mask assumption
is needed for this chart.

## 1. Fixing a uniformly long axis

Write the intrinsic edge vector as

\[
 (X_{ij},yV_{ij}),\qquad
 X_{ij}=x_j-x_i+m_{ij}+n_{ij}/2,\quad
 V_{ij}=v_j-v_i+n_{ij},\quad x_0=v_0=0.
\]

The shortest-lift inequalities give

\[
 |X_{ij}|<\tfrac12,\qquad |V_{ij}|<\tfrac12+t/8.
 \tag{1}
\]

For both markings the eight cyclic step-one vertical increments have
sum one.  Some increment is at least $1/8$.  Every cyclic rotation
$p(i)=i+r\pmod8$ preserves the oriented faces and each marked cocycle
up to an integral vertex gauge:

\[
 K_{p(i),p(j)}-K_{ij}=g_j-g_i.
 \tag{2}
\]

The checker constructs all 16 gauge tables and checks (2) on every edge.
After replacing the lifts by

\[
 x'_i=x_{p(i)}-x_{p(0)}+g_i^{(1)}+g_i^{(2)}/2,
 \qquad v'_i=v_{p(i)}-v_{p(0)}+g_i^{(2)},
\]

the marking is unchanged and $v_1=b_0\ge1/8$.  This is a symmetry of
each fixed marking, rather than only a symmetry of the Boolean topology.

Put the actual edge (01) on the unit spatial axis $N$:

\[
 r_0=0,\quad r_1=L N,\quad
 r_i=P_i+y\zeta_i N,\quad P_i\perp N,\quad
 \ell=L/y=\sqrt{v_1^2+t x_1^2}.
\]

The face (013) is nondegenerate, so a transverse rotation makes
$P_3=(p_{3u},0)$, $p_{3u}>0$.  A reflection, when necessary, makes
$[0123]>0$, equivalently $p_{2v}<0$.  These choices do not restrict
the existence of an embedding.

## 2. Four common neighbors are uniformly bounded

The vertices $i\in\{2,3,6,7\}$ are adjacent to both 0 and 1.  Their
edges to these anchors have zero vertical cocycle, and $K_{0i}=0$.
Set $A_i=x_i^2+x_1^2-X_{1i}^2$.  Exact polarization gives

\[
 \zeta_i=\frac{v_1v_i+tA_i/2}{\ell}=v_i+t\rho_i,
 \tag{3}
\]

\[
 |P_i|^2=x_i^2+
 \frac{x_1^2v_i^2-v_1v_iA_i-tA_i^2/4}{\ell^2}.
 \tag{4}
\]

For $y\ge8$, use $S=257/512$, so $|v_i|<S$,
$|A_i|<1/2$, $\ell\ge v_1\ge1/8$.  Then

\[
 |\rho_i|<8S+2<7,\qquad
 |P_i|^2<\tfrac14+16S^2+4S<9.
 \tag{5}
\]

Also $\zeta_1=v_1+t\rho_1$ with $0\le\rho_1\le1$.
These estimates divide only by the chosen long axis; no other edge
has a positive lower bound.

## 3. A second long edge and two reflected vertices

Both markings have $n_{36}=1$.  Put $d=v_6-v_3$ and
$\Delta\rho=\rho_6-\rho_3$.  The edge (36) equation is exactly

\[
 2d+1=t\bigl(|P_6-P_3|^2-X_{36}^2
                 +2d\Delta\rho+t(\Delta\rho)^2\bigr).
 \tag{6}
\]

Consequently

\[
 v_6=v_3-\tfrac12+t w,\qquad |w|<34.
 \tag{7}
\]

For example the absolute bound from (5) is

\[
 |w|<\tfrac12\bigl(36+\tfrac14+4S\cdot14+196/64\bigr)<34.
\]

For $y\ge32$, both the intrinsic and the actual axial lengths of
edge (36) have absolute value greater than $7y/16$:

\[
 V_{36}=\tfrac12+t w>7/16,\qquad
 \zeta_6-\zeta_3=-\tfrac12+t(w+\Delta\rho)<-7/16.
 \tag{8}
\]

The triangles **346 and 356 are actual faces**.  For either $k=4$
or $k=5$, the distance from $r_k$ to the actual line (36) is

\[
 \frac{y|X_{3k}V_{36}-X_{36}V_{3k}|}{L_{36}}
 <\tfrac12+\frac{S/2}{7/16}<9/8.
 \tag{9}
\]

The projection length along that line is at most the length of edge
$3k$, hence at most $17y/32$.  Its unit direction has transverse
component of norm at most $96/(7y)$, by (5) and (8).  Thus

\[
 |P_k|<3+\tfrac{17}{32}\tfrac{96}{7}+\tfrac98
          =\tfrac{639}{56}<12.
 \tag{10}
\]

The axial baselines are reflected:

\[
 \zeta_4=2v_3-v_4+t\rho_4,\qquad
 \zeta_5=2v_3-v_5-1+t\rho_5.
 \tag{11}
\]

Here is a uniform bound, including the perpendicular component of each
face.  Write $D=\zeta_6-\zeta_3$, $V=V_{36}$, $X=X_{36}$, and
$R=2w+\Delta\rho$, so $D=-V+tR$ and $|R|<82$.  The axial
coordinate of the parallel projection, after adding $V_{3k}$, is
exactly

\[
 t\frac{V_{3k}VR+X_{3k}XD+V_{3k}X^2}{V^2+tX^2}.
 \tag{12}
\]

The perpendicular contribution to $\zeta_k$ is at most
$(9/8)(96/7)t=108t/7$.  Use

\[
 |V_{3k}|<257/512,\quad |V|<273/512,\quad |D|<35/64,
 \quad V^2+tX^2>49/256.
\]

Adding $|\rho_3|<7$, (12) gives

\[
 |\rho_4|,|\rho_5|<\frac{3473657}{25088}<144.
 \tag{13}
\]

Equations (3), (7), and (11) prove the global boundedness claim.

## 4. Keep all six product scales

Let $v^0$ equal $v$ except that $v^0_6=v_3-1/2$, and put

\[
 z=(0,v_1,v_2,v_3,2v_3-v_4,2v_3-v_5-1,v_3-1/2,v_7).
\]

Write $v^{\rm actual}=v^0+t\omega$, where only
$\omega_6=w$ is nonzero, and $\zeta=z+tH$.  Thus
$H_6=w+\rho_6$, all other $H_i=\rho_i$, and $H_0=0$.
Every $P_i$, $H_i$, $w$, $x_i$, and $v_i^0$ is bounded.

For $V^0_{ij}=v^0_j-v^0_i+n_{ij}$, the difference
$(z_j-z_i)^2-(V^0_{ij})^2$ vanishes identically on 18 edges.  On
the remaining six introduce $q_{ij}$ through these exact equations:

| Edge | $tq_{ij}$ |
|---|---|
| 05 | $(2v_3-1)(2v_3-2v_5-1)$ |
| 14 | $-4(v_1-v_3)(v_3-v_4)$ |
| 24 | $-4(v_2-v_3)(v_3-v_4)$ |
| 25 | $-4(v_2-v_3)(v_3-v_5-1)$ |
| 47 | $(2v_3-2v_4+1)(2v_3-2v_7-1)$ |
| 57 | $(2v_3-2v_5-1)(2v_3-2v_7-1)$ |

Set $q_{ij}=0$ on every other edge.  The 24 original edge equations
are exactly equivalent, using these product identities, to

\[
\begin{split}
0={}&|P_j-P_i|^2-X_{ij}^2+q_{ij}
 +2(z_j-z_i)(H_j-H_i)\\
 &-2V^0_{ij}(\omega_j-\omega_i)
 +t\bigl((H_j-H_i)^2-(\omega_j-\omega_i)^2\bigr).
\end{split}
\tag{14}
\]

For fixed $t>0$, every equation in (14), and every product identity,
has degree at most two.  None of the six product edges contains vertex
6, so its $\omega$ difference vanishes.  Since
$|z_i|<257/256$ and $|H_i|<144$, (14) gives the explicit bound

\[
 |q_{ij}|<24^2+\tfrac14
      +2\tfrac{257}{128}\,288+\frac{288^2}{1024}
      =\frac{7255}{4}<2048.
 \tag{15}
\]

In particular it is legitimate to pass to a common convergent
subsequence of all these bounded variables as $t\to0$.  The six
$q_{ij}$ remain independent limit variables subject to (14).  They
must **not** be set to zero merely because both factors in their
defining product tend to zero.

## 5. Consequence for the two-block mask 04

In the asymptotic mask 04,
$v_1,v_2,v_3,v_4\to1/2$ and $v_5,v_6,v_7\to0$.  The product
identities prove two useful individual rates:

\[
 tq_{25}=4b_2(v_3-v_5-1),\qquad
 tq_{47}=(2v_3-2v_4+1)(-2b_6-2tw).
\]

Their respective nonvanishing factors tend to $-1/2$ and (1),
so $b_2,b_6=O(t)$.  This conclusion uses no comparison between the
other small increments.  Products such as $b_1b_3/t$ and $b_5b_7/t$
can still have nonzero limits.  In particular a cap tetrahedron cannot
be replaced by its zero-product Gram matrix without a further argument.

## 6. Replaying and using the reduction

```sh
python research/type7_completion/exhaustive_remaining_axis.py
python research/type7_completion/exhaustive_remaining_axis.py /tmp/type7-axis --y 32
```

The second command writes the checked rotation tables, two complete
queries, and their metadata.  The transverse variables have Euclidean
norm less than 12; the six product variables have absolute value less
than 2048; the largest axial correction bound is 144.  The gauge uses
11 transverse coordinates, in addition to seven horizontal intrinsic
coordinates, six independent vertical coordinates, $w$, seven axial
corrections, and six products: 38 real variables in total.

The point coordinates used for direct minors are $(P_{iu},P_{iv},z_i+tH_i)$.
They are obtained from the actual spatial coordinates by a nonsingular
positive axial scaling.  Consequently the rank tests, oriented minors,
and actual affine circuit conditions are unchanged.  The independently
compiled ray-1/2 Boolean constraints can be applied to these same minors.
The separate 29-real face chart uses fewer coordinates; this chart adds
uniform bounds and explicitly preserves the small product scales.

The reused topology suffix is valid throughout this chart's range:
the horizontal-unlinking diameter theorem already applies when
$y^2\ge35/4$, below $y\ge32$.  The retained alternating-ring linking
alternatives are both magnitudes 1 and 2, as in the full ray-1/2 system.
The source generator's finite-mask metric prefix is discarded entirely;
no finite-mask separation assertion or $y\ge10^6$ localization premise
is imported.  Finally, the checker verifies all eight consecutive
triangle periods are $(-1,0)$.  Since each of their three oriented
horizontal edges exceeds $-1/2$ and the sum is $-1$, every cyclic
step-one horizontal displacement is negative, justifying the retained
cyclic sign inequalities independently of a mask.
