# A section obstruction for one-collinear C0 limits on a common axis

There is no embedded ray-1 sequence with a C0 limit satisfying

* `0<u<v<1/2`, `d1=0`, and a regular positively oriented lower cap 067;
* `P2,P4,P5,P6` collinear with the origin.

This includes both the strict upper-a order `d1=0<d2` and the coincident
order `d1=d2=0`, but only on the stated common-axis family. It is not
a reduction of the whole one-collinear stratum to that family.

The proof uses the already established necessary actual signs
`C27<=0` and `[4567]<=0`, from the
[collinear-cap](exhaustive_c0_collinear.md) and
[positive extension](exhaustive_c0_collinear_positive.md) packages.

## Coordinates and the two annuli

Set `L=d2>=0`, `M=d6+d7>0`, and choose the unit direction `e` so that

\[
P_2=-\tfrac12e,\qquad P_3=-Le.
\]

Since `C27<=0` and `C67>0`, the common-axis hypothesis forces
`P6=Me` and `P7_y>0`. The deficit budget and lower-cap regularity
give `L<1/2` and `M<1/2`.

Write `alpha=2u`, `beta=2v`. At every normalized height `w` between
`beta` and 1, the direct annulus B has the section

\[
0,\quad-wLe,\quad-\tfrac w2e,\quad
-\tfrac w2e+(1-w)P_7,\quad(1-w)P_7,\quad(1-w)Me.
\tag{1}
\]

The convex hull of (1) meets the axis precisely in

\[
[-w/2,(1-w)M]e.                                      \tag{2}
\]

Indeed its only vertices off the axis have the same positive vertical
coordinate `(1-w)P7_y`. The section has nonzero winding on an open
set: after suppressing the collinear intermediate point `-wLe`, it
is the boundary of a nondegenerate convex polygon. Its successive
horizontal boundary edges have opposite directions, and the remaining
two boundary vectors are positive multiples of `P7` and `P6-P7`.

The other annulus A has the upper section with vertices on edges
`34,14,24,25,35,36`. All six limiting vertices lie on the axis. In
particular the vertices on edges 14 and 35 are

\[
\frac{1-w}{1-2u}P_4,\qquad
-Le+\frac{1-w}{1-2v}(P_5+Le).                         \tag{3}
\]

Finite embedded sections are disjoint Jordan curves and have a fixed
nesting order through the interval. Their limits inherit containment
in the outer limiting curve together with its nonzero-winding region.
This follows by winding-number stability at any point outside the
limiting curve. In particular containment in the convex hull survives.
The finite-section and annulus facts are the same as in the
[upper-b section proof](remaining_c0_upper_b_sections.md); all twelve
face incidences for (1) and (3) are checked again in the companion.

Annulus A cannot be outer: its limiting curve is on a line, whereas
the limiting B section has nonzero winding on an open set. Equivalently,
the B vertex `(1-w)P7` lies off the line and cannot remain inside a
sequence of Jordan curves converging to that line.

## The direct annulus cannot be outer either

Suppose B is outer. The edge-14 point in (3), together with (2), gives

\[
x_4\le(1-2u)M.                                      \tag{4}
\]

Use `p=d3`, `q=d4`, `g=d5`, `D=d0+L+M`, and the exact metric notation

\[
\begin{gathered}
\ell_u=1-2u,\quad\ell_v=1-2v,\quad h_2=1/2-L,\quad h_3=1/2-p,\\
Q_4=(x_4+2uL-\ell_uM)e,\quad
Q_5=(x_5+2vL-\ell_vM)e,\\
|Q_4|=r=q+g+2uD>0,\qquad
|Q_5|=s=p+q+\ell_vD>0.
\end{gathered}
\]

Bound (4) gives `Q4 dot e<=2uL`, while `r>=2uD>2uL`.
Therefore `Q4=-r e`.

If `Q5=+s e`, the dot equation `Q4 dot Q5=-rs+q` forces `q=0`.
The equation involving `E=P3-P2=h2 e` then reduces exactly to

\[
p\bigl(\ell_v+4h_2(v-u)\bigr)=0.
\]

Thus `p=0`. But `W=vQ4-uQ5=-(vr+us)e`, so

\[
[4567]=-\operatorname{cross}(W,P_7-P_6)
=(vr+us)P_{7,y}>0,
\]

contrary to its proved weak nonpositive sign.

It remains that `Q5=-s e`. Now `q=2rs`, and the `E.S` equation is

\[
2h_2r=h_2-p,\qquad Lp=h_2\ell_uD>0.                  \tag{5}
\]

The second identity immediately rules out `L=0`. Otherwise `p>0`,
and substituting `q=2rs` into `s=p+q+lv D` gives

\[
s=h_2+\frac{h_2\ell_vD}{p}
 =h_2+\frac{\ell_vL}{\ell_u}.
\]

Consequently

\[
x_5+v=\ell_v\left(M-h_2-\frac L{\ell_u}\right)<0.     \tag{6}
\]

The inequality is strict because `M<1/2` and
`h2+L/lu=1/2+2uL/lu>=1/2`. Formula (6) puts `P5` strictly to
the left of the interval (2) at `w=2v`. By continuity, the edge-35
point from (3) remains strictly left of (2) for some fixed
`w>2v`. That contradicts containment of the A section in the
convex hull of B.

Both nesting orders are impossible, proving the stated common-axis
exclusion. No cap-area scale, minimum deficit, or nonzero limiting
mixed determinant was assumed.

## Exact replay

```sh
python research/type7_completion/remaining_c0_one_collinear_axis.py
```

The checker binds the metric equations to the original C0 source,
checks the section-face incidences and coordinates, and expands the
four radius sign cases and the strict endpoint contradiction. The
winding and inequality arguments are supplied above; no numerical
solver or Boolean source implication is used by this package.
