# A section obstruction for the upper-b collinear cap

Consider an unbounded embedded ray-1 sequence with an interior C0 limit
whose upper cap has order b and whose lower cap 067 is regular:

\[
d_2=0<d_1=L,\qquad 0<u,v<1/2.
\]

The direct annulus `B`, with faces `013,023,027,127,167,016`, **cannot
be the outer of the two nested section curves**. This holds for both
strict orders of `u,v` and for `u=v`. Thus every remaining sequence in
this stratum must have the complementary annulus `A` outside `B`.

The proof uses actual embedded finite sections and winding stability.
It does not use a generic sign completion as a replacement for a zero
limiting determinant. Its companion checks the section formulas, source
faces and links, and every metric identity exactly; no Boolean or
numerical solver is needed.

## 1. Finite nesting and its limiting consequence

The lower triangle 067 is regular. As in the
[height-boundary proof](remaining_c0_height_boundary.md), make a
sufficiently small embedding-preserving generic perturbation, reanchor
01, and flatten the plane of 067 by a normalized height shear tending
to zero. The perturbations can preserve every metric and auxiliary
limit at the scales in use.

Near the lower cap, both annulus sections surround a fixed point in
its interior. They are disjoint simple curves, so they are nested.
The upper and lower neighbors of each intermediate vertex 4 and 5
are contiguous in its link, in either relative height order. Hence
the section cycles do not split or join at those heights; their
nesting order persists throughout the open height interval. The
companion checks both links against the original faces.

Take a subsequence with a fixed nesting order and suppose `B` is the
outer curve. At every fixed normalized section height `s` in `(0,1)`,
every limiting `A` section point belongs to

\[
\mathcal F(B(s)):=B(s)\ \cup\
 \{q:\operatorname{wind}(B(s),q)\ne0\}.                    \tag{1}
\]

To justify (1), if a limiting point is off the limiting curve and has
winding zero, it has a neighborhood disjoint from that curve. Uniform
convergence of the polygonal curves makes the finite winding number
zero on this neighborhood as well. A point of the inner `A` curve
cannot lie there, since the finite outer simple curve has winding
`+1` or `-1` throughout its bounded region. Points on the limiting
curve remain allowed. Thus a vanishing-width part of the outer
region is retained rather than discarded.

At a critical height, the same conclusion follows by approaching
the vertex along a neighboring `A` edge and using the closure of
the finite outer bounded region. In particular it applies to vertex
5 at its limiting height `v`.

## 2. The direct section has a backtracked segment

Choose a transverse unit vector `e` so that

\[
P_1=0,\qquad P_2=a e,\qquad P_3=-L e,
\qquad a=1/2-L>0.                                       \tag{2}
\]

Regularity of 067 gives `M=d6+d7>0` and `L<1/2`. With `s=2z`, the
direct section has cyclic vertices

\[
0,\ -sLe,\ sae,\ sae+(1-s)P_7,\ (1-s)P_7,\ (1-s)P_6.  \tag{3}
\]

Its excursion `0 -> -sLe -> 0` is traversed in both directions and
cancels in the winding number. The remaining closed five-edge walk
has vertices

\[
C(s)=\bigl(0,sae,sae+(1-s)P_7,(1-s)P_7,(1-s)P_6\bigr).
\]

No simplicity of this limiting walk is asserted or needed. A closed
polygonal walk has winding zero outside the convex hull of its vertices.
Consequently

\[
\mathcal F(B(s))\subset
 \operatorname{conv}C(s)\ \cup\ [-sLe,0].                 \tag{4}
\]

The leftmost horizontal coordinate of `conv C(s)` is bounded below
by `-C(1-s)` for a constant `C`: its only potentially negative
horizontal contributions come from `(1-s)P6` and `(1-s)P7`.

## 3. Outer containment forces three transverse points onto the line

For `s>max(2u,2v)`, the complementary section traverses the six
edges `34,14,24,25,35,36`. Three of its vertices converge to `P3`
as `s` tends to one:

\[
\begin{aligned}
A_{34}(s)&=P_3+\frac{1-s}{1-2u}(P_4-P_3),\\
A_{35}(s)&=P_3+\frac{1-s}{1-2v}(P_5-P_3),\\
A_{36}(s)&=P_3+(1-s)(P_6-P_3).
\end{aligned}                                           \tag{5}
\]

Choose one fixed `s<1` sufficiently close to one that all three
horizontal coordinates in (5) are less than `-L/2`, while every
point of `conv C(s)` has horizontal coordinate greater than `-L/4`.
By (1) and (4), all three points in (5) lie on the backtracked segment.
Their normal coordinates must vanish. The coefficients in (5) are
strictly positive, so

\[
P_4=x_4e,\qquad P_5=x_5e,\qquad P_6=\epsilon M e,
\qquad\epsilon\in\{-1,1\}.                             \tag{6}
\]

This argument takes the sequence limit at a fixed section height
before choosing that height close to one. It does not compare an
unknown finite cap width to `1-s`.

## 4. A precise interval containing the axis part of the outer region

The lower cap is regular and `P6` is a nonzero multiple of `e`.
Hence `P7` has a nonzero component normal to `e`. All non-axis vertices
of `C(s)` have exactly the same normal component `(1-s)P7_y`.
Thus its convex hull lies in one closed half-plane bounded by the axis,
and its intersection with the axis is the interval spanned by its
three axis vertices `0,sae,(1-s)epsilon M e`.

Combining this fact with (4), every axis point of the filled outer
limit has horizontal coordinate at least

\[
\min(-sL,(1-s)\epsilon M).                              \tag{7}
\]

Apply (7) at `s=2v` to `P5`, using the critical-height consequence of
(1). It gives

\[
x_5\ge\min(-2vL,(1-2v)\epsilon M).                      \tag{8}
\]

## 5. The closed metric identities contradict that containment

Put

\[
\begin{gathered}
p=d_3,\quad q=d_4,\quad g=d_5,\quad
D=d_0+L+M,\qquad \ell_u=1-2u,\quad\ell_v=1-2v,\\
Q_4=P_4-2uP_3-\ell_uP_6,\qquad
Q_5=P_5-2vP_3-\ell_vP_6.
\end{gathered}
\]

The closed C0 metric source gives the strictly positive radii

\[
r=|Q_4|=q+g+2uD=h_3-\ell_uD>0,
\qquad
s_*=|Q_5|=p+q+\ell_vD=h_5-2vD>0.                        \tag{9}
\]

By (6), write `Q4=sigma r e` and `Q5=tau s_* e`, with
`sigma,tau` independently in `{-1,1}`.

If `tau=-1`, then

\[
x_5=-2vL+\ell_v\epsilon M-(p+q+\ell_vD).
\]

This lies strictly to the left of both endpoints in (8):

\[
\begin{aligned}
x_5+2vL&=-(p+q)-\ell_v(D-\epsilon M)<0,\\
x_5-\ell_v\epsilon M&=-2vL-s_*<0.
\end{aligned}
\]

The first strict sign uses only `D-epsilon M>=L>0`; the second uses
`v,L,s_*>0`. Thus `tau=-1` contradicts (8), for either value of
`sigma` or `epsilon`.

It remains to consider `tau=+1`. Here `E=P3-P2=-e/2` and `h2=1/2`.
The exact middle dot equation is

\[
E\cdot(\ell_vQ_4-\ell_uQ_5)
=h_2(\ell_vr+\ell_us_*)-\ell_v(h_2-p).
\]

Equivalently,

\[
\ell_v(\sigma+1)r+\ell_u(1-\tau)s_*=2\ell_vh_3.         \tag{10}
\]

For `sigma=-1,tau=+1`, equation (10) forces `h3=0`, impossible
because `h3=D+q+g>0`. For `sigma=tau=+1`, it forces `r=h3`,
contrary to `r=h3-lu D` and `lu D>0`.

All four sign choices are excluded. Therefore `B` cannot be outer.

## Reproduction and remaining scope

```sh
python research/type7_completion/remaining_c0_upper_b_sections.py
```

The exact checker binds all twelve section edges to their original
faces, checks the two intermediate vertex links in both height orders,
replays the complete closed metric source, and verifies the three
normal-coordinate formulas and all four radius-sign contradictions.
The winding stability and convex-hull arguments above supply the
geometric proof.

This closes one complete nesting alternative for the **entire upper-b
stratum**, with all limiting zero brackets retained. It leaves the
opposite nesting order `A` outer, the other upper-collinear orders,
and degenerate height boundaries separate. It is not a full ray-1
or Type 7 exclusion.
