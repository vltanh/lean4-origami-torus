# Excluding regular C1 by nested sections

There is no unbounded embedded sequence of either remaining marking
whose C1 limit has two noncollinear endpoint triangles and
`0<alpha,beta<1`.

The proof uses sections of the **original embedded sequence**. It is
stronger than a calculation with arbitrary weak realizations of the
limiting determinant signs. In particular, a limiting zero minor is
never declared strictly positive. Convexity and nesting are first
established for finite generic sections and then passed to the limit.

The metric input is the
[closed C1 circle package](solver_remaining_c1_geometry.md), together
with `0<=hi<=1/2` and the nearest-lift inequalities
`hi+h(i+1)>=1/2`. No total-weight budget is used. The seven source CNFs
emitted by `remaining_c1_sections.py` are required premises.

## 1. Two annuli and their sections

The C1 levels are

\[
(0,\alpha/2,1/2,1/2,1/2,\beta/2,0,0),\qquad P_0=P_1=0.
\]

The cycles 067 and 234 divide the triangulation into two annuli. Call
the one containing vertex 1 annulus `B`, and the one containing vertex
5 annulus `A`. Use normalized section height `t=2z`, so the caps occur
at `t=0,1` and the two intermediate vertices at `t=alpha,beta`.

For `0<t<alpha`, the cyclic section of `B` is

\[
\begin{split}
B_-(t)=(&tP_3,\ tP_2,\ (1-t)P_7+tP_2,\\
        &(1-t/\alpha)P_7,\ (1-t/\alpha)P_6,\ 0).
\end{split}                                                     \tag{1}
\]

For `alpha<t<1`, replace its last three vertices by

\[
\frac{t-\alpha}{1-\alpha}P_2,\quad
\frac{t-\alpha}{1-\alpha}P_4,\quad
\frac{t-\alpha}{1-\alpha}P_3.                         \tag{2}
\]

For `0<t<beta`, the section of `A` is

\[
\begin{split}
A_-(t)=(& (1-t)P_6+tP_3,\ (1-t/\beta)P_6+(t/\beta)P_5,\ (t/\beta)P_5,\\
        & (1-t/\beta)P_7+(t/\beta)P_5,\ (1-t)P_7+tP_4,\ (1-t)P_6+tP_4).
\end{split}                                                     \tag{3}
\]

For `beta<t<1`, replace its second, third, and fourth vertices by

\[
\frac{1-t}{1-\beta}P_5+\frac{t-\beta}{1-\beta}P_i,
\qquad i=3,2,4,                                      \tag{4}
\]

in that order. These orders are clockwise at the lower cap. The
checker binds all 24 section vertices to their original edges and
checks the sixteen source faces, both annulus boundaries, and the
two intermediate vertex links. It also verifies every directed
section-edge formula below and all four perimeter identities.

At its intermediate vertex height, each annulus has a quadrilateral
section. With the circle notation, the `B` quadrilateral is

\[
Q_B=(0,-R_1,Y_0,Z_0),\qquad Z_0=Y_0+(1-\alpha)P_7.   \tag{5}
\]

Translate the `A` quadrilateral by `-P5` and reverse its order. It is

\[
Q_A-P_5=(0,-R_5,Y_5,Z_5),\qquad Z_5=Y_5+(1-\beta)F. \tag{6}
\]

This reversal only makes the two scalar calculations identical.

## 2. Every limiting section has perimeter one

For (5), put

\[
\tau_0=\sigma_0-(1-\alpha)h_7.
\]

The norm and dot identities give

\[
|Z_0|^2=\tau_0^2,
\qquad
\tau_0=(1-\alpha)(1-h_0-h_7)+\alpha h_1>0.
\]

The last strict inequality follows from `h7<1/2`, `h0<=1/2`, and
`alpha<1`. Also `rho1>=alpha*(1/2-h2)>0`. The four side lengths are

\[
\rho_1,\quad\alpha h_2,\quad(1-\alpha)h_7,\quad\tau_0,
\]

and their sum is one. All four lengths are positive.
For (6), the corresponding lengths are

\[
\rho_5,\quad\beta h_3,\quad(1-\beta)h_6,\quad
\tau_5=\sigma_5-(1-\beta)h_6>0,
\]

again summing to one.

On each of the four open height intervals in (1)–(4), every directed
edge is a positive affine scalar times a fixed nonzero vector. For
example the six `B` edges below `alpha` are

\[
tE_2,\quad(1-t)P_7,\quad-\frac t\alpha Z_0,
\quad-(1-t/\alpha)F,\quad-(1-t/\alpha)P_6,
\quad-\frac t\alpha R_1.                             \tag{7}
\]

The corresponding statement above `alpha` and on both `A` intervals
is checked by exact expansion. The perimeter is therefore affine in
height on each interval. Its endpoint values are one: each cap is a
perimeter-one triangle, and (5)–(6) have perimeter one. Consequently

\[
\boxed{\operatorname{length} A(t)=\operatorname{length} B(t)=1}
\quad(0<t<1).                                       \tag{8}
\]

These are identities in the limiting projected geometry. The finite
section perimeters need only converge to these values.

## 3. Nesting and the inner critical quadrilateral

### Finite sections and the necessary signs

Start with a sufficiently far member of the original embedded
sequence, and make an arbitrarily small generic perturbation. The
perturbation is chosen small enough to preserve every normalized
coordinate, metric residual, and auxiliary limit already used in
the bounded chart; merely tending to zero in unscaled coordinates
would not suffice. Arbitrarily small embedding-preserving generic
perturbations permit this choice. Reanchor the axis through 01 so
that `P0=P1=0` still holds. Flatten the plane through 067 by a shear of the
height coordinate, leaving all transverse coordinates unchanged.
Because the limiting projected cap is noncollinear, the shear tends
to zero in the normalized coordinates. All other vertices remain
above this plane; vertices 2,3,4 remain above both intermediate
heights. Projection of each section plane onto the transverse plane
is injective, so it preserves simplicity, nesting, and convexity.

The finite sections consist of two disjoint simple polygons. Near the
lower cap both surround its interior, so one is inside the other.
Their nesting order cannot change at an interior height because the
two annuli are disjoint. The intermediate vertices have contiguous
upper and lower neighbors, so crossing either intermediate height
does not join or split the two section cycles.

Let `L` be the generic sign of `[0156]`. The independently certified
source implications are

\[
\begin{array}{c|c}
L>0 &[0157]<0,\quad[0237]>0,\\
L<0 &[3467]>0.
\end{array}                                                       \tag{9}
\]

The common signs are

\[
[0123]>0,\quad[0127]<0,\quad[3456]<0,\quad[4567]<0.   \tag{10}
\]

These strict signs refer to the finite generic configurations, not to
their possibly zero limits. Three additional CNFs force both limiting
cap orientations to be positive.

To identify the inner annulus, look near vertex 0 of the lower cap.
The `A` section has the corner `(t/beta)P5`, with adjacent edge
directions `-P6` and `P7`. The fixed transverse origin, a vertex of
the `B` section, lies inside that corner exactly when `-P5` lies in
the positive cone of `P6,P7`. For the finite generic configuration
this is equivalent to `C56>0` and `C57<0`. Thus (9) gives:

| Generic branch | Inner annulus | Favorable critical turn |
|---|---|---|
| `[0156]>0` | `B` | `[0237]>0` |
| `[0156]<0` | `A` | `[3467]>0` |

When `[0156]<0`, the origin is outside the `A` section; since the two
interiors overlap near the cap, `A` must be inside `B`.
The finite sign choices persist on a subsequence even if the
corresponding limiting cross products vanish.

### A strict bound at the distinguished vertex

The remaining corner of either critical quadrilateral has a strict
metric bound. For `B`, abbreviate

\[
a=\alpha,\ q=1-a,\ h=h_2,\ k=h_7,\quad
\rho=\rho_1,\ \sigma=\sigma_0,\ \tau=\sigma-qk,
\quad n=|Y_0|.
\]

The vector `Y0` is nonzero. Indeed, with `p=d0`, `r=d1`,

\[
n^2-(\tfrac12-p-r)^2
=[ap+(1-a)r](1-2p-2r)+[ap-(1-a)r]^2\ge0.
\]

Here `p+r<=1/2` is the nearest-lift bound. Equality `n=0` would give
`p=(1-a)/2`, `r=a/2`, `sigma=1-a`, and then the dot identity would
force `h7=1/2`, contradicting cap regularity. The same proof gives
`Y5!=0`, using `h6<1/2`.

Let `phi` and `chi` be the angles at the origin in the two triangles
`(0,-R1,Y0)` and `(0,Y0,Z0)`. Their cosine sum has numerator

\[
N=\tau(\rho^2+n^2-a^2h^2)
  +\rho(n^2+\tau^2-q^2k^2),\qquad
\cos\phi+\cos\chi=\frac{N}{2\rho\tau n}.
\]

Put `r2=1/2-h`, `r7=1/2-k`. Exact expansion gives

\[
\begin{split}
N={}&2h_0\,q r_7(q+2ar_2)
    +2h_1\,a r_2(a+2qr_7)\\
   &+2(h_0+h_1-\tfrac12)aq(h+k-2hk)>0.              \tag{11}
\end{split}
\]

All factors are nonnegative, `r2,r7,a,q` are positive, and
`h0+h1>=1/2`. Hence `phi+chi<pi`. The identical calculation for `A`
uses `(h0,h1,h,k,a)=(h5,h4,h3,h6,beta)`.

The strict bound survives in sufficiently far finite sections. The
two adjacent triangles lie on opposite sides of the diagonal by
(10), so their angle sum is the interior angle at the distinguished
vertex. That vertex is therefore strictly convex.

The other three turns of the finite `B` critical quadrilateral have
the signs of `-[0123]`, `-[0237]`, and `[0127]`, with positive
factors. For the reversed `A` critical quadrilateral they have the
signs of `-[3456]`, `[3467]`, and `-[4567]`. The companion verifies
these six formulas with arbitrary finite upper heights `z2,z3,z4`;
it does not substitute the limiting equal heights prematurely.
Equations (9)–(11) therefore make the **inner** critical
quadrilateral strictly convex in the finite sequence.

## 4. Equal perimeter forces coincident boundaries

Pass to the limit at the inner critical height. Its quadrilateral is
a convex boundary of perimeter one, possibly initially allowing a
degenerate segment. Let its convex hull be `K`, and let `L` be the
convex hull of the outer limiting section. Nesting gives `K subset L`.
For planar convex sets, perimeter is monotone, and is strictly
monotone under proper inclusion. The perimeter of a polygonal curve
is at least the perimeter of its convex hull. Thus (8) gives

\[
1=\operatorname{perim}K
\le\operatorname{perim}L
\le\operatorname{length}(\text{outer section})=1.
\]

It follows that `K=L`, and equality in the polygonal triangle
inequalities makes the outer curve traverse the same convex boundary.

This common boundary is nondegenerate. If the critical heights differ,
the outer section has three nonzero edges in the three nonparallel
directions of one regular cap. It cannot be a segment. If the heights
are equal and both critical quadrilaterals were collinear, (5) would
make `P2,P3,P7` collinear with the origin. The `A` edges parallel to
`E3` and `F` would then put `P4,P6` on that same line, contradicting
both regular caps.

All four critical side lengths are positive. The distinguished
vertex is a genuine corner by (11). The common boundary is therefore
a triangle or a quadrilateral, with at least two of the other three
critical vertices genuine corners.

## 5. Different critical heights are impossible

We use a simple support-function observation. On an interval where
the outer section has fixed nonzero edge directions, convexity at
one height makes it convex throughout that interval: its cyclic
edge-direction order is unchanged. Its normal cones are fixed, and
each support function is affine in height.

Suppose a point `v(t)` is affine in height, lies in the inner section
on both sides of the critical height, and is a genuine corner of the
common boundary there. For a normal strictly inside that corner's
normal cone, the difference between the outer support function and
`n dot v(t)` is affine, nonnegative on both sides, and zero at the
critical height. It vanishes identically. Two independent normals
therefore show that `v(t)` tracks a single outer vertex throughout
the interval. This identity extends to the cap endpoint of the
interval.

### Inner annulus B

Its three common vertices, present both below and above `alpha`, are

\[
U(t)=tP_3,\qquad V(t)=tP_2,\qquad
W(t)=(1-t)P_7+tP_2.                                 \tag{12}
\]

If `alpha<beta`, both `U,V` tend to 0 at the lower cap. The outer `A`
section has only one vertex tending to 0, namely the intersection of
05. Thus `U,V` cannot both be genuine corners. Since there must be at
least two genuine common corners, `W` and exactly one of `U,V` are
genuine, while the other is flat.

The outer vertices tending to `P7` are 47 and 57. Tracking 47 by `W`
would give `P4=P2`, impossible. Tracking 57 gives

\[
P_5=\beta P_2+(1-\beta)P_7.                          \tag{13}
\]

If `V` is genuine, tracking 05 gives `P5=beta*P2`, contradicting
(13) and `P7!=0`. If `U` is genuine, it gives `P5=beta*P3`, so
`beta*(P3-P2)=(1-beta)*P7`. But then `V` is flat: the consecutive
edges in directions `E2` and `P7` must point the same way along the
convex boundary. The displayed equality makes them point opposite
ways, again impossible.

If `alpha>beta`, use the upper cap. Now `V,W` both tend to `P2`,
where the outer section has only the vertex 25. Hence `U` and one
of `V,W` are genuine. The outer vertices tending to `P3` are 36 and
35. Tracking 36 would give `P6=0`, impossible; tracking 35 gives
`P5=beta*P3`. Tracking 25 by `V` then gives `P2=P3`. Tracking 25
by `W` gives (13), while `V` is flat, producing the same opposite-
direction contradiction as before.

### Inner annulus A

For completeness the symmetric endpoint argument is explicit. Its
common vertices are

\[
X(t)=(1-t)P_6+tP_3,\quad
Y(t)=(1-t)P_6+tP_4,\quad
Z(t)=(1-t)P_7+tP_4.
\]

If `beta<alpha`, `X,Y` both tend to `P6`, where outer `B` has only
vertex 16. Thus `Z` and one of `X,Y` are genuine. Tracking `Z` by
27 gives `P4=P2`; tracking it by 17 gives
`alpha*P4=-(1-alpha)*P7`. Tracking `Y` by 16 would force `P6=P7`.
Tracking `X` by 16 instead gives
`alpha*P3=-(1-alpha)*P6`, hence
`alpha*E3=-(1-alpha)*F`. But `Y` is then flat, so its consecutive
edges in directions `E3,F` must point the same way, a contradiction.

If `beta>alpha`, `Y,Z` both tend to `P4`, where outer `B` has only
vertex 14. Thus `X` and one of `Y,Z` are genuine. Tracking `X` by
03 would give `P6=0`; tracking it by 13 gives
`alpha*P3=-(1-alpha)*P6`. Tracking `Y` by 14 forces `P3=P4`.
Tracking `Z` by 14 gives `alpha*P4=-(1-alpha)*P7`; now `Y` is flat
and the same opposite-direction contradiction applies.

The companion checks all sixteen vertex-tracking identities used in
these four arguments. We conclude

\[
\boxed{\alpha=\beta.}                               \tag{14}
\]

## 6. Coincident critical quadrilaterals are impossible

Put `u=alpha=beta`, `q=1-u`. Use clockwise labels

\[
\begin{aligned}
(B_0,B_1,B_2,B_3)&=(0,uP_3,uP_2,uP_2+qP_7),\\
(A_0,A_1,A_2,A_3)&=(uP_3+qP_6,P_5,uP_4+qP_7,uP_4+qP_6).
\end{aligned}
\]

They satisfy the exact vector identity

\[
A_0+A_2-A_3=B_1-B_2+B_3.                            \tag{15}
\]

Their cap areas are recovered by

\[
\begin{aligned}
u^2 A_u&=\operatorname{cross}(B_1-B_2,A_2-B_3)>0,\\
q^2 A_l&=\operatorname{cross}(A_0-B_1,B_3-B_2)>0.
\end{aligned}                                                       \tag{16}
\]

If the common boundary has four corners, both cyclic vertex lists
agree up to a shift: `Ai=B(i+k)`, `k=0,1,2,3`. Exact substitution in
(15)–(16) gives:

| Shift k | Obstruction |
|---:|---|
| 0 | `Al=0` |
| 1 | `Al=0` |
| 2 | `Au=0` |
| 3 | `q^2 Al=cross(B2-B1,B3-B2)<0` |

The last sign is the strict clockwise turn at `B2`.

If the common boundary is a triangle, each quadrilateral has one
flat vertex strictly between its neighbors. Neither distinguished
vertex can be flat: these are `B0` and `A1`, and both satisfy (11).
Thus the flat `B` index is one of `1,2,3`, the flat `A` index is one
of `0,2,3`, and there are three cyclic matches of the remaining
triangle vertices: **27 cases**.

Normalize the clockwise triangle to `(0,0),(1,0),(0,-1)`. Put the
flat vertices at fractions `s,t` strictly between zero and one on
their respective sides. Equation (15) is a two-coordinate linear
system in `s,t`. Exact linear algebra gives four inconsistent cases
and twenty cases requiring an endpoint or a fraction outside `(0,1)`.
The remaining three have `s=t`; the upper numerator in (16) is
respectively `t-1`, `0`, or `-t`. None is positive. The checker emits
the complete 27-case table and verifies every substitution exactly.

The segment case was already excluded in Section 4. Hence the
coincident section is impossible in every case, completing the
regular C1 exclusion.

## 7. Verification and scope

```sh
python research/type7_completion/remaining_c1_sections.py /tmp/type7-c1-sections
python research/type7_completion/solver_cnf_certificates.py /tmp/type7-c1-sections-rup \
  --checker /path/to/solver-check-rup /tmp/type7-c1-sections
```

The algebraic replay checks the strict corner decomposition, both
critical perimeter identities, 24 section-edge identities, four full
section perimeter identities, sixteen corner-tracking identities,
six finite-height turn identities, and all 31 coincident-boundary
matches. All seven topology CNFs additionally require independent
RUP replay. The planar convexity, nesting, support-function, and
perimeter arguments are supplied above as mathematical proofs.

The result includes zero individual deficits, flat critical corners,
and limiting zero orientation minors. It assumes both endpoint caps
remain noncollinear and both intermediate heights remain interior;
collinear caps and height endpoints require their separate arguments.
