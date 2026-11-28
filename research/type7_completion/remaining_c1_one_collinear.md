# Ray-2 C1 with exactly one collinear cap

There is no unbounded embedded ray-2 sequence whose C1 limit has
exactly one collinear endpoint cap and `0<alpha,beta<1`.

This extends the [regular C1 section proof](remaining_c1_sections.md).
It retains actual zero brackets, both possible zero edges in the
collinear cap, and coincident critical heights. It uses the ray-2
weight budget. Both-collinear caps and height endpoints are outside
its scope. The eight CNFs emitted by
`remaining_c1_one_collinear.py` require independent RUP replay.

## 1. Normalization and the five remaining upper-cap orders

Use the checked marked cap swap `i -> i+4`, when necessary, to put
the regular cap at 067. Its new height parameters are
`1-beta,1-alpha`, still interior. Reanchoring the spatial axis changes
each horizontal section by a common translation, so its perimeter,
convexity and nesting are preserved. The companion replays both marked
symmetry checks from
[the collinear rank package](solver_remaining_c1_collinear_rank.md).

Choose the ambient transverse orientation so that

\[
A_l=\operatorname{cross}(P_6,P_7)>0.
\]

Write `M=|P6|=1-h6-h7`. Regularity gives

\[
0<M,h_6,h_7<\tfrac12,\qquad h_6+h_7>\tfrac12.
\tag{1}
\]

The four nearest-lift slacks

\[
h_0+h_1-\tfrac12,\quad h_2+h_3-\tfrac12,\quad
h_4+h_5-\tfrac12,\quad h_6+h_7-\tfrac12
\]

are nonnegative and sum to `1/2`, because `sum hi=5/2`.
The coincidence `P2=P4` would give `h2=h3=1/2`, consuming that
entire sum while the last slack is positive. It is impossible.
The nonconstant collinear upper triangle therefore has exactly one
of the following five forms:

| Upper-cap order | Edge conditions |
|---|---|
| 4 strictly between 2 and 3 | `h2=1/2`, `0<h3<1/2` |
| 2 strictly between 3 and 4 | `h3=1/2`, `0<h2<1/2` |
| 3 strictly between 2 and 4 | `h2+h3=1/2`, `h2,h3>0` |
| `P2=P3` | `h2=0`, `h1=h3=1/2` |
| `P3=P4` | `h3=0`, `h2=h4=1/2` |

The extra adjacent half-weights in the last two rows follow from the
nearest-lift inequalities. A fully coincident upper cap is impossible
because its three edge lengths sum to one.

## 2. Finite nesting and the surviving strict corner bound

Use the same annuli `A` (containing vertex 5) and `B` (containing
vertex 1), section formulas, and critical quadrilaterals as in the
regular proof. Every limiting section still has perimeter one. The
edge and perimeter identities do not divide by an upper edge or cap
area; a zero edge is simply omitted from the polygonal curve.

The lower cap remains regular, so all the finite-section operations
in that proof remain valid: make arbitrarily small generic,
embedding-preserving perturbations that preserve all normalized and
auxiliary limits, flatten the plane 067 by a vanishing height shear,
and project each section plane injectively to the transverse plane.
Both finite section cycles are simple, disjoint and nested. Their
nesting order is constant between the two caps.

Here the generic source formula has its freely chosen orientation
unit `[0123]>0` removed. All embedding and absolute-linking clauses
remain. Add the two strict height cuts with high sets `{2,3,4}` and
`{1,2,3,4,5}`, and the five positive ordered brackets `[067j]` for
`j=1,2,3,4,5`. These cuts and cap signs persist in the finite sequence.

Put `L=[0156]` in its finite generic sign model. Two source CNFs give

\[
L>0\Longrightarrow[0157]<0,
\qquad
L<0\Longrightarrow[3456]<0\ \hbox{and}\ [4567]<0.
\tag{2}
\]

As in the regular proof, the first implication identifies `B` as
inner when `L>0`; when `L<0`, `A` is inner. The checked marked
reflection `i -> 6-i` swaps the annuli and swaps `alpha,beta`.
It reverses the lower-cap orientation and preserves the literal
`[0156]`. An additional ambient transverse reflection restores
`Al>0` and reverses `L`. We may therefore assume throughout the
remaining proof that **A is inner and L<0**. This also exchanges the
two coincident upper-cap cases, so no zero-edge case is discarded.

The strict distinguished-corner inequality survives. In the notation
of equation (11) of the regular proof, only the lower edge `k` needs
to satisfy `k<1/2`: nearest lifts give `h0>=1/2-h7>0` for `B` and
`h5>=1/2-h6>0` for `A`. Hence the first term

\[
2h_0(1-a)(\tfrac12-k)
\bigl((1-a)+2a(\tfrac12-h)\bigr)
\]

in that positive decomposition is strictly positive, including
`h=0` or `h=1/2`. The same zero-norm argument gives `Y0,Y5!=0`.
Also `rho1,rho5,tau0,tau5>0`; for example
`rho5>=(1-beta)h5>0` and `tau5>=(1-beta)(1/2-h6)>0`.
Consequently the two angles at the distinguished vertex satisfy

\[
\phi+\chi<\pi.                                      \tag{3}
\]

The finite signs in (2) put the adjacent triangles on opposite
sides of the distinguished diagonal. Thus (3) is the strict
interior-angle bound used by the regular section argument. It also
prevents the distinguished vertex of a nondegenerate convex limiting
section from becoming a flat boundary point.

## 3. A convex inner critical section for every strict upper order

Suppose first that 2,3,4 are distinct. For each of the three strict
orders, an actual-bracket CNF proves

\[
[3467]\ge0.                                         \tag{4}
\]

These models use actual positive/negative trits, affine five-point
cocycles, the positive interpolation expressing the middle upper
point, weak Grassmann-Pluecker relations, and the two checked height
identities. An actual zero bracket leaves its generic sign free.
In particular, (4) is not asserted to hold strictly in the finite
generic sequence.

Translate and reverse the inner critical section as before:

\[
Q=(0,-R,Y,Z),\quad R=R_5,\ Y=Y_5,
\quad Z=Y+(1-\beta)F,\quad F=P_7-P_6.
\tag{5}
\]

Its other consecutive edge is `beta E3`, where `E3=P4-P3`.
The first and last turns are nonnegative by (2), and its middle
turn is nonnegative by (4). If (5) is noncollinear, (3) and these
three weak turns make it a convex boundary. One can see this
directly by putting the nonzero diagonal `Y` between `-R` and `Z`
in their angular cone of width less than pi: the middle-turn
inequality puts `Y` on or beyond the opposite side `[-R,Z]`.

If (5) is collinear, (3) puts `-R,Y,Z` on the same open ray.
It traverses its full segment once in each direction except for
one possible ordering: `Y` lies strictly between 0 and both
`-R,Z`. In this backtracking case, set `h=h3`, `k=h6`,
`q=1-beta`, and take the unit vector `e=E3/h`. Then

\[
R=\rho e,\qquad F=-ke,
\qquad \rho=\tfrac12-qk.                            \tag{6}
\]

For completeness, the two circle dot identities first give
`delta4=2h rho` and `delta5=k(1-2 beta h)`. Substitution into the
definition of `rho5` gives

\[
(1-2\beta h)(\rho-\tfrac12+qk)=0.
\]

Its first factor is positive. Put

\[
n=\tfrac12-\beta h-qk>0,\qquad
\tau=\tfrac12-\beta h>0.
\]

The original limiting spatial points `ri=(Pi,zi)` now satisfy three
positive-coefficient affine dependencies:

\[
\begin{aligned}
r_5+(n/h)r_3-(\rho/h)r_4-q r_6&=0,\\
r_7+(k/h)r_4-r_6-(k/h)r_3&=0,\\
r_5+(n/k)r_7-\beta r_4-(\tau/k)r_6&=0.
\end{aligned}                                       \tag{7}
\]

The coefficient sums vanish as well. Applying every triple of
vertices to each affine dependency gives necessary signed-zero-sum
relations between actual brackets. A separate CNF for each strict
upper order proves these relations incompatible with the source and
`L<0`. This excludes the backtracking ordering, including all
vanishing minors. Thus **the inner critical section is a convex
boundary** in every strict upper order.

If instead `P3=P4`, its edge `beta E3` is zero and (5) is a triangle.
It is already a convex boundary, possibly initially a segment. No
middle-turn or backtracking CNF is needed for this case.

## 4. Consequences of a convex inner critical section

At the critical height `t=beta`, nesting and the two perimeter-one
identities give exactly the chain from the regular proof:

\[
1=\operatorname{perim}K
\le\operatorname{perim}\operatorname{conv}(B(\beta))
\le\operatorname{length}B(\beta)=1.
\]

Both section curves therefore traverse the same convex boundary.
It cannot be a segment using only lower-cap regularity. Such a
segment would be parallel to the nonzero inner edge `F`. The outer
section has a nonzero edge parallel to `P7`. Its line passes through
0: below or at `alpha` it contains 0 directly; above `alpha` it
contains the two distinct scalar multiples `beta P3` and
`((beta-alpha)/(1-alpha))P3`, with `P3!=0`. Hence `P7` and `F`
would be parallel, contradicting `Al>0`.

### Unequal critical heights

For the three strict upper orders, the support-function argument of
the regular proof applies unchanged. All upper vertices are distinct
and all its relevant edges are nonzero. Only distinctness, not upper
cap area, was used in the four endpoint tracking contradictions.
In particular, for inner `A`, the common vertices

\[
X=(1-t)P_6+tP_3,\quad
Y=(1-t)P_6+tP_4,\quad
Z=(1-t)P_7+tP_4
\]

give `P4=P2`, `P6=P7`, `P6=0`, `P3=P4`, or opposite directions
at a flat convex corner if `alpha!=beta`. All are impossible.

Here are the extra details when `P3=P4`. Now `X=Y`, and the inner
critical section is a nondegenerate triangle with genuine common
corners `X,Z`.

If `beta<alpha`, `X` must track outer edge 16 and `Z` must track
27 or 17. Tracking 27 gives `P4=P2`, impossible; tracking 17 gives
`alpha P4=-(1-alpha)P7`, whereas tracking 16 gives
`alpha P3=-(1-alpha)P6`. Since `P3=P4`, this forces `P6=P7`.

If `beta>alpha`, both `X,Z` tend to the common upper point `P3=P4`.
The outer section has only two distinct vertex trajectories with that
endpoint: `tP3` and `((t-alpha)/(1-alpha))P3`; its 13 and 14
trajectories coincide identically. Distinct genuine corners must
track different trajectories, so one must track `tP3`. This forces
`P6=0` or `P7=0`, again impossible. Fixed zero edges can be omitted
from the support-function argument, since every remaining edge keeps
a positive scalar multiple of a fixed direction on its stratum.

Thus `alpha=beta` in every convex-inner case under consideration.

### Coincident critical heights

Use the same clockwise vertex lists `Bi,Ai` as the regular proof.
They satisfy

\[
A_0+A_2-A_3=B_1-B_2+B_3,
\qquad
(1-\alpha)^2 A_l
=\operatorname{cross}(A_0-B_1,B_3-B_2)>0.             \tag{8}
\]

The coincidence check only needs the lower area. If the common
boundary has four corners, the four cyclic matches `Ai=B(i+k)`
give respectively zero, zero, the strict clockwise turn at `B2`,
and that same negative turn for the lower-area numerator.

If it is a triangle and all critical edges are positive, `B0` and
`A1` are genuine corners by (3). The same 27 flat-vertex matches
as before give four inconsistent systems and twenty endpoint or
out-of-range fractions. The remaining three have equal interior
fractions `s=t`; their **lower** area numerators are `t-1,0,-t`.
All contradict (8).

When `P3=P4`, the inner critical list has `A0=A3`. Represent this
by flat index `A0` at fraction zero. The outer `B` section has four
positive edges and hence exactly one interior flat fraction. There
are nine choices of its flat index and the cyclic triangle match.
Their exact linear systems are either inconsistent or force that
outer fraction to an endpoint or outside `(0,1)`. The companion
checks all nine. Thus this zero edge also gives no coincident
boundary.

This completes the three strict upper orders and the inner zero-edge
case `P3=P4`.

## 5. The remaining zero edge: an outer triangle and backtracked segment

It remains to handle `P2=P3` while `A` is inner. Here `h2=0` and
`h1=h3=1/2`; in particular, write `P4=P3+(1/2)e` with `|e|=1`.
Let `q=1-alpha`. For every `t>alpha`, set

\[
r(t)=\frac{t-\alpha}{q},\qquad
\lambda(t)=\frac{1-t}{q},\qquad H=r(t)P_3,
\quad J=r(t)P_4.
\]

The outer limiting section is exactly a triangle together with the
segment `[H,J]` traversed out and back. Its triangle is

\[
T_t=H+\lambda(t)\operatorname{conv}
       \{0,\alpha P_3,\alpha P_3+qP_7\}.             \tag{9}
\]

The inner section is contained in `Tt union [H,J]`, not merely in
its convex hull. Indeed, away from this union the limiting outer
loop has winding number zero: its triangle is followed by a
backtracked segment. Winding number is unchanged under sufficiently
small uniform perturbations avoiding the point. If a limiting inner
point lay outside the union, a neighborhood of it would therefore be
outside every sufficiently far finite outer section, contradicting
finite nesting. This also covers a degenerate triangle in (9).

As `t` tends to one, `Tt` shrinks to `P3`, while `[H,J]` approaches
the nontrivial segment `[P3,P4]`. For `t>max(alpha,beta)`, the inner
section has two long edges parallel to `e`: the edge from `X` to
`Y`, of length `t/2`, and the edge from

\[
V_3=\frac{1-t}{1-\beta}P_5+
       \frac{t-\beta}{1-\beta}P_3
\quad\hbox{to}\quad
V_4=\frac{1-t}{1-\beta}P_5+
       \frac{t-\beta}{1-\beta}P_4.
\]

Each has a subsegment away from the shrinking triangle, so its
whole supporting line equals the line of `[H,J]`. The endpoints
`Y,Z` also tend to `P4`, remain outside `Tt`, and therefore lie on
`[H,J]`. Since

\[
V_3-X=\frac{1-t}{1-\beta}R_5,
\qquad Z-Y=(1-t)F,
\]

we obtain

\[
R_5=\eta\rho_5e,\quad F=\varepsilon h_6e,
\quad D:=\alpha P_3+qP_6=d e,
\qquad \eta,\varepsilon\in\{-1,1\}.                 \tag{10}
\]

Both signs are well defined because `rho5,h6>0`. The endpoint
condition `Y in [H,J]` gives one further scalar inequality:

\[
Y-J=\frac{1-t}{q}(d+\alpha/2)e,
\qquad d\le-\alpha/2.                              \tag{11}
\]

The four parallel-vector cases now follow directly from the circle
dot identities. Put `k=h6` and `qb=1-beta`.

| `eta` | `epsilon` | Necessary consequence |
|---:|---:|---|
| + | + | `h4=0`, `h5=1/2` |
| - | + | `h4=1/2`, `h5=1/2-k` |
| - | - | `h4=h5=1/2` |
| + | - | `h4=qb*k`, `h5=1/2-qb*k` |

Here `eta=+` first gives `h4+h5=1/2`; `eta=-` first gives
`h4=1/2`. The lower dot identity then gives the displayed values;
the factors `1-2k` and `1-2qb*k` are strictly positive.

In the two `epsilon=+` rows, the inner critical section (5)
traverses a segment of length `1/2` once in each direction. In the
first row its scalar coordinates are

\[
0,\ -\tfrac12,\ -q_b/2,\ -q_b(\tfrac12-k),
\]

and in the second row they increase from 0 through `rho5` and
`beta/2+rho5` to `1/2`, then return to 0. The convex-inner argument
in Section 4 would force the outer section onto that same segment,
contradicting the regular lower cap. The `eta=epsilon=-` row
consumes the whole pair-slack budget at `h4+h5=1`, also impossible.

In the last row `h4+h5=1/2`. The ray-2 total weight then gives
`h0=M`. The two critical `B` norms are therefore

\[
|\alpha P_3|=\alpha/2+qM,
\qquad |\alpha P_3+qP_7|=\alpha/2+qk.              \tag{12}
\]

But `F=-ke` and (10) make the second vector `(d-qk)e`.
By (11) its scalar is negative, so the second norm in (12) forces
`d=-alpha/2`. The first norm becomes

\[
|-(\alpha/2)e-qP_6|=\alpha/2+q|P_6|.
\]

Equality in this triangle inequality forces `P6` parallel to `e`.
Since `F` is already parallel to `e`, the lower cap is collinear,
contradicting (1). This disposes of the final zero-edge orbit.

## 6. Replay and exact scope

```sh
python research/type7_completion/remaining_c1_one_collinear.py /tmp/type7-c1-one-collinear
python research/type7_completion/solver_cnf_certificates.py /tmp/type7-c1-one-collinear-rup \
  --checker /path/to/solver-check-rup /tmp/type7-c1-one-collinear
```

The producer replays the original section-to-face bindings, all
section edge and perimeter identities, the finite turn formulas,
marked reflections and cap swaps, the actual-trit algebra, the three
positive affine dependencies, the outer-section decomposition and
all four parallel-vector metric cases. It additionally checks all
4+27 coincidence matches using only the regular lower area and the
nine zero-edge triangle matches. The finite nesting, winding,
convex-perimeter and support-function steps are the geometric proof
given above. Each of the eight source CNFs requires its independent
RUP certificate; producer SAT answers alone are not certificates.

The conclusion covers **every exactly-one-collinear-cap ray-2 C1
limit with both intermediate heights interior**. It does not infer
anything about a second collinear cap or a height endpoint.
