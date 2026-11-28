# Ray-2 C1: opposite zero edges force parallel cap directions

Consider an interior ray-2 C1 limit with

\[
h_2=h_7=0,\qquad 0<\alpha,\beta<1.
\]

The two cap directions `E3=P4-P3` and `P6` must be parallel. Thus the
nonparallel part of the zero-edge orbit EF is excluded. The proof
combines the relative short-edge estimate, finite embedded sections,
and four independently replayable CNFs. Parallel EF and the other
zero-edge orbits remain separate cases.

## 1. The exact nonparallel limiting family

Assume for a contradiction that `U=E3` and `V=P6` are independent.
Nearest lifts and the ray-2 total give

\[
h_0=h_1=h_3=h_6=\tfrac12,\qquad h_4+h_5=\tfrac12.
\]

Write `W=alpha P3`. The
[closed C1 circle identities](solver_remaining_c1_geometry.md) imply

\[
|W|=|U|=|V|=\tfrac12,
\qquad R_5=2h_5U,\qquad Y_5=(\beta-2h_5)U.
\]

Since `F=-V`, its lower dot identity factors as

\[
(\beta-2h_5)(U\cdot V+\tfrac14)=0.                \tag{1}
\]

Independence gives `U dot V > -1/4`, so

\[
h_5=\beta/2,\quad h_4=(1-\beta)/2,\quad Y_5=0.
\]

The complete transverse coordinates are therefore

\[
\begin{aligned}
P_0=P_1=P_7&=0,& P_2=P_3&=W/\alpha,\\
P_4&=W/\alpha+U,& P_6&=V,\\
P_5&=\beta P_4+(1-\beta)V.
\end{aligned}                                                     \tag{2}
\]

The companion checks the exact factorization (1). No strict sign is
assigned to an original zero determinant in (2).

## 2. These limiting annulus sections cannot be nested

Use the two annuli and the exact section orders from the
[section source package](remaining_c1_sections.md). Choose any fixed
`0<t<min(alpha,beta)`. Substitution of (2) gives the following two
sets traced by the limiting section curves:

\[
\begin{aligned}
T_B(t)&=[0,(t/\alpha)W]\ \cup\ [0,(1-t/\alpha)V],\\
T_A(t)&=[Q(t),Q(t)-tU]\ \cup\ [Q(t),Q(t)-(1-t)V],\\
Q(t)&=t(W/\alpha+U)+(1-t)V.
\end{aligned}                                                     \tag{3}
\]

Both closed curves backtrack along their two segments. In the A
section, the repeated intermediate point is

\[
J=(t/\beta)P_5=Q(t)-(1-t/\beta)V,
\]

which lies on its V-segment because `0<t<beta<1`. The companion
checks all twelve vertices against (3) and replays their original
face, edge, annulus-boundary, and vertex-link bindings.

Suppose a sequence of the finite section curves is nested. Any
limit point of the inner curve must belong to the outer limiting
tree. Indeed, outside that tree the winding number is zero for its
backtracking limit, and remains zero for all sufficiently late
finite curves. This contradicts being inside the finite outer
polygon. Thus one of the two trees in (3) must contain the other.

If W and V are independent, each tree consists of two nonparallel
segments meeting only at their corner. Both have total segment
length `1/2`:

\[
t|U|+(1-t)|V|=\tfrac12,
\qquad (t/\alpha)|W|+(1-t/\alpha)|V|=\tfrac12.
\]

Containment of these closed finite unions with equal length forces
equality. Equality identifies their unique corners, giving `Q(t)=0`.
Nesting at two distinct heights in `(0,min(alpha,beta))` would
therefore give two zeros of the affine vector function Q. That
would make its constant term V zero, a contradiction.

If W and V are parallel, `T_B(t)` is a nontrivial segment on the
line through V and the origin. The noncollinear A tree cannot lie
in that line. Conversely, the only A segment parallel to it is the
V-segment, whose supporting line has transverse displacement `tU`
from the V-line. Since U and V are independent, that supporting
line does not meet the V-line. Hence B cannot lie in A either.

Consequently the finite sections cannot have a nesting order
persisting through the stated open range of heights.

## 3. A regular virtual cap would force precisely that nesting

By the [relative short-edge lemma](remaining_c1_short_edges.md), pass
to a joint subsequence with unit vectors

\[
w=\lim\frac{P_3-P_2}{h_2},\qquad
v=\lim\frac{P_7-P_0}{h_7}.                         \tag{4}
\]

The corresponding normalized axial differences are `O(t_n h2)`
and `O(t_n h7)`, where `t_n=1/y_n^2`. This use of `t_n` is separate
from the fixed section parameter t in (3).

If w is independent of U, the finite plane through 234 has height
gradient `O(t_n)` in transverse coordinates. To see this, solve
for its gradient on the two transverse vectors
`(P3-P2)/h2` and `P4-P3`. They converge to the independent vectors
w and U, while the two corresponding axial differences, after
the same division by h2 in the first, are `O(t_n)`. The estimate
on edge 34 follows from the same relative lemma.

Flatten this finite cap plane by its height shear. The shear tends
to zero; every other vertex remains strictly below the upper cap,
and the limiting section formulas (3) are unchanged. Near that cap
the two finite section polygons both surround its interior. They
are disjoint simple polygons, so they are nested. Their nesting
persists down to every fixed height used in (3): the two annuli
are embedded and disjoint, and the checked intermediate vertex
links have contiguous upper and lower neighbors. Crossing either
intermediate height cannot split or join a section cycle.

This contradicts Section 2. The same argument at the lower cap,
using its edges 07 and 06, applies if v is independent of V. Any
generic perturbation used to choose a completion can be taken
small enough to preserve all these relative estimates.

Thus both virtual directions are parallel to their long edges.
Their norms give two signs `eta,theta in {−1,+1}` such that

\[
w=2\eta U,\qquad v=2\theta V.                    \tag{5}
\]

## 4. One generic source for all seventy normalized determinants

Choose the ambient orientation so that `cross(U,V)>0`. The
companion retains the full necessary generic embedding/linking
formula, with only its freely chosen ambient-orientation unit
removed. It introduces actual cross-product trits for the five
transverse vectors

\[
P_3,\ P_4,\ P_6,\ w,\ v.
\]

Their rank-two three-term identities are imposed, including every
zero case. Since U,V span the plane and each virtual vector is
nonzero, each has a nonzero cross product with at least one of
`P3,P4,P6`.

For every original four-point determinant, use its own necessary
normalization:

| Vertices contained | Positive divisor |
|---|---|
| Neither full pair 23 nor full pair 07 | 1 |
| Pair 23 only | `h2` |
| Pair 07 only | `h7` |
| Both pairs, namely 0237 | `h2*h7` |

The relative estimates justify all these limits simultaneously.
For instance `[0237]/(h2*h7)` tends to `cross(w,v)/2`. The checker
derives all seventy forms by inserting independent formal edge
lengths, verifies their direct three-dimensional determinants in
arbitrary transverse coordinates, divides by the displayed factors,
and only then sets those two lengths to zero. It binds every
nonzero normalized trit to the same original generic completion.

Each resulting form is linear in the ten transverse cross
products. Its coefficients have exact uniform signs in the open
height square, certified by multilinear interpolation. One form
with a variable-sign coefficient is omitted entirely. The retained
zero-sum conditions relax positive coefficient magnitudes, which
only weakens the necessary system.

Affine cocycles between differently normalized determinants are
not imposed. The rank-two relations above concern the actual five
transverse vectors, so they have no such scale mismatch.

The first independently replayable CNF proves the exact sign cover

\[
\bigl(\operatorname{sgn}(P_3\times w),
      \operatorname{sgn}(P_3\times v),
      \operatorname{sgn}(w\times v)\bigr)
\in\{(-,0,+),(0,0,+),(0,+,+)\}.                  \tag{6}
\]

In particular `cross(w,v)>0`. By (5), `eta*theta=+1`.
The second CNF excludes the positive choice `eta=theta=+1`.
It adds exactly the cross-product relations following from
`w=2(P4-P3)` and `v=2P6`, again retaining zero cases.

It remains to consider `eta=theta=-1`. By (6),

\[
P_3\times U\ge0,\qquad P_3\times V\le0,
\qquad (P_3\times U)(P_3\times V)=0.              \tag{7}
\]

Since P3 is nonzero and U,V are independent, (7) means that P3
is a negative multiple of U or a negative multiple of V. The
already proved norms `|alpha P3|=|U|=|V|=1/2` therefore give

\[
W=-U\qquad\text{or}\qquad W=-V.                 \tag{8}
\]

## 5. Both negative alignments contradict the original source

The final two CNFs exclude the two alternatives in (8) using only
strict original limiting minors. For `W=-U`, an orientation-preserving
linear transverse change of coordinates puts

\[
U=(1,0),\quad V=(\xi,1),\quad W=-U.
\]

For `W=-V`, use

\[
V=(1,0),\quad U=(\xi,-1),\quad W=-V.
\]

The affine relations (2) remain exact. Unit lengths need not be
preserved after this change; they were used only to establish (8).
In each case, all determinant signs are independent of xi. After
multiplication by the positive alpha, every nonzero determinant
factors into uniformly signed polynomials on `0<alpha,beta<1`.
The checker verifies the factorizations and coefficient signs.

Each alternative supplies 32 strict original minor signs. Each
resulting generic formula is UNSAT. Zero minors remain unrestricted.
Together with (6) and the positive-direction exclusion, this
contradicts every possibility in (5), proving that U,V cannot be
independent.

## Reproduction and scope

```sh
python research/type7_completion/remaining_c1_opposite_zero.py /tmp/type7-c1-opposite-zero
python research/type7_completion/solver_cnf_certificates.py /tmp/type7-c1-opposite-zero-rup --checker /path/to/solver-check-rup-watched /tmp/type7-c1-opposite-zero
```

All four exported CNFs require independent replay. The conclusion
is the parallel-direction reduction for interior ray-2 EF. No
comparison between the two shrinking edge lengths, t, a cap area,
or a further transverse deviation was used. Parallel EF, the other
zero-edge orbits, ray-2 C0, and the height endpoints are outside this
package's exclusion claim.
