# Excluding the interior of the same-zero C1 orbit

No unbounded embedded ray-2 sequence has an interior C1 limit with

\[
h_2=h_6=0,\qquad 0<h_0<\tfrac12.
\]

This closes the open parameter interval of the EE orbit, and its
reflected FF orbit. The two scalar endpoints `h0=0,1/2` remain separate
cases. The proof retains unrelated rates of the two shrinking edges,
cap areas, and inverse height. Its five CNFs independently replay.

## 1. The two strict circle inequalities

Put `a=alpha`, `b=beta`, `r=h0`, and use the original C1 axis gauge
`P0=P1=0`. The zero edges, nearest lifts, and ray-2 total weight give

\[
h=(r,\tfrac12,0,\tfrac12,\tfrac12-r,\tfrac12,0,\tfrac12).
\]

Write

\[
P=P_2=P_3,\quad U=P_4-P_3,\quad V=P_6=P_7,
\quad R=P_5-bP-(1-b)V.
\]

Thus `|U|=|V|=1/2`, and `P5=bP+(1-b)V+R`. The
[closed circle identities](solver_remaining_c1_geometry.md) give

\[
\begin{aligned}
\rho&=a/2+(1-a)r,& |aP|&=\rho,
& aP\cdot(2V)&=a/2-(1+a)r,\\
\rho_5&=br+(1-b)/2,& |R|&=\rho_5,
&R\cdot(2U)&=2r-\rho_5.
\end{aligned}
\tag{1}
\]

Their exact squared perpendicular components are

\[
\begin{aligned}
\rho^2-[a/2-(1+a)r]^2&=4ar(1/2-r)>0,\\
\rho_5^2-(2r-\rho_5)^2&=4(1-b)r(1/2-r)>0.
\end{aligned}
\tag{2}
\]

Consequently `P,V` are independent and `R,U` are independent. These
identities and their original circle source are replayed by the
companion, using the preceding
[EE circle calculation](remaining_c1_zero_common.md).

## 2. The two annuli cannot have nested finite sections

Use section height `s=2z`; the intermediate vertices have heights
`a,b`. The checked section orders and source faces are those of
[the section theorem](remaining_c1_sections.md). We first show that
no subsequence of the finite embedded sections can be nested throughout
the height interval between the caps.

Suppose first that annulus A is inside annulus B. Above `a`, the
limiting B curve is a triangle plus a segment traversed out and back.
With

\[
H=\frac{s-a}{1-a}P,\qquad
J=\frac{s-a}{1-a}(P+U),\qquad
\lambda=\frac{1-s}{1-a},
\]

the triangle is

\[
T_s=H+\lambda\operatorname{conv}
\{0,aP,aP+(1-a)V\},
\tag{3}
\]

and the additional segment is `[H,J]`. Every limiting inner point
lies in `T_s union [H,J]`. Outside this closed set the limiting outer
curve has winding number zero, and uniform convergence preserves that
winding number in a neighborhood of any point outside it. Such a
neighborhood therefore cannot contain an inner point of sufficiently
far finite nested sections.

For `s>max(a,b)`, the A curve contains two edges parallel to U:

\[
\begin{aligned}
X&=(1-s)V+sP,&Y&=X+sU,\\
J_3&=\frac{1-s}{1-b}P_5+\frac{s-b}{1-b}P,
&J_4&=J_3+\frac{s-b}{1-b}U.
\end{aligned}
\]

As `s` tends to one, `T_s` shrinks to P while both displayed edges
have lengths tending to `1/2`. Each therefore has a nontrivial part
outside `T_s`, which must lie on `[H,J]`. Both supporting lines equal
the line of that segment. Since

\[
J_3-X=\frac{1-s}{1-b}R,
\]

this forces R parallel to U, contradicting (2).

If B is inside A, use sections near the lower cap instead. Below b,
the A curve is the triangle with vertices

\[
X=(1-s)V+sP,\quad
C=(1-s/b)V+(s/b)P_5,\quad
Y=X+sU,
\]

together with the segment from C to `(s/b)P5` traversed out and back.
Its triangle shrinks to V as `s` tends to zero, and that segment tends
to `[V,0]`. For small positive s, the inner B curve contains the two
nontrivial edges

\[
[sP,sP+(1-s)V],\qquad [0,(1-s/a)V].
\]

Both have parts outside the shrinking triangle. Their supporting
lines must therefore coincide with the line of the backtracked
segment. The second line is the line through V and the origin;
the first is its translate by sP. This forces P parallel to V,
again contradicting (2).

The companion checks both triangle-plus-segment decompositions,
the two long edges in each argument, and their exact differences
against the original section formulas. No assertion of convexity of
an arbitrary limiting quadrilateral is needed.

## 3. Both virtual cap edges are parallel to the long cap edges

The [relative short-edge lemma](remaining_c1_short_edges.md) gives
unit limits

\[
w=\lim\frac{P_3-P_2}{h_2},\qquad
v=\lim\frac{P_7-P_6}{h_6},
\]

and normalized axial differences `O(t h2)` and `O(t h6)`, where
`t=1/y²`. These estimates hold at the respective edge's own scale.

If w and U were independent, solve for the height gradient of the
finite plane 234 on the transverse vectors `(P3-P2)/h2` and
`P4-P3`. Both axial differences, after the same first-edge division,
are `O(t)`, while the transverse basis has an invertible limit.
The gradient is therefore `O(t)`. Flatten that cap plane by a
vanishing height shear. Every other vertex remains below it, and
the two finite section cycles near it are nested. The checked annulus
faces and intermediate vertex links keep them nested at every fixed
interior height. This contradicts Section 2. The same argument at
cap 067 excludes independence of v and V.

Hence, for two signs `eta,theta in {-1,+1}`,

\[
w=2\eta U,\qquad v=2\theta V.
\tag{4}
\]

This step uses the finite-section nesting argument already employed
in the [opposite-zero proof](remaining_c1_opposite_zero.md), with its
independent-edge relative bounds. It does not assume a cap's unscaled
area is bounded away from zero.

## 4. The complete normalized sign cover

Use the four transverse vectors `(P,U,V,R)` and their six actual
cross products. Orient the ambient transverse plane so that
`cross(P,V)>0`, possible by (2). For every original four-point
determinant, use its own positive divisor:

| Pairs contained in the determinant | Divisor |
|---|---|
| Neither 23 nor 67 | 1 |
| 23 only | `h2` |
| 67 only | `h6` |
| Both, namely 2367 | `h2*h6` |

The companion expands all seventy direct three-dimensional
determinants for each choice in (4), including formal axial errors
`t*h2*axial23` and `t*h6*axial67`. It factors the actual edge columns
before dividing. The quotients have no short-edge denominators, and
their remaining axial-error terms vanish with t independently of the
two edge lengths. This verifies the simultaneous normalization.

Every resulting determinant is a linear combination of the six cross
products with coefficients of uniform sign on `0<a,b<1`. No relation
is omitted. The CNFs impose the actual rank-two Pluecker identity,
retain zero cross products and zero normalized determinants, and link
each nonzero normalized determinant to one common generic source.
They impose no affine cocycle between differently normalized minors.

Three independently replayed CNFs exclude the direction pairs
`(-,-)`, `(-,+)`, and `(+,+)`. A fourth forces the remaining pair
`(+,-)` to have exactly

\[
\begin{array}{c|rrrrrr}
&P\times U&P\times V&P\times R&U\times V&U\times R&V\times R\\
\hline
\text{sign}&0&+&-&-&+&+
\end{array}.
\tag{5}
\]

In particular P is a negative multiple of U. The exact norms in (1)
give `P=-(2rho/a)U`.

## 5. The two circles contradict the remaining pattern

Rotate so that `U=(1/2,0)`. Equations (1), (2), and (5) fix the signs
of the two remaining perpendicular components. Put

\[
g=2\sqrt{ar(1/2-r)}>0,\qquad
q=\sqrt{(1-b)/a}>0,\qquad k=\frac{r}{1/2-r}>0.
\]

Thus `b=1-aq²`. Divide the second transverse coordinate by g, a
positive-determinant change. The four vectors become

\[
\begin{aligned}
P&=(-\rho/a,0),&U&=(1/2,0),\\
V&=\left(-\frac{a/2-(1+a)r}{2\rho},-\frac1{2\rho}\right),
&R&=(2r-\rho_5,q).
\end{aligned}
\tag{6}
\]

Multiplying all six cross products by the common positive factor
`4a rho (1+k)²` gives, in the order of (5),

\[
\begin{aligned}
C_{01}&=0,&C_{02}&=(a+k)(1+k),\\
C_{03}&=-(a+k)^2q,&C_{12}&=-a(1+k)^2,\\
C_{13}&=a(a+k)q(1+k),
&C_{23}&=a(1+q)(k-aq)(1+k).
\end{aligned}
\tag{7}
\]

The last sign in (5) therefore gives `k>aq`. The checker verifies
(6)--(7) symbolically and substitutes them into all seventy
normalized determinants from Section 4. Every nonzero determinant
factors into known strictly signed factors and at most one of five
polynomials:

\[
\begin{aligned}
f_1&=akq+aq-a-k,\\
f_2&=-a^2q+akq^2+akq+ak-a-k,\\
f_3&=kq-1,\\
f_4&=akq+ak+aq-k,\\
f_5&=ak^2q^2+akq^2-2akq-aq+kq-k-1.
\end{aligned}
\]

Each `fi` receives a free actual sign trit, including zero. All
occurrences of the same polynomial use that same trit. The known
signs use only `0<a<1`, `q,k>0`, and `k>aq`; for example
`aq-k-q-1=(a-1)q-k-1<0`. No numerical sign test is used.

The fifth CNF is UNSAT even with these five polynomial signs left
otherwise arbitrary. When a factor vanishes, the corresponding
normalized determinant vanishes and its original generic sign is
left free. Thus the argument includes all zeros of all five
polynomials. It contradicts the final possibility (5), completing
the EE interior exclusion.

## Verification and scope

```sh
python research/type7_completion/remaining_c1_same_zero.py /tmp/type7-c1-same-zero
python research/type7_completion/solver_cnf_certificates.py /tmp/type7-c1-same-zero-rup \
  --checker /tmp/type7-rup-check /tmp/type7-c1-same-zero
```

Fresh generation took 3.708 seconds and all five distinct RUP proofs
independently passed in 0.357 seconds in this workspace. The producer
binds the original section faces and links, both strict Gram
identities, all four seventy-determinant normalizations including
the independent double-edge case, and all final factorizations.
The nesting and winding arguments above are geometric proof steps.

The reflected FF interior follows from the already checked marked
reflection. The four scalar EE endpoint families, other zero-edge
orbits, all height endpoints, and ray-2 C0 remain outside this
package's claim. This is a research exclusion, not a Lean theorem
or a numerical eventual-height bound.
