# Parallel cap lines in the remaining single-zero C1 orbits

Every interior ray-2 C1 limit in either orbit EB or ED has parallel
cap lines. Together with the previous EA, EC, EF, and EE results,
this closes the remaining nonparallel single-zero cap configurations.
Parallel EB/ED configurations still require further analysis.

The proof uses the relative direction of the actual shrinking edge
23, finite embedded sections, and seven independently replayable CNFs.
It includes all values of the outer weights, including zero, and
requires no comparison between any collapse rates.

## 1. Coordinates and finite-section obstruction

Put `a=alpha`, `b=beta`, `P=P2=P3`, `U=P4-P3`, and let `2V` be
the unit direction of the lower line. Thus `|U|=|V|=1/2`.
The two cases are

| Order | `P7` | `P6` | Cap weights |
|---|---|---|---|
| EB | `V` | `(1-2ell)V` | `h7=1/2`, `h6=ell`, `0<ell<1/2` |
| ED | `2kV` | `V` | `h7=k`, `h6=1/2-k`, `0<k<1/2` |

In both cases write `R=P5-bP-(1-b)P6`. Suppose U and V are
independent. We show first that the two finite annulus sections cannot
be nested throughout the interval between the caps.

If A is inner and B is outer, use the
[upper triangle plus backtracked segment](remaining_c1_one_collinear.md#5-the-remaining-zero-edge-an-outer-triangle-and-backtracked-segment).
The outer triangle shrinks to P near the upper cap, while the inner
curve has two long edges parallel to U. Winding stability forces the
parts outside that triangle onto the outer segment. The two inner
vertices tending to `P4` also lie on it. Their difference is
`(1-s)(P7-P6)`, where s is section height. Thus `P7-P6` is parallel
to U. It is a nonzero multiple of V in both EB and ED, a contradiction.
The companion replays the original general section and spur identities.

Suppose B is inner. At its critical height a, its limiting section
is the triangle with vertices

\[
0,\quad aP,\quad aP+(1-a)P_7.
\tag{1}
\]

Its perimeter is one. Finite nesting, convex-hull perimeter monotonicity,
and the outer section's perimeter one force the outer curve to traverse
the same convex boundary. If (1) is a segment, it is on the lower line;
the outer A section has a nonzero edge parallel to U, contradicting
independence. Hence the common boundary is a nondegenerate triangle.

The two common B vertices `sP` and `sP+(1-s)P7` are genuine corners.
The support-function tracking argument from the
[regular section theorem](remaining_c1_sections.md#5-different-critical-heights-are-impossible)
applies to them. If `a<b`, the first tracks outer edge 05, giving
`P5=bP`. The second must track 47 or 57; the former gives `P4=P`,
and the latter gives `P5=bP+(1-b)P7`. Both are impossible. Here 05
is the unique outer trajectory ending at zero at the lower cap,
because `P6,P7` are distinct and nonzero.

If `a>b`, the two corners both tend to P at the upper cap. The
outer trajectories ending at P are 36 and the common trajectory
35=25. They must track distinct ones, so one tracks 36. This gives
`P6=0` or `P6=P7`, both impossible in EB and ED.

Therefore `a=b`. The outer A critical quadrilateral has four positive
side lengths: `rho5`, `b/2`, `(1-b)h6`, and `tau5`. Positivity of
`rho5,tau5` follows from `h5>=1/2-h6>0` and `h6<1/2`.
Its distinguished vertex A1 is a genuine corner: the strict-corner
decomposition in the section theorem has the positive term
`2h5(1-b)(1/2-h6)(1-b)` when `h3=1/2`.

The common triangle therefore has exactly one flat A vertex, among
`A0,A2,A3`. Use the clockwise lists of the section theorem, with
`B1=B2`. The exact relation is

\[
A_0+A_2-A_3=B_1-B_2+B_3=B_3.
\tag{2}
\]

There are nine matches: three flat A indices and three cyclic triangle
matches. The companion solves their two-coordinate affine equations
exactly. Five are inconsistent; the other four put the flat vertex
at an endpoint, contradicting its two positive adjacent side lengths.
Thus B cannot be inner either.

The [relative short-edge theorem](remaining_c1_short_edges.md) gives a
unit vector `w=lim(P3-P2)/h2` and axial difference `O(t h2)`.
If w and U were independent, flattening the finite cap plane 234
would require only an `O(t)` height shear. Near that cap the two
finite section cycles are nested, and their nesting persists through
the intermediate vertex levels. The preceding obstruction excludes
this. Consequently

\[
w=2\eta U,\qquad \eta\in\{-1,+1\}.
\tag{3}
\]

## 2. Complete zero-safe normalized sign covers

Orient the transverse plane so that `U cross V>0`. Use the four
vectors `(P,U,V,R)`. For every original determinant containing 23,
factor and divide by the positive actual edge length h2 before
passing to the limit. Leave the other determinants unscaled.
The checker independently expands all seventy determinants, retains
the formal axial term `t*h2*axial23`, and verifies that no h2
denominator survives. Every nonzero limit binds to the same original
generic completion; zeros leave that sign free.

The actual cross-product trits satisfy their rank-two Pluecker
identity. Because `|aP|=a/2+(1-a)h0>0` and U,V span the plane,
at least one of `P cross U`, `P cross V` is nonzero. All coefficient
signs are checked exactly on the open height and cap-length box.
One variable-sign relation is omitted in EB and none in ED.

The four source CNFs give this complete cover, in cross-product order
`(P cross U,P cross V,P cross R,U cross V,U cross R,V cross R)`:

| Case | Remaining actual sign patterns |
|---|---|
| EB, `eta=-1` | None |
| EB, `eta=+1` | `(+,-,-,+,+,0)` |
| ED, `eta=-1` | `(+,0,0,+,-,0)` |
| ED, `eta=+1` | `(+,0,0,+,0,0)` or `(0,-,+,+,-,-)` |

No original limiting zero minor is made strict. The consequences
of these patterns are dealt with below.

## 3. The ED boundary patterns and interior cone

Put `r=h0`, `p=1/2-r`. The first circle has

\[
\rho=\tfrac12-(1-a)p,\qquad
aP\cdot(2V)=p/k-\tfrac12-(1-a)p,
\]

and the exact Gram difference

\[
\rho^2-[p/k-\tfrac12-(1-a)p]^2
=\frac{p(k-p)[1-2(1-a)k]}{k^2}.
\tag{4}
\]

Nearest lifts give `0<=p<=k`. In either boundary pattern, P is a
negative multiple of V. Equation (4) then forces `p=0`, so `r=1/2`
and `P=-V/a`; the other zero `p=k` gives a positive multiple and
cannot occur.

Write `d=1/2-h4`. At `r=1/2` the second circle gives
`|R|=d` and `R dot (2U)=d`. Thus `R=2dU` by Cauchy equality.
For `eta=-1`, the sign pattern makes R a nonzero negative multiple
of V, contradicting independence of U,V. For the boundary pattern
with `eta=+1`, it makes R zero, hence `d=0`. Substitution of
`P=-V/a,R=0` into the normalized determinants gives a fifth UNSAT
CNF. The checker retains all uniformly strict factors and omits
exactly two variable-sign minors.

The remaining ED pattern gives

\[
P=-xU,\qquad R=yU-zV,\qquad x,y,z>0.
\]

Since `r>=1/2-k>0`, the first norm identity yields

\[
x=\frac{2\rho}{a}=1+\frac{2(1-a)r}{a}>1.
\tag{5}
\]

Section 5 below excludes this entire cone by one factor-sign CNF.

## 4. The EB metric forces a cone coefficient greater than one

The sole EB sign pattern gives

\[
P=-xU-yV,\qquad R=zV,\qquad x,y,z>0.
\tag{6}
\]

Put `r=h0`, `d=1/2-h4`, `rho5=|R|`, and
`c=(2U) dot (2V)`, so `-1<c<1`. The ray-2 budget gives
`h4+h5=1-r-ell`. The radius definition and two circle dot identities
give

\[
\begin{aligned}
\rho_5(1-c)&=2(1-b)(1/2-r-\ell),\\
2r&=\rho_5(1+c-4\ell)-b\ell(1-c).
\end{aligned}
\tag{7}
\]

Their positive denominator is

\[
D=2-b(1+c)-4(1-b)\ell
=b(1-c)+2(1-b)(1-2\ell)>0,
\]

and solving gives

\[
\rho_5=\frac{(1-b)[1-2\ell+b\ell(1-c)]}{D}.
\]

With `s=(1-c)/2` in `(0,1)`, exact substitution gives

\[
4D\left(\frac{1+c}{4}-r\right)
=8(1-b)\ell(1-2\ell)
 +4bs[1-(1-2\ell)s]>0.
\tag{8}
\]

Thus `r<r_max=(1+c)/4`. The first circle yields

\[
x^2=F(r):=\frac{16r(1/2-r)}{a(1-c^2)}.
\tag{9}
\]

There is also a strict lower bound on r from the positive cone (6).
The direction of `-P=xU+yV` lies strictly between the two independent
unit directions `2U,2V`. Its angle with `2V` is strictly smaller
than theirs, so

\[
\frac{(1+a)r-a/2}{a/2+(1-a)r}>c,
\qquad
r>r_{\min}:=\frac{a(1+c)}{2[(1+a)-(1-a)c]}.
\tag{10}
\]

The function F is strictly concave. The companion checks

\[
F(r_{\max})=1/a>1,\qquad
F(r_{\min})=
\left(1+\frac{2(1-a)r_{\min}}a\right)^2>1.
\]

Since (8) and (10) put r strictly between these two endpoints,
concavity gives `x²>1`, hence **x>1**. This uses the complete open
parameter domain; it does not sample the height parameters or assume
an edge length bounded away from zero in the original sequence.

## 5. Exact factor-sign contradictions

Apply a positive-determinant transverse linear map sending U,V to
the coordinate basis. In EB the six cross products become

\[
(y,-x,-xz,1,z,0),
\]

and in ED they become

\[
(0,-x,xz,1,-z,-y).
\]

Here `x>1,y,z>0` in both cases. The checker substitutes these exact
expressions into all seventy normalized determinants and factors
the resulting polynomials. It verifies each factorization exactly.
Uniform coefficient signs are checked by multilinear interpolation
in `a,b,ell` or `a,b,k`, and by positive monomials in `x,y,z`.
The factor `x-1` is positive by (5) or Section 4.

The other irreducible factors receive free actual sign trits: seven
in EB and eight in ED. Identical factors in different determinants
share a trit; products use their exact three-valued sign multiplication.
Zeros remain free generic completions. In ED the resulting formula
is already UNSAT.

For EB two of the seven factors are

\[
f=-ay+2a\ell-a-2\ell+1,\qquad g=ay+a-1.
\]

Their exact identity `f+g=2ell(a-1)<0` requires at least one to be
negative. Adding just this necessary clause makes the EB formula
UNSAT. All other free polynomial signs remain unconstrained.
These are the final two independently replayable CNFs.

## Replay and scope

```sh
python research/type7_completion/remaining_c1_single_zero_nonparallel.py /tmp/type7-c1-single-zero
python research/type7_completion/solver_cnf_certificates.py /tmp/type7-c1-single-zero-rup \
  --checker /tmp/type7-rup-check /tmp/type7-c1-single-zero
```

The exact producer checks the original annulus source, general
zero-edge spur identities, nine equal-height triangle matches,
the metric bounds in Sections 3--4, all four seventy-determinant
normalizations, and both factor-sign systems. The geometric nesting,
winding, support-function, and cone-angle arguments are supplied
above. All seven CNFs require independent replay.

The conclusion is that **EB and ED must have parallel cap lines**.
The marked symmetry transports it to their eight order labels.
The parallel cases, remaining common-line families, height endpoints,
and ray-2 C0 are not excluded here. No numerical eventual bound or
Lean theorem is claimed.
