# Ray 3: a triple cluster cannot face a cap with one zero weight

## Result and scope

Consider a common-line ray-3 sequence whose first normal blow-up has
one collinear cap and one noncollinear cap. Suppose exactly two adjacent
weights in the collinear cap and exactly one weight in its partner
vanish. Such a sequence is impossible. All relative rates of the three
small lengths, the normal width, and `t=1/y²` are allowed.

The complete degenerate-norm cover has 304 such cells. The marked
symmetries reduce them to 38 shapes. The three possible ratios of the
two cluster-edge stretched norms give 114 cases. The necessary sign
formula excludes 78 cases directly; a third independently normalized
edge direction excludes twelve more. The remaining twenty-four reduce
to six metric endpoint arguments, with two ratios and their mirrors.

This extends `remaining_cluster_blowup.md`. It excludes the stated
three-zero stratum; it does not give a numerical height bound or a
complete Type 7 theorem.

## 1. Finite directional cover

Use the notation and factored determinants of the two-zero cluster
proof. In canonical labels the collinear cap is
`A=(0,1,4,5)=(0,0,0,1/2)` and the partner is `B=(2,3,6,7)`.
Normalize `a=01` and `b=14` by their own stretched norms. The three
cases are a dominant, comparable, or b dominant. Sum-sign rules in
the comparable case retain cancellation and every zero leading sign.

When the zero-weight B edge also has coincident stretched endpoints,
normalize that actual edge separately as `c=(cx,cy)`. Its scale is
independent of both cluster-edge scales. Add the rank-three determinant
identities of nine homogeneous points: E, F, a, b, c at infinity and
the four B vertices. The symbolic determinants yield eleven linear
c-forms and three bilinear forms `det(a,c)`, `det(b,c)`, and
`det(a+b,c)`. Each has the actual small edge, or both actual small
edges, as factored rows. Relative axial errors are therefore `O(t)`
after division by these same edge scales; no absolute coordinate error
is divided by an uncontrolled smaller length.

The complete necessary orientation/linking formula allows either
global orientation. All auxiliary signs are trits, including zero.
The twelve surviving normalized implication certificates force

\[
 a_x<0,\quad a_y\le0,\quad b_x>0,\quad b_y=0.       \tag{1}
\]

The mirror `(0 4)(2 6)` exchanges the two cluster edges and reverses
their dominance. After this mirror, the B vertical weak order is
`(0,1,1,0)`. The following table lists all six surviving forms; x is
the B horizontal weak order and beta its four triangle signs.

| x | beta | Endpoint after relabeling | Third direction |
|---|---|---|---|
| `(1,2,2,0)` | `(0,1,1,0)` | Flat `z=1/2` | Original 36 points horizontally negative |
| `(2,1,1,0)` | `(0,1,1,0)` | Exceptional `z=a` | Original 36 points horizontally negative |
| `(0,2,1,0)` | `(1,0,0,1)` | Flat `u=0` | Original 72 points horizontally positive |
| `(1,2,0,0)` | `(1,1,1,1)` | Flat `z=0` | Zero edge is vertical in the stretched plane |
| `(2,1,0,0)` | `(1,1,1,1)` | Exceptional `z=0` | Zero edge is vertical in the stretched plane |
| `(2,2,1,0)` | `(1,1,1,1)` | Flat `u=1/2` | Zero edge is vertical in the stretched plane |

In the comparable hierarchy the implication also forces the limiting
trit `a13=sign det(a,B7-B3)` to be positive. The zero trit is explicitly
excluded. This is needed for the strict limiting slope bounds below.
The four required Farkas signs from the cluster proof are included in
each combined implication certificate.

## 2. Shared metric setup

Relabel by `(5,0,3,6,1,4,7,2)`. The cluster is now `0,1,5`, with tip
4. Use the face-023 metric gauge, writing incidence coordinates as
`(P,Z,c-2tH)` with `P=-U` and `H=zeta`. Put

\[
 \delta=Z_6>0,\qquad Z_7/\delta\to1,\qquad
 Z_1/\delta,Z_4/\delta,Z_5/\delta\to0.
\]

Define actual positive lengths and signed defects

\[
 r=h_{01},\quad \beta=h_{50}=x_5+\tfrac12,\quad
 p=r+U_1,\quad q=\beta+U_5.                       \tag{2}
\]

The forced directions (1), including their nonzero horizontal
components, imply

\[
 U_1/r\to-1,\quad Z_1=o(\delta r),\qquad
 U_5/\beta\to-1,\quad Z_5=O(\delta\beta).          \tag{3}
\]

These statements compare the stretched norm with the physical weight
before using a relative height estimate. In particular, no relation
between beta, r, and delta has been assumed.

All but the `u=0` row have a positive limiting anchor length 23. In
that row the third-direction certificate says that the actual edge
23, divided by its own stretched norm, is horizontal with positive P
component. Thus its physical horizontal component divided by `h23`
tends to one and its normal component is `o(delta h23)`. Rotating the
transverse coordinates to place this edge in the face plane changes
their angle by `o(delta)`. This preserves the displayed limiting normal
profile. The axial error divided by the same edge length is `O(t)`.
Consequently the exact face gauge and its relative height bounds remain
valid at this endpoint; no inverse power of `h23` occurs in a remainder.

The two exact identities used throughout are

\[
 (1-2t\gamma_3)(H_1-\gamma_1)=2x_3p,
\]

\[
 p\left[(r-U_1)-
 \frac{2tx_3(H_1+\gamma_1)}{1-2t\gamma_3}\right]=Z_1^2,
 \qquad
 q(\beta-U_5)=Z_5^2+t(H_5-\gamma_5)(H_5+\gamma_5). \tag{4}
\]

The first bracket is at least r eventually, and
`|H5+gamma5|≤C beta`. Therefore

\[
 0\le p=o(\delta^2r),\qquad
 |q|\le C\delta^2\beta+Ct|H_5-\gamma_5|.           \tag{5}
\]

The second estimate uses both conclusions about edge 50 in (3), not
only a bound for its negative defect.

### Regularized equations and necessity

Replace the squared metric equations for 01 and 50 by their signed
defect definitions. In the five rows with an additional non-anchor
zero edge, replace that edge equation by its signed defect as well.
Retain all other metric equations. There are twenty-one equations for
twenty-one dependent planar variables and three chosen free intrinsic
parameters. Every actual configuration satisfies this system with its
own defects.

The intrinsic stress necessity system and the cross-edge height system
from `remaining_cluster_blowup.py` have identical constant coefficient
matrices for the flat and exceptional families, of ranks fourteen and
five respectively. Their checked substitutions identify the actual
planar limit uniquely, also at all endpoints considered here. The
reference is therefore forced by the metric constraints.

The Jacobians listed below are nonzero in the stated open intervals.
The implicit solutions are analytic jointly in t, the free parameters,
the signed defects, and all five normal coordinates, with bounded
derivatives in a fixed neighborhood of each proposed limit. Dependence
on the normal coordinates is even under simultaneous `Z -> -Z`.
Planar normal corrections begin quadratically with remainder `O(|Z|⁴)`;
the bracket functional is linear in Z at fixed planar coordinates,
giving cubic corrections and remainder `O(|Z|⁵)`. Differences in defects
factor those defects by analytic integration. These estimates never
divide by t, delta, or a collapsed weight.

### A nonnegative bracket functional

The necessary signs are
`-[0124]≥0`, `[0146]≥0`, `[0345]≥0`, `[1256]≥0`.
Their combination L has weights

\[
 ((1-2u)N/D,\ 2uN/D,\ N/D,\ 1),\quad
 N=4+t(4r-1)^2,\quad D=4+t(32ru-8r-8u+1),          \tag{6}
\]

where `u=h23` is its actual finite value. Always `0<u<1/2` and `D>0`,
so `L≥0`, even when u tends to an endpoint. At `t=0` and the limiting
normal profile, its planar first variation divided by delta is the
first variation of `U1-U5`.

## 3. Reference families and exact coefficients

The flat family, valid for every r,u,z,t, is

\[
\begin{aligned}
 P&=(0,r,0,u,\tfrac12,r,\tfrac12,z),\\
 x&=(0,-r,0,-u,0,r-\tfrac12,0,z-\tfrac12),\\
 \gamma=H&=(0,r/2,g_2,g_2+du,r-\tfrac14,r/2,
                         g_2+d/2,g_2+dz),\\
 g_2&=r-\tfrac18,\qquad d=\tfrac12-2r.
\end{aligned}                                                    \tag{7}
\]

Choose actual free parameters `r=-x1`, `u=x2-x3`,
`z=x7-x2+1/2`. Its reference functional is exactly

\[
 L_{\rm flat}=-4r(\tfrac12-r)u\,t(N/D)\delta\le0.  \tag{8}
\]

The exceptional family, valid at `r=0` for every a,z,t, is

\[
\begin{aligned}
 P&=(0,0,0,\tfrac12,\tfrac12,0,a,z),\\
 x&=(0,0,0,-\tfrac12,0,-\tfrac12,a-\tfrac12,z-\tfrac12),\\
 \gamma=H&=(0,0,-\tfrac18,\tfrac18,-\tfrac14,0,
                               a/2-\tfrac18,z/2-\tfrac18).
\end{aligned}                                                    \tag{9}
\]

Choose actual parameters `r=-x1`, `a=x6-x2+1/2`, `z=x7-x2+1/2`.
Its reference functional is

\[
 L_{\rm exc}=
 \frac{(2a-1)(t+4)}{8(4-3t)}
       ((t+4)Z_1+(3t-4)Z_5).                    \tag{10}
\]

For a B edge define its extra signed defect as follows:

\[
 n_{72}=h_{72}+U_7-U_2,\qquad
 n_{67}=h_{67}-(U_7-U_6),\qquad
 m_{36}=h_{36}+U_6-U_3.                           \tag{11}
\]

The verifier checks all entries in the following table. The middle
column gives the coefficients of `(p,q,extra)` in `L/delta`; the last
column is the coefficient of the cubic normal term `delta³`. In the
anchor row there is no extra defect.

| Endpoint | Regularized determinant | Defect coefficients | Cubic coefficient |
|---|---|---|---|
| Flat `z=0`, `0<u<1/2`, extra 72 | `2048(2u-1)` | `(u,0,-1/2)` | `0` |
| Flat `z=1/2`, `0<u<1/2`, extra 67 | `2048(2u-1)` | `(u,-1/2,0)` | `-1/2` |
| Flat `u=1/2`, `0<z<1/2`, extra 36 | `4096z(2z-1)` | `(1/2,-z,0)` | `-1/(4z)` |
| Flat `u=0`, `0<z<1/2`, anchor 23 | `-4096z(2z-1)` | `(0,-z)` | `-1/(4z)` |
| Exceptional `z=0`, `0<a<1/2`, extra 72 | `-4096a(2a-1)` | `(1-a,a-1/2,-1/2)` | `0` |
| Exceptional `z=a`, `0<a<1/2`, extra 67 | `-4096a(2a-1)` | `(1-a,-1/2,0)` | `-1/(4a)` |

In each exceptional row the r coefficients of beta and `L/delta` are
`2a` and `2a-1`. The beta coefficients of a defect equal its displayed
Farkas coefficient, except that the p coefficient is smaller by one
and the q coefficient is larger by one. Its normal quadratic
coefficient equals the displayed cubic coefficient. These identities
are also checked symbolically.

## 4. Two exact restored B-edge identities

For the vertical endpoint 72 put `z=h72`, `n=n72`,
`D7=H7-gamma7`, and `S7=H7+gamma7-2gamma2`. The original edge equations
give exactly

\[
 (1-2t\gamma_2)D_7=2x_2(n-2z),\qquad
 n(2z-n)=Z_7^2+tD_7S_7.                          \tag{12}
\]

Relative edge bounds give `|n|≤Cz` and `|S7|≤Cz`. In particular,
`|D7|≤C|x2|z`. If n is negative, (12) implies

\[
 n_-\le Ct z|x_2|.                              \tag{13}
\]

For the horizontal endpoint 67 put `lambda=h67`, `n=n67`,
`D67=(H7-H6)-(gamma7-gamma6)`, and
`S67=(H7-H6)+(gamma7-gamma6)`. Then

\[
 n(2\lambda-n)=(Z_7-Z_6)^2+tD_{67}S_{67}.        \tag{14}
\]

The third-direction certificate gives
`(U7-U6)/lambda -> 1` and `Z7-Z6=o(delta lambda)`.
Since `|S67|≤C lambda`, this yields

\[
 |n|\le o(\delta^2\lambda)+Ct|D_{67}|.           \tag{15}
\]

All identities are checked by polynomial expansion from the exact
twenty-four edge equations.

## 5. Flat vertical endpoint `z=0`

The flat reference has `H=gamma` and `x2=0` for every free parameter
and t. Analyticity therefore gives

\[
 |H_5-\gamma_5|+|x_2|
 \le C(p+|q|+|n|+\delta^2).
\]

Equations (5) and `beta -> 0`, followed by absorption of `Ct|q|`, show
`q=o(delta²+|n|)`, and hence `x2=O(delta²+|n|)`.
From (13), absorb the small coefficient of `n_-` to obtain

\[
 n_-=o(\delta^2+n_+),\quad
 |n|=O(\delta^2+n_+),\quad q=o(\delta^2+n_+).
\]

The second equation in (12), with `Z7/delta -> 1`, now gives

\[
 \delta^2\le C z n_+ +o(\delta^2),
 \qquad n_+\ge c\delta^2/z\gg\delta^2.           \tag{16}
\]

Thus `n_-=o(n_+)`, `q=o(n_+)`, and `p=o(n_+)`. The negative n
coefficient `-1/2` dominates every defect error and the bounded cubic
normal term. The exact reference term (8) is nonpositive, so
`L<0`, a contradiction.

The estimates in this section remain uniform as `u -> 0`, provided
the collapsed anchor 23 has the horizontal direction used in Section
2. The regularized determinant remains nonzero there. This extension
can be used for that boundary of the four-zero stratum.

## 6. Flat horizontal and anchor endpoints

At `z=1/2`, the flat reference has `H=gamma`. Consequently both
`H5-gamma5` and `D67` are `O(p+|q|+|n|+delta²)`. Combine (5) and
(15), use `beta,lambda -> 0`, and absorb their small multiples of
`|q|+|n|`. This proves

\[
 |q|+|n|=o(\delta^2).
\]

The p contribution is also `o(delta³)` after multiplication by delta.
The reference term is nonpositive and the cubic coefficient tends to
`-1/2`. Hence `L<0`.

At `u=0` the third edge is the anchor 23, handled by its own normalized
horizontal direction as described in Section 2. No extra squared
equation needs replacement. The flat reference and (5) give
`q=o(delta²)`. Its cubic coefficient `-1/(4z)` is strictly negative,
where `0<z<1/2`, while the reference term stays nonpositive even
though its factor u tends to zero. Again `L<0`.

## 7. The two exceptional endpoints

### Horizontal endpoint `z=a`

The reference (9) has `H=gamma` at `r=0`. Analyticity gives

\[
 |H_5-\gamma_5|+|D_{67}|
 \le C(r+p+|q|+|n|+\delta^2).
\]

Equations (5) and (15) imply `|q|+|n|=o(r+delta²)`. The checked beta
jet is therefore

\[
 \beta=2ar-\frac{\delta^2}{4a}+o(r+\delta^2).     \tag{17}
\]

Positivity of beta forces `delta²=O(r)` and `beta=O(r)`. This excludes
the hierarchy `beta/r -> infinity`. In the comparable hierarchy set
`eta=lim Z5/(delta beta)`. The limiting signs (1) and `a13>0` give

\[
 0\le\eta<1/a.                                  \tag{18}
\]

Indeed the original normalized small vector is `(-1,-eta)` and
`B7-B3=(-a,-1)`, so its determinant is `1-a eta`. The equality branch
is part of the implication's UNSAT check.

Let `R=beta/r`; (17) gives `0≤R≤2a+o(1)`. Substituting its normal
term into (10) and the checked Farkas correction gives

\[
 \frac{L}{r\delta}
 =-1+R(1+(\tfrac12-a)\eta)+o(1)
 \le-2(\tfrac12-a)(1-a\eta)+o(1)<0.              \tag{19}
\]

If `R -> 0`, the left side instead tends directly to `-1`; no strict
slope bound is needed in that branch. Thus all ratios are covered.

### Vertical endpoint `z=0`

Here
`|H5-gamma5|+|x2|≤C(r+p+|q|+|n|+delta²)`.
Equations (5) and (13) imply

\[
 q=o(r+|n|+\delta^2),\qquad
 n_-=o(r+n_++\delta^2).
\]

The beta jet, whose quadratic normal coefficient is zero, becomes

\[
 \beta=2ar-\tfrac12n_++o(r+n_++\delta^2).
\]

Its positivity gives `n_+≤Cr+o(delta²)`. The restored vertical-edge
equation (12) then yields

\[
 \delta^2\le Czn_++Ct z^2(r+n_++\delta^2),
 \qquad \delta^2=O(zr)=o(r).                     \tag{20}
\]

It follows that `n_+=O(r)`, `q=o(r)`, `n_-=o(r)`, and `beta=O(r)`.
The dominant beta hierarchy is again impossible. In the comparable
case use the same strict slope bound (18). The relation
`beta/r=2a-n/(2r)+o(1)` eliminates the n term in the Farkas expansion,
giving exactly (19). The normal cubic term is negligible by (20).
This also contradicts `L≥0`.

## 8. Flat endpoint `u=1/2`: an exact expanded reference

The zero coefficient of `m=m36` in the table alone is insufficient:
an uncontrolled higher power of m could dominate the negative cubic
term. The following exact reference avoids that issue.

Put `a0=(1-m)/2` and `beta0=r(1-m)`. For every r,u,z,m,t define

\[
\begin{aligned}
 P&=(0,r,0,u,\tfrac12,\beta_0,a_0,z),\\
 x&=(0,-r,0,-u,0,\beta_0-\tfrac12,a_0-\tfrac12,z-\tfrac12),\\
 \gamma=H&=(0,2a_0r-r/2,2a_0r-\tfrac18,
       -4a_0ru+2a_0r+u/2-\tfrac18,\\
 &\hspace{33mm}2a_0r-\tfrac14,a_0r,a_0/2-\tfrac18,
       2a_0r-2rz+z/2-\tfrac18).
\end{aligned}                                                    \tag{21}
\]

The checker verifies all original metric residuals are zero except
edge 36, whose residual is exactly `m(2u-1)`. Its signed defects are
`p=q=0`, `m36=m`. Thus (21) solves the regularized system for every
parameter, and `H=gamma` identically throughout this enlarged family.

For the actual implicit solution this yields the uniform bounds

\[
 |H_5-\gamma_5|+|H_6-\gamma_6|
 \le C(p+|q|+\delta^2),                           \tag{22}
\]

with no separate m term or uncontrolled higher powers of m. Equation
(5) gives `q=o(delta²)`. For edge 36, with `lambda=h36`, the restored
equation is

\[
 m(2\lambda-m)=Z_6^2+
 t(H_6-\gamma_6)(H_6+\gamma_6-2\gamma_3).
\]

Relative height bounds and (22) give `m_-≤Ct delta²`. The beta jet
about (21) is

\[
 \beta=r(1-m)-\frac{\delta^2}{4z}+o(\delta^2).    \tag{23}
\]

Consequently `delta²=O(r)` and `beta/r≤1+o(1)`; the dominant beta
hierarchy is impossible.

The exact Farkas numerator of (21), minus that of the old flat
reference, factors m. At `t=0` the quotient is

\[
 2(-Z_1+2rZ_4+Z_5-2rZ_6).
\]

For all t, its coefficients of `Z4,Z6,Z7` vanish at `r=0`, while
there its two remaining coefficients are
`-(t+4)²/8` and `-(t+4)(8tu-t-4)/8`. These polynomial identities imply

\[
 L_{\rm ref}=L_{\rm flat}+
 m(-r\delta+Z_5/2+o(r\delta)+o(1)Z_5).           \tag{24}
\]

In the comparable hierarchy the same zero-retaining trit certificate
now gives `0≤eta=lim Z5/(delta beta)<2`. With (23), the bracket in
(24) is at most `-epsilon r delta` for some fixed positive epsilon.
Thus a positive m decreases the functional. Its negative part
contributes at most `O(m_-r delta)=o(delta³)`. The `beta/r -> 0`
branch has the same conclusion immediately from `Z5=O(delta beta)`.

The p and q corrections are `o(delta³)`. The remaining normal cubic
coefficient tends to `-1/(4z)<0`, while (8) is nonpositive. Therefore
`L<0`. This treats arbitrary relative rates of m, r, t, and delta and
finishes all six endpoint families.

## Reproduction

```sh
python3 research/type7_completion/remaining_three_cluster_blowup.py /tmp/type7-three-cluster
g++ -O3 -std=c++17 research/orientation_checkpoint/check_unsat.cpp -o /tmp/type7-three-checker
```

Pass each generated CNF to the independent checker on standard input
and require explicit `UNSAT nodes ...` output. There are 103 files:
78 base directional exclusions, twelve third-direction exclusions,
twelve combined directional/sign implications, and one complete
1,888-model coverage certificate. The JSON records all 304 cells,
the complete 114-case split, and the exact metric coefficients.

The producer also rechecks the constant necessity ranks, all six
regularized Jacobians and inverse-Jacobian coefficients, the restored
edge identities, and the all-parameter reference (21). The analytic
estimates above supply the uniform passage from these exact finite
certificates to arbitrary-rate sequences.
