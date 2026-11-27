# Ray 3: all 300 mixed four-zero common-line cells are impossible

Consider a common-line ray-3 sequence whose first normal blow-up has
one collinear cap and one noncollinear cap, and exactly four vanishing
physical short-edge weights. Such a sequence is impossible. The proof
allows arbitrary relative rates of all four small weights, the normal
width, and `t=1/y²`.

The exhaustive degenerate-norm cover has **300** cells in this stratum.
Each has two adjacent zero weights in the collinear cap and two zero
weights in its partner. Marked symmetries reduce them to 35 shapes.
The three ratios of the two A-edge stretched norms give 105 cases:
73 are directly UNSAT, twelve more are UNSAT after separately
normalizing a coincident B short edge, and twenty reduce to six metric
endpoint arguments and their checked mirrors.

This is an asymptotic research theorem. It supplies neither a numerical
height threshold nor a Lean proof of Type 7.

## 1. Complete finite cover

Use `A=(0,1,4,5)=(0,0,0,1/2)` and `B=(2,3,6,7)` in the stretched
transverse plane. Let a=01 and b=14. The three cases are a dominant,
comparable stretched norms, or b dominant. Every normalized actual
short edge is nonzero; zero leading bracket coefficients remain free.

The 34 constant, thirty linear, and four quadratic bracket formulas
are those checked in `remaining_cluster_blowup.py`. When a B edge has
coincident stretched endpoints, its separately normalized direction c
adds the eleven linear and three bilinear formulas of
`remaining_three_cluster_blowup.py`. The rank-three Grassmann–Plücker
sign conditions include all five directions E,F,a,b,c at infinity.
Every formula factors the actual small edge or edge product before
the uniform relative axial estimate is used.

The marked mirror `(0 4)(2 6)` reverses the A hierarchy. The surviving
cases, after this explicitly recorded mirror, are:

| Shape | B horizontal order | B normal order | Triangle signs | Cases including mirrors |
|---|---|---|---|---:|
| Opposite vertical V | `(1,0,1,1)` | `(0,0,0,1)` | `(0,-1,0,1)` | 2 |
| Complementary vertical V | `(1,0,0,0)` | `(1,1,0,1)` | `(1,0,-1,0)` | 2 |
| Exceptional zero/zero | `(1,0,0,0)` | `(0,1,1,0)` | `(0,1,1,0)` | 4 |
| Flat half/half | `(1,1,1,0)` | `(0,1,1,0)` | `(0,1,1,0)` | 4 |
| Flat zero/zero | `(0,1,0,0)` | `(0,1,1,0)` | `(1,0,0,1)` | 4 |
| Flat half/zero | `(1,1,0,0)` | `(0,1,1,0)` | `(1,1,1,1)` | 4 |

Both V rows have a dominant. Their complete uniform exclusions are
proved in `exhaustive_four_cluster_v.md`; the present producer imports
and rechecks both implication certificates and all their metric
identities. This includes the complementary V's centered first defect
and its exact all-t folded reference.

The remaining four rows have a dominant or comparable. Relabel by the
checked permutation `(5,0,3,6,1,4,7,2)`, taking the cluster to 0,1,5
and the tip to4. They become respectively the parameter endpoints

\[
 (r,a,z)\to(0,0,0),\quad
 (r,u,z)\to(0,\tfrac12,\tfrac12),\quad
 (r,u,z)\to(0,0,0),\quad
 (r,u,z)\to(0,\tfrac12,0).
\]

All ten combined implication certificates retain every leading-zero
branch. In particular, the dominant exceptional row permits `ax=0`;
the proof below never replaces this by a strict horizontal direction.

## 2. Common metric setup

Use the exact face-023 chart `(P_i,Z_i,c_i-2tH_i)` with `P=-U`, and put

\[
 \delta=Z_6>0,\quad Z_7/\delta\to1,
 \quad Z_1/\delta,Z_4/\delta,Z_5/\delta\to0.
\]

The normalized coincident B edge is horizontal. For the zero/zero flat
corner it is the anchor23 itself. Dividing this actual edge by its own
stretched norm gives a nonzero horizontal component; the physical
component divided by h23 tends to one and its normal component is
`o(delta h23)`. Rotating into the face plane changes the angle by
`o(delta)`, preserving the displayed normal profile. The relative
axial error divided by this same edge length is `O(t)`. Thus no inverse
power of the vanishing anchor length occurs.

Write

\[
 r=h_{01},\quad \beta=h_{50},\qquad
 p=r+U_1,\quad q=\beta+U_5.
\]

All four rows force 01 horizontal with `U1/r→-1` and
`Z1=o(delta r)`. Its exact restored equation gives

\[
 0\le p=o(\delta^2r).                            \tag{1}
\]

In the three flat rows, 50 also has a nonzero horizontal component:
`U5/beta→-1`, `Z5=O(delta beta)`. Consequently

\[
 |q|\le C\delta^2\beta+Ct|H_5-\gamma_5|.          \tag{2}
\]

The exceptional row uses only `q=O(beta)` and the physical edge bound.

For B define

\[
 m=\mu_{36}=h_{36}+U_6-U_3,\quad
 w=\mu_{67}=h_{67}-(U_7-U_6),\quad
 n=\mu_{72}=h_{72}+U_7-U_2.
\]

For a horizontal67 edge, with `lambda=h67`, the restored equation and
the separately normalized direction give

\[
 |w|\le o(\delta^2\lambda)+Ct|D_{67}|,
 \qquad D_{67}=H_7-H_6-\gamma_7+\gamma_6.         \tag{3}
\]

For a vertical72 edge, with `z=h72`, the exact equations are

\[
\begin{aligned}
 (1-2t\gamma_2)(H_7-\gamma_7)&=2x_2(n-2z),\\
 n(2z-n)&=Z_7^2+t(H_7-\gamma_7)(H_7+\gamma_7-2\gamma_2).
\end{aligned}                                                    \tag{4}
\]

Since `|n|≤Cz` and the last height factor is `O(z)`,

\[
 n_-\le Ct z|x_2|.                               \tag{5}
\]

All these exact identities are the ones verified in the preceding
three-zero package. The newly regularized Jacobians and their
coefficients are:

| Corner | Replaced equations | Determinant | Coefficients of `L/delta` | Normal cubic |
|---|---|---:|---|---:|
| Flat zero/zero | 01,50,72 | -2048 | `(p,q,n)=(0,0,-1/2)` | 0 |
| Flat half/half | 01,50,36,67 | 2048 | `(p,q,m,w)=(1/2,-1/2,0,0)` | -1/2 |
| Flat half/zero | 01,50,36,72 | 2048 | `(p,q,m,n)=(1/2,0,0,-1/2)` | 0 |
| Exceptional zero/zero | 01,50,67,72 | -2048 | `(p,q,w,n)=(1,-1/2,0,-1/2)` | 0 |

Here L is the nonnegative combination of the four required weak
bracket signs from the preceding proofs. Its weights are
`((1-2u)N/D,2uN/D,N/D,1)`, with
`N=4+t(4r-1)²`, `D=4+t(32ru-8r-8u+1)` and actual `0<u=h23<1/2`.
The beta coefficients follow from
`U1-U5=beta-r+p-q`, and its normal quadratic coefficient equals the
last column. The exceptional beta coefficients are
`(0,1/2,0,-1/2)`.

The determinant checks provide analytic charts with bounded
derivatives. The constant rank14 intrinsic and rank5 height systems
force the displayed limiting branches. Normal corrections start
quadratically, and analytic differences in defects factor those
defects. Exact references, rather than truncated jets alone, control
the unrestricted rates below.

## 3. The flat zero/zero corner

This is the uniform `u→0` extension of Section5 in
`remaining_three_cluster_blowup.md`. Its three-defect Jacobian remains
nonzero and the forced horizontal anchor direction justifies the same
face chart.

The exact flat reference has `x2=0`, `H=gamma` for every r,u,z,t, so

\[
 |H_5-\gamma_5|+|x_2|\le C(p+|q|+|n|+\delta^2).
\]

Equations (2) and (5), with absorption of the small defect multiples,
give `q=o(delta²+n+)`, `n-=o(delta²+n+)`, and
`x2=O(delta²+n+)`. Equation (4) then gives

\[
 \delta^2\le C z n_++o(\delta^2),
 \qquad n_+\gg\delta^2.                          \tag{6}
\]

Thus q,n-,p are `o(n+)`. The exact reference functional is nonpositive,
and the coefficient of n is `-1/2`; its negative contribution dominates
all remaining defect and cubic errors. This contradicts `L≥0`.

## 4. An exact expanded flat reference

The two remaining flat corners use the all-parameter reference (21)
in `remaining_three_cluster_blowup.md`. Put `a0=(1-m)/2`,
`beta0=r(1-m)`. Its horizontal coordinates are

\[
 P=(0,r,0,u,\tfrac12,\beta_0,a_0,z),\qquad
 x=(0,-r,0,-u,0,\beta_0-\tfrac12,a_0-\tfrac12,z-\tfrac12).
\]

It has `x2=0`, `H=gamma`, `p=q=w=n=0`, and `mu36=m` exactly. Every
original equation other than36 vanishes, while the residual of36 is
`m(2u-1)`. It consequently solves either modified four-defect system
for every r,u,z,m,t. This removes every uncontrolled power of m from
the height-error bounds.

The checked reference functional is

\[
 L_{\rm ref}=L_{\rm flat}
       +m\{-r\delta+Z_5/2+o(r\delta)+o(1)Z_5\},
 \qquad L_{\rm flat}\le0.                        \tag{7}
\]

The exact coefficient calculation, including divisibility of the
Z4,Z6,Z7 coefficients by r, is rechecked by the new producer. In the
comparable A hierarchy the finite implication forces the leading trit
`a13` strictly positive, including exclusion of its zero boundary.
Thus whenever `beta/r` has a positive finite limit,

\[
 0\le\eta_5=\lim Z_5/(\delta\beta)<2.            \tag{8}
\]

Indeed its determinant is `1-eta5/2`. The dominant beta hierarchy
corresponds to `beta/r→infinity`, since both A directions in these
flat rows have nonzero horizontal components.

## 5. Flat half/half

The extra67 direction is horizontal. The expanded reference gives

\[
 |H_5-\gamma_5|+|D_{67}|+|H_6-\gamma_6|
       \le C(p+|q|+|w|+\delta^2).
\]

Equations (2) and (3) give `q,w=o(delta²)` after absorption. The
restored36 equation gives `m-≤Ct delta²`. Expanding beta around the
exact m-reference, rather than around m=0, gives

\[
 \beta=r(1-m)-\delta^2/2+o(\delta^2).             \tag{9}
\]

Positivity of beta gives `delta²=O(r)` and `beta/r≤1+o(1)`, excluding
the dominant beta hierarchy. In the comparable case, (8) makes the
brace in (7) at most `-epsilon r delta`. Thus positive m helps, while
its negative part contributes only `O(t r delta³)=o(delta³)`.
If `beta/r→0`, the same conclusion follows directly from
`Z5=O(delta beta)`.

The p,q,w corrections are `o(delta³)` and the remaining normal cubic
coefficient tends to `-1/2`. Hence `L<0`. No positivity of the
reference value `h67=a0-z` was used: only its exact metric equations
and `H=gamma` are needed; the relative bounds above apply to the actual
positive edge.

## 6. Flat half/zero

Now 36 and72 are both vertical. The same expanded reference gives

\[
 |H_5-\gamma_5|+|H_6-\gamma_6|+|x_2|
       \le C(p+|q|+|n|+\delta^2),
\]

with no separate m term. The absorption argument of Section3 gives
`q,n-=o(n+)`, `x2=O(n+)`, and `n+≫delta²`. The restored36 equation
then gives `m-≤Ct n+`. The beta jet is

\[
 \beta=r(1-m)-n_+/2+o(n_+).                      \tag{10}
\]

Consequently `n+=O(r)` and `beta/r≤1+o(1)`. The dominant beta
hierarchy is impossible. In the comparable hierarchy (8) again makes
the positive-m reference contribution nonpositive. Its negative part
is `O(t r n+ delta)=o(n+ delta)`. Every normal cubic is negligible
because `delta²=o(n+)`; p and q also contribute `o(n+ delta)`.
The remaining `-n+ delta/2` coefficient forces `L<0`.

## 7. Exceptional zero/zero, including the vertical50 direction

Set `lambda=h67`, `z=h72`, `a=lambda+z`. All are positive and tend to
zero. The directional implication retains `ax=0` in the dominant
case. It gives the required weak sign **`[1256]≥0`**, `ay≤0`, and
the horizontal67 direction. No physical/stretched comparison for
edge50 is assumed.

There is an exact reference for every r,a,z,t, obtained from Section4
by setting `u=1/2`, `m=1-2a`:

\[
\begin{aligned}
 P&=(0,r,0,\tfrac12,\tfrac12,2ar,a,z),\\
 x&=(0,-r,0,-\tfrac12,0,2ar-\tfrac12,a-\tfrac12,z-\tfrac12),\\
 \gamma=H&=(0,2ar-r/2,2ar-\tfrac18,\tfrac18,
     2ar-\tfrac14,ar,a/2-\tfrac18,2ar-2rz+z/2-\tfrac18).
\end{aligned}                                                    \tag{11}
\]

All original metric equations vanish. Its four defects p,q,w,n
vanish, `x2=0`, and `beta0=2ar`. Uniform analyticity gives

\[
 |x_2|+|H_5-\gamma_5|+|D_{67}|
       \le C(p+|q|+|w|+|n|+\delta^2).
\]

Use only `q=O(beta)`. Equations (3) and (5) imply

\[
 w=o(\beta+|n|+\delta^2),\quad
 n_-=o(\beta+n_++\delta^2),\quad
 x_2=O(\beta+n_++\delta^2).
\]

The checked beta jet and its zero normal quadratic coefficient give,
with `W=beta-U5=2beta-q`,

\[
 W=4ar-n_++o(\beta+n_++\delta^2).
\]

The physical edge bound gives `W≥-Ct beta`. Thus
`n+=O(ar)+o(beta+delta²)`. Substitution into (4), using `z≤a`, yields

\[
 \delta^2=O(a^2r)+o(a\beta).
\]

Returning to the previous bounds gives

\[
 n_+=O(ar)+o(\beta),\quad n_-,w=o(ar+\beta),
 \quad -Ct\beta\le W\le Car+o(\beta).           \tag{12}
\]

Put `kappa=Z5/delta→0`. The direction condition `ay≤0` implies
`kappa-=o(beta)`: otherwise, since `|U5|≤C beta`, the original a
vector normalized by its stretched norm would have a strictly positive
limiting normal component. This argument includes a zero horizontal
component.

The actual short-path difference is exactly

\[
 C=P_6-P_2=a-n-w,\qquad |C|\le C_0a.            \tag{13}
\]

Factor `[1256]` using the three rows
`L=r2-r1`, `v=r5-r1`, `B=r6-r2`. Their axial increments in the last
two rows are bounded by `Ct(r+beta)` and `Ct a`. Also
`Z1=o(delta r)`, `P1=r-p`, `P5=-U5`, and the first row's horizontal
component is `O(r+beta)` by (12). The exact determinant, divided by
delta, therefore gives the necessary inequality

\[
 -U_5-r-C\kappa+o(r+\beta+a|\kappa|)\ge0.        \tag{14}
\]

Every axial error retains a relative short-path factor; no missing-edge
length is used as a denominator.

After a subsequence either `beta=O(ar)` or `beta/(ar)→infinity`.
In the first case `beta=o(r)` and `U5=o(r)`. Equations (12) and (13)
give `C=a(1+o(1))`. As `kappa-=o(beta)`, the left side of (14) is
strictly negative at scale `r+a kappa+`, a contradiction.

In the second case (12) gives `W=o(beta)`, hence `U5/beta→1`.
Initially use only `|C|≤C0 a` in (14); absorption gives
`beta+r=O(a|kappa|)`, so `beta=o(a)`. Now (12) gives `n+w=o(a)` and
again `C=a(1+o(1))`. The left side of (14) is strictly negative at
scale `beta+r+a kappa+`, using `kappa-=o(beta)` once more.
This is the final contradiction and completes the 300-cell stratum.

## Reproduction

```sh
python3 research/type7_completion/exhaustive_four_cluster_blowup.py /tmp/type7-four-cluster
g++ -O3 -std=c++17 research/type7_completion/solver_check_rup.cpp -o /tmp/type7-rup-check
python3 research/type7_completion/solver_cnf_certificates.py /tmp/type7-four-cluster-proofs \
  --checker /tmp/type7-rup-check /tmp/type7-four-cluster
```

The producer reconstructs the complete 1,888-model cover and all 300
marked-symmetry mappings. It emits 96 CNFs: 73 direct exclusions, twelve
third-direction exclusions, ten combined implications, and one complete
model-coverage certificate. The JSON records every original cell,
hierarchy, mirror, implication, and exact metric coefficient. Its rank
sign clauses are cached across the three hierarchies without changing
the formulas.

Independently replay each CNF with the repository C++ checker, requiring
explicit `UNSAT nodes ...` output, or use the checked RUP replay path.
The symbolic producer also verifies both V references and relative
jets, all four new corner Jacobians, the simultaneous expanded
references, the exact Farkas factors, the exceptional all-r family,
and the factored determinant in (14).
