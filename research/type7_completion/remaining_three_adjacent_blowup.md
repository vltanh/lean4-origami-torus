# Ray 3: the sixteen adjacent-collision mixed three-zero cells

## Result and complete cover

The sixteen mixed common-line blow-up cells with one zero weight in the
collinear cap and two in its noncollinear partner are impossible. Checked
marked symmetries and horizontal/normal reflection put every cell in
the stretched transverse picture

\[
 A=(0,0),(r,0),(r,0),(\tfrac12,0),\qquad
 B=(0,0),(-\tfrac12,0),(0,0),(0,1),\quad 0<r<\tfrac12.
\]

The cyclic labels are `A=(0,1,4,5)`, `B=(2,3,6,7)`. The zero physical
weights are 14, 67, and 72. The proof uses both cap signs. The A-cap
sign first makes two length defects negligible; the B-cap then has
the opposite sign from its necessary weak sign.

This is an asymptotic research exclusion, with no fixed height bound
or Lean theorem. Every relative rate of all three small weights, the
width, and `t=1/y²` is allowed.

## 1. Coordinates and necessary signs

Use the face-023 incidence chart

\[
 P_i=(U_i,Z_i,c_i-2tH_i),\qquad c_i=\mathbf1_{i\in B}.
\]

The anchors have `U2=x2`, `U3=x3`, `H2=gamma2`, `H3=gamma3`, and
`Z0=Z2=Z3=0`. Choose the reflection so that `delta=Z7>0`.
The displayed limiting shape means

\[
 Z_1,Z_4,Z_5,Z_6=o(\delta).
\]

The finite implication in `remaining_adjacent_blowup.py`, whose
coefficients do not require a positive B72 weight, gives

\[
 [0124]\le0,\quad [1247]\ge0,\quad[1467]\ge0,
 \quad[0145]\le0.                              \tag{1}
\]

Normalize edge 14 by its own stretched maximum norm. The three
factored determinants in (1) have limiting coefficients
`-r*d_y`, `d_x`, and `-d_x`. Thus `d_x=0`, and nonzeroness forces
`d_y>0`. In particular, with

\[
 dU=U_4-U_1,\qquad dZ=Z_4-Z_1,\qquad
 \kappa=dZ/\delta,
\]

we have `kappa>0` eventually, `kappa→0`, and `dU/kappa→0`.
Every determinant used here contains the actual edge 14 before
division, so the error is relative to that edge.

Retaining this positive vertical virtual direction gives a second
finite implication:

\[
 [0145]\le0,\qquad[2367]\le0.                  \tag{2}
\]

The new checker generates all nonzero leading determinants, factoring
14 whenever it occurs, and proves the negation of (2) UNSAT. Each
scalar coefficient is affine in r; its endpoint signs certify its
strict sign throughout `0<r<1/2`. Every zero leading determinant remains
unrestricted. Both global orientations are allowed in the base formula.

## 2. The A collision is smaller than the entire B cluster

Put

\[
 \beta=h_{14},\quad\lambda=h_{67},\quad\sigma=h_{72},
 \quad\eta=\lambda+\sigma.
\]

All are positive and tend to zero. The uniform short-edge bounds give

\[
 |dU|+|dH_{14}|\le C\beta,\quad
 |U_7-U_2|+|H_7-H_2|\le C\sigma,\quad
 |U_7-U_6|+|H_7-H_6|\le C\lambda.
\]

Also `delta≤C sigma≤C eta`, because 72 is an actual short edge.

The actual signs `[1247]≥0` and `[1467]≥0` give more information
than their limiting directions. Factor edge 14 and respectively the
actual edges 27 and 67. In `[1247]`, the main transverse term, after
division by delta, is

\[
 (1+O(t))\bigl(dU-\kappa(U_7-U_2)\bigr).
\]

All other terms are bounded by `Ct(beta+sigma*kappa)`. Indeed the
axial increment of 14 is `O(t beta)`, the axial increment of 27 is
`O(t sigma)`, and the normal coordinate of the remaining long vector
is `Z1=o(delta)`. Factoring both short vectors before estimating
preserves these bounds even when either edge is arbitrarily small.

For `[1467]` the main term is

\[
 -(1+o(1)+O(t))dU+(1+O(t))\kappa(U_7-U_6),
\]

with error bounded by `Ct(beta+lambda*kappa)`. Here
`Z7-Z6=delta(1+o(1))`. Combining the two inequalities yields

\[
 |dU|\le C\eta\kappa+Ct\beta.                  \tag{3}
\]

The exact edge-14 metric and the relative axial bounds imply
`beta≤C(|dU|+|dZ|)` for sufficiently small t. Since
`dZ=delta*kappa≤C eta*kappa`, absorb the `Ct beta` term in (3):

\[
 \boxed{\ \beta=O(\eta\kappa)=o(\eta).\ }       \tag{4}
\]

This comparison is deduced from actual determinant inequalities; it
is not an assumption on the three collapse rates.

## 3. A regular metric chart and its exact first derivatives

Use the three actual intrinsic parameters

\[
 r=h_{01},\qquad b=h_{14},\qquad z=h_{72},
\]

so `x1=-r`, `x4=1/2-r-b`, and `x7=x2+z-1/2`.
Replace just the three vanishing-edge squared equations by the signed
defect definitions

\[
 \mu_{14}=b-(U_4-U_1),\quad
 \mu_{67}=h_{67}-(U_7-U_6),\quad
 \mu_{72}=z+(U_7-U_2).                          \tag{5}
\]

Every actual realization satisfies this modified system with its own
defects. At `b=z=mu14=mu67=mu72=Z=0` it has the exact solution

\[
\begin{aligned}
 x&=(0,-r,\tfrac12,0,\tfrac12-r,0,0,0),\\
 \gamma=H&=(0,r/2,\tfrac18,\tfrac38,r/2,
                         \tfrac14,\tfrac18,\tfrac18),\\
 U&=(0,r,\tfrac12,0,r,\tfrac12,\tfrac12,\tfrac12).
\end{aligned}                                                   \tag{6}
\]

All twenty-one original metric equations vanish identically for every
r and t in this family. The affine stress reconstruction has constant
rank fourteen; the cross-edge height reconstruction has constant rank
five. They force (6) as the limit of an actual sequence, rather than
selecting a convenient branch without justification.

The modified twenty-one-variable Jacobian at `t=0` has determinant

\[
 4096r(2r-1)\ne0.
\]

The implicit solution is therefore analytic uniformly near the
proposed limiting r. Define `theta_i=H_i-U_i/2`. Exact differentiation
gives the following coefficients at the corner:

| Quantity | b | z | mu14 | mu67 | mu72 |
|---|---:|---:|---:|---:|---:|
| theta1 | 0 | -4r | -2r | -2r(2r-1) | 2r |
| theta5 | 0 | -2 | 0 | 0 | (2r+1)/2 |
| h67 | 0 | 0 | 0 | 1/2 | (1-2r)/2 |
| U6-U2 | 0 | -1 | 0 | 1/2 | (2r+1)/2 |
| H6-gamma2 | 0 | -3/2 | 0 | -(8r-3)/4 | -(2r-3)/4 |

By the original short-edge metrics,

\[
 -Ct h_e\le\mu_e\le(2+Ct)h_e.
\tag{7}
\]

Consequently `b,mu14=o(eta)` by (4), while `z,mu67,mu72=O(eta)`.
All five normal coordinates are `O(delta)=O(eta)` and enter the
planar metric system only quadratically. The exact all-t identity
(6) removes errors depending only on t. Analyticity therefore makes
the remainder in every table expansion `o(eta)`, uniformly for every
ratio of eta to t.

## 4. The A-cap sign removes both B defects

Factoring the actual edge 14 gives the exact identity

\[
\begin{aligned}
 [0145]=2t\{&dZ(U_5\theta_1-U_1\theta_5)\\
 &+Z_5(U_1d\theta-\theta_1dU)
  +Z_1(dU\theta_5-U_5d\theta)\},
\end{aligned}                                                   \tag{8}
\]

where `dtheta=theta4-theta1`. The relative height bound gives
`dtheta=O(beta)`. Since `Z1,Z5=o(delta)`, `dZ=delta*kappa`, and
`beta=O(eta*kappa)`, the last two terms divided by dZ are `o(eta)`.
The table and `U1→r`, `U5→1/2` give

\[
 \frac{[0145]}{2t\,dZ}
 =r(1-2r)\bigl(\mu_{67}+\tfrac12\mu_{72}\bigr)+o(\eta).
\tag{9}
\]

Both coefficients are strictly positive. By (7) the negative parts
of the two defects are `o(eta)`. The necessary sign `[0145]≤0`
therefore forces

\[
 \mu_{67}=o(\eta),\qquad\mu_{72}=o(\eta).       \tag{10}
\]

This inference retains zero limiting cap determinants: it uses the
weak sign and the strict coefficients, not a presumed nonzero limit.

## 5. The B-cap has the forbidden positive sign

The same table and (10) now yield

\[
 \lambda=o(\eta),\quad \sigma/\eta\to1,\quad
 (U_6-U_2)/\eta\to-1,\quad
 (H_6-\gamma_2)/\eta\to-\tfrac32.              \tag{11}
\]

Also `h23→1/2`, `gamma23→1/4`. The exact B-cap identity is

\[
 [2367]=2t\{Z_6(h_{23}\Delta H_{67}+\gamma_{23}\Delta U_{67})
 -\Delta Z_{67}[h_{23}(H_6-\gamma_2)
                    +\gamma_{23}(U_6-U_2)]\}.
\tag{12}
\]

The first term divided by `delta eta` tends to zero because
`Z6=o(delta)` and both increments are `O(lambda)`. The second term
has `Delta Z67/delta→1`, and its bracketed coefficient divided by
eta tends to

\[
 \tfrac12(-\tfrac32)+\tfrac14(-1)=-1.
\]

Thus

\[
 \boxed{\displaystyle [2367]/(2t\delta\eta)\longrightarrow1>0.}
\]

This contradicts `[2367]≤0` from (2), and excludes all sixteen cells.

## Reproduction

```sh
python3 research/type7_completion/remaining_three_adjacent_blowup.py /tmp/type7-three-adjacent
g++ -O3 -std=c++17 research/orientation_checkpoint/check_unsat.cpp -o /tmp/type7-adjacent-checker
/tmp/type7-adjacent-checker < /tmp/type7-three-adjacent/three_adjacent_required_signs.cnf
/tmp/type7-adjacent-checker < /tmp/type7-three-adjacent/three_adjacent_negative_caps.cnf
/tmp/type7-adjacent-checker < /tmp/type7-three-adjacent/three_adjacent_model_coverage.cnf
```

Require explicit `UNSAT nodes ...` from every independent replay.
The JSON records all sixteen canonical maps, the factored leading
determinants, and the exact derivative table. The producer checks the
all-t reference family, both necessity ranks, the nonsingular Jacobian,
and the exact factored A-cap identity.
