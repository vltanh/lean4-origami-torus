# Ray 3: the two vertical-V four-zero endpoints

The two V-shaped endpoints left by the mixed four-zero directional
cover are impossible. This proof allows arbitrary relative rates of
the four small weights, the first normal width, and `t=1/y²`. It is an
asymptotic research exclusion, with no numerical height threshold and
no Lean theorem.

The complementary V is first reflected by the checked marked symmetry
`(0 4)(2 6)`. In the resulting labels both cases have

\[
 A=(0,0,0,\tfrac12E),\qquad a=01,\quad b=14.
\]

The opposite case has `B2=B6=0`, `B3=-E/2`, `B7=F`. The complementary
case has `B2=0`, `B3=B7=-E/2`, `B6=-E/2-F`. These are stretched
transverse coordinates; both caps also have their usual axial levels.

## 1. Necessary signs and the small vertical edge

The two finite implication certificates force a along positive E and
b along positive F, with a dominant in stretched norm. Both cap signs
are weakly negative:

\[
 [0145]\le0,\qquad[2367]\le0.                    \tag{1}
\]

In the opposite case they also force `[1247]≥0`, `[1467]≥0`; in the
complementary case they force `[1346]≤0`, `[1467]≥0`. Every zero
leading determinant remains unrestricted. The formula allows either
global orientation.

Use the face-023 incidence coordinates
`(U_i,Z_i,c_i-2tH_i)`, where `c_i=1` on B and zero on A. Write

\[
 \alpha=h_{01},\quad \beta=h_{14},\quad
 dU=U_4-U_1,\quad dZ=Z_4-Z_1.
\]

For the opposite case put `delta=Z7>0` and
`eta=h67+h72`; for the complementary case put `delta=-Z6>0` and
`eta=h36+h67`. All other normal coordinates are `o(delta)`. The
forced horizontal direction of 01 gives

\[
 U_1/\alpha\to1,\qquad Z_1=o(\delta\alpha).
                                                               \tag{2}
\]

The forced vertical direction of 14 gives
`kappa=dZ/delta>0`, `kappa→0`, and `dU=o(kappa)`.
The actual B short edges give `delta≤C eta`.

The same two-edge factoring used in
`remaining_three_adjacent_blowup.md`, Section 2, now gives

\[
 |dU|\le C\eta\kappa+Ct\beta.
\]

For the complementary case the transverse terms of its two signed
brackets, divided by delta, are respectively
`dU+kappa*(U6-U3)` and `-dU+kappa*(U7-U6)`. For the opposite case
they are the terms already displayed in that earlier proof. The
remaining terms are bounded by `Ct(beta+eta*kappa)`: factor the actual
14 edge and the named B edge before applying either relative height
bound. This is valid when alpha tends to zero as well.

The edge-14 norm estimate gives `beta≤C(|dU|+|dZ|)`. Absorbing `Ct beta`
therefore proves

\[
 \boxed{\ \beta=O(\eta\kappa)=o(\eta).\ }       \tag{3}
\]

## 2. Four-defect charts and exact reference families

Choose actual intrinsic parameters `alpha,beta,k`, with `k=h72` in
the opposite case and `k=h36` in the complementary case. Replace the
four vanishing-edge squared equations by their signed defect
definitions. There remain twenty-one equations for twenty-one planar
variables. Both Jacobian determinants at the endpoint are **2048**.
Their implicit solutions are analytic jointly in all free parameters,
t, the defects, and the five normal coordinates. Simultaneous normal
reflection makes the planar variables even in Z.

The usual constant affine stress and cross-height systems have ranks
fourteen and five. The checker verifies these ranks and the reference
substitutions, so the actual limiting branch is forced by the metric
constraints.

### Opposite reference

For every alpha and t, with all other parameters zero, an exact
solution of all the original metric equations is

\[
\begin{aligned}
 x&=(0,-\alpha,\tfrac12,0,\tfrac12-\alpha,0,0,0),\\
 \gamma=H&=(0,\alpha/2,\tfrac18,\tfrac38,\alpha/2,
                         \tfrac14,\tfrac18,\tfrac18),\\
 U&=(0,\alpha,\tfrac12,0,\alpha,\tfrac12,\tfrac12,\tfrac12).
\end{aligned}                                                    \tag{4}
\]

Define

\[
 p=\alpha-U_1,\quad m_b=\beta-dU,\quad
 m_c=h_{67}-(U_7-U_6),\quad m_d=h_{72}+U_7-U_2.   \tag{5}
\]

### Complementary reference

Put

\[
 q_0=\frac{4-3t}{4+t},\qquad
 v_0=\frac{t-12}{2(4+t)}.
\]

For every alpha and t the following is also an exact solution of all
the original metric equations:

\[
\begin{aligned}
 x&=(0,-\alpha,0,-\tfrac12,\tfrac12-\alpha,0,0,0),\\
 \gamma&=(0,\alpha/2,-\tfrac18,\tfrac18,\alpha/2,
                         \tfrac14,\tfrac18,\tfrac18),\\
 U&=(0,\alpha q_0,0,-\tfrac12,\alpha q_0,q_0/2,-\tfrac12,-\tfrac12),\\
 H&=(0,\alpha v_0,-\tfrac18,\tfrac18,\alpha v_0,v_0/2,
                                                    \tfrac18,\tfrac18).
\end{aligned}                                                    \tag{6}
\]

Here `q0²+t v0²=1+t/4`. Use the centered first defect

\[
\begin{aligned}
 p&=\alpha-U_1-\frac{4\alpha t}{4+t},\qquad
 m_b=\beta-dU,\\
 m_c&=h_{36}+U_6-U_3,\qquad
 m_d=h_{67}-(U_7-U_6).
\end{aligned}                                                    \tag{7}
\]

The centering in p is essential: the uncentered defect is of order
`t alpha` already on the exact folded reference.

In both cases `mb=O(beta)=o(eta)` and `mc,md=O(eta)`. The exact
references remove every remainder depending only on alpha and t.

## 3. The horizontal-edge defect is smaller by a factor alpha

Distance subtraction gives the exact actual identity

\[
 (1-2t\gamma_3)(H_1-\gamma_1)=2x_3(U_1+\alpha).  \tag{8}
\]

For the opposite reference `x3=0`. Analyticity around (4) gives
`x3=O(eta+|p|+delta²)`. Combining (8) with the restored 01 equation
gives exactly

\[
 p=\frac{Z_1^2}{\alpha+U_1}
       +\frac{2t x_3(H_1+\gamma_1)}{1-2t\gamma_3}.
\]

Use (2), the relative bound `|H1+gamma1|≤C alpha`, and absorption of
the small multiple of `|p|`. Since `delta²=o(eta)`, this proves
`p=o(alpha eta)`.

For the complementary case the exact special stress identity is
`gamma1=alpha/2-R(01,36)`. Edge 36 is now small, so its relative norm
and gamma bounds give `gamma1/alpha=1/2+O(eta)`. Analyticity around
(6) gives `x3+1/2,gamma3-1/8=O(eta+|p|+delta²)`. Equation (8) then
yields

\[
 H_1/\alpha-v_0=O(|p|/\alpha+\eta+|p|).
\]

Subtract `q0²+t v0²=1+t/4` from the restored 01 equation divided by
`alpha²`. As `U1/alpha=q0-p/alpha`, absorption gives

\[
 |p|/\alpha\le o(\delta^2)+Ct\eta=o(\eta).
\]

Thus in both charts

\[
 \boxed{\ p=o(\alpha\eta).\ }                  \tag{9}
\]

## 4. Exact divisibility supplies the missing relative remainder

Let `W=H1-U1*H5/U5`. It vanishes on both exact references. More
strongly, in either modified chart it vanishes identically when
`alpha=p=Z1=0`, without setting any other small parameter to zero.
Indeed `x1=U1=Z1=0`, and the retained equation 13 factors as

\[
 (H_1-\gamma_1)\{1+t(H_1+\gamma_1-2\gamma_3)\}=0.
\]

Its second factor is nonzero, so `H1=gamma1`. The exact cross-edge
stress identity then gives
`gamma1*(1+t*(gamma6-H6))=0`, forcing both values to vanish.

Analytic division therefore writes

\[
 W=\alpha F+pG+Z_1J,
\]

with bounded analytic F,G and `J=O(|Z|)` by simultaneous normal
reflection. Both reference identities imply F has no term depending
only on alpha,t. Using (2), (3), and (9), the checked mixed derivatives
at the endpoint give the uniform expansions

\[
\begin{array}{ll}
 \text{opposite:}&W/\alpha=2m_c+m_d+o(\eta),\\
 \text{complementary:}&W/\alpha=2k-m_c+2m_d+o(\eta).
\end{array}                                                     \tag{10}
\]

In the first line the additional coefficient `-2mb` is negligible by
(3). The normal contribution is `O(delta²)=o(eta)`. This divisibility
argument, rather than an absolute Taylor remainder divided by alpha,
allows alpha to be arbitrarily smaller than all the other scales.

## 5. Two cap signs finish both cases

Factoring the actual edge 14 gives

\[
\begin{aligned}
 [0145]=2t\{&dZ(U_5H_1-U_1H_5)\\
 &+Z_5(U_1dH-H_1dU)+Z_1(dU H_5-U_5dH)\}.
\end{aligned}                                                   \tag{11}
\]

Here `dH=O(beta)`, `U1,H1=O(alpha)`, `Z5=o(delta)`, and
`Z1=o(delta alpha)`. After division by dZ, the two error terms in
(11) are `o(alpha eta)` by (3). Since `U5→1/2`, equations (1) and
(10) imply respectively

\[
 m_c+\tfrac12m_d\le o(\eta),\qquad
 (2k-m_c)/2+m_d\le o(\eta).                      \tag{12}
\]

Every short edge has `-Ct h≤h-signed(Delta U)≤(2+Ct)h`.
In the opposite case both negative parts in (12) are `o(eta)`, hence
`mc,md=o(eta)`. The checked first derivatives then give

\[
 h_{67}=o(\eta),\quad h_{72}/\eta\to1,
 \quad (U_6-U_2)/\eta\to-1,
 \quad (H_6-\gamma_2)/\eta\to-\tfrac32.          \tag{13}
\]

The exact B-cap identity from the adjacent-collision proof, using
`Z6=o(delta)` and `(Z7-Z6)/delta→1`, now gives
`[2367]/(2t delta eta)→1>0`, contradicting (1).

In the complementary case `2k-mc=k-(U6-U3)≥-Ct k`, so (12) gives
`md=o(eta)` and `2k-mc=o(eta)`. Its first derivatives give

\[
 h_{67}=o(\eta),\quad k/\eta\to1,
 \quad (U_7-U_3)/\eta\to1,
 \quad (H_7-\gamma_3)/\eta\to-\tfrac52.          \tag{14}
\]

Write `C=7-3`. The exact cap formula is

\[
\frac{[2367]}{2t}
 =Z_6(h_{23}C_H+\gamma_{23}C_U)
  -Z_7\{h_{23}(H_6-\gamma_3)+\gamma_{23}(U_6-U_3)\}.
\]

The second brace is `O(k)`, while `Z7=o(delta)`. In the first term,
`Z6/delta→-1`, `h23→1/2`, and `gamma23→1/4`. Equation (14) makes
its coefficient divided by eta tend to `-1`, giving again
`[2367]/(2t delta eta)→1>0`. This is the second contradiction.

## Reproduction

```sh
python3 research/type7_completion/exhaustive_four_cluster_v.py /tmp/type7-four-cluster-v
```

Replay both emitted CNFs with `research/orientation_checkpoint/check_unsat.cpp`
on standard input and require explicit `UNSAT nodes ...` output.
The exact symbolic checker verifies both all-t references, the constant
necessity ranks, the two determinant-2048 Jacobians, the target first
derivatives, the mixed W derivatives, and the identities supplying
the relative divisibility argument.
