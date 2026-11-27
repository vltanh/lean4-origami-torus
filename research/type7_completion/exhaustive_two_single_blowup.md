# Ray 3: the remaining two-line orders with one collapsed edge per cap

## Result and coverage

A common-line ray-3 sequence cannot have a first transverse blow-up of
this form, with cyclic labels `A=(0,1,4,5)` and `B=(2,3,6,7)`:

```
A=(0,0), (r,0), (r,0), (1/2,0),
B=(0,0), (-1/2,-1/2), (-u,-u), (-u,-u),
0<r,u<1/2.
```

The physical limiting norm is the original horizontal seminorm
`|Delta X|`. Thus the short weights are

```
A: (r,0,1/2-r,1/2),   B: (1/2,1/2-u,0,u).
```

Edges 14 and 67 collapse. The complete two-line weak-order cover has
48 orders with exactly one zero weight in each cap. The verifier
`exhaustive_two_single_blowup.py` selects exactly 16 and maps each to
this picture by a checked marking-preserving symmetry and horizontal
reflection. It records the other 32 separately. The proof here concerns
these 16 only.

Only edge 67 needs an independently normalized direction. Its forced
transverse direction makes the cap determinant `[2367]` strictly
positive, contradicting its necessary weak sign. This is an asymptotic
research exclusion under the existing geometric necessity audit, not a
fixed-height or Lean theorem.

## 1. A finite implication for the virtual edge 67

Give the two caps axial levels zero and one. The displayed picture has
25 nonzero four-point determinants. Fix their signs in the complete
necessary orientation, embedding, and linking CNF, allowing either
global orientation. All other limiting brackets remain free.

Normalize the actual edge 67 at its own stretched scale and write its
nonzero limiting transverse direction as `(d_x,d_y)`. The thirteen
nonzero linear determinant terms containing this edge are positive or
negative multiples of `d_y` or `d_x-d_y`. For example,

\[
 [0167]/m\to-rd_y,
 \qquad [0267]/m\to u(d_x-d_y),
 \qquad [0367]/m\to(u-\tfrac12)(d_x-d_y).       \tag{1}
\]

The common positive stretching factor is implicit. Every link factors
the actual edge 67 before taking the limit. The verifier computes all
thirteen factors symbolically. Every scalar coefficient has a fixed
sign throughout `0<r,u<1/2`; no parameter sampling is used to establish
that sign.

Three ternary variables represent the signs of `d_x`, `d_y`, and
`d_x-d_y`. Their necessary addition rule and nonzero-direction condition,
together with the thirteen links, imply

\[
 d_x<0,\qquad d_y=0,\qquad \chi_{2367}<0.       \tag{2}
\]

The negation of this conjunction is UNSAT: 415 variables and 8,448
clauses. In particular, every actual completion has `[2367]≤0`.
No direction for edge 14 and no comparison of the two edge lengths is
used.

## 2. An exact positive coordinate change fixes the orientation

Use the face-023 incidence chart `(U_i,Z_i,H_i)` with

\[
 H_i=c_i-2t\zeta_i,
 \qquad t=1/y^2,
\]

and anchors

\[
 (U_0,Z_0,\zeta_0)=(0,0,0),\quad
 (U_2,Z_2,\zeta_2)=(x_2,0,\gamma_2),\quad
 (U_3,Z_3,\zeta_3)=(x_3,0,\gamma_3).
\]

Choose the normal reflection so that `Z5<0`, and put `delta=-2 Z5>0`.
The two distinct blown-up lines give

\[
 Z_i/\delta\to-\text{(horizontal A coordinate)}
 \quad(i\in A),
 \qquad Z_i/\delta\to0\quad(i\in B).           \tag{3}
\]

The exact transformation to the picture in section 1 is

\[
 X_i=U_i-\frac{x_2}{H_2}H_i,
 \qquad Y_i=X_i+Z_i/\delta,
 \qquad \widehat H_i=H_i/H_2.                  \tag{4}
\]

Its determinant is `1/(delta H2)>0`, since `H2→1`. Thus the signs in
(2) are also the signs of determinants in the face chart. This explicit
orientation check matters: the alternative moving frame with transverse
anchors `05` and `23` has negative determinant for this picture.

Let `eta=h67>0` and use the scale

\[
 m=\max(|\Delta X_{67}|,|\Delta Y_{67}|).
\]

The uniform relative metric bounds give

\[
 |\Delta\zeta_{67}|=O(\eta),\qquad
 \Delta H_{67}=O(t\eta),\qquad
 (\Delta U_{67})^2+(\Delta Z_{67})^2
       =\eta^2(1+O(t)).                        \tag{5}
\]

Since `Delta Z=delta(Delta Y-Delta X)` and
`Delta U=Delta X+O(t eta)`, these imply `m≥c eta` for a fixed positive c.
The normalized axial coordinate is therefore `O(t eta/m)→0`, so the
virtual direction used above is nonzero and legitimate.

Equation (2), with maximum-norm normalization, gives
`Delta X/m→-1` and `Delta Y/m→0`. Combining with (5) yields

\[
 \eta/m\to1,\qquad
 \Delta U_{67}/\eta\to-1,\qquad
 \frac{\Delta Z_{67}}{\delta\eta}\to1.         \tag{6}
\]

These comparisons are consequences of the necessary signs. No lower
bound on eta and no relation between delta and t is assumed.

## 3. The needed metric limits are uniquely forced

The sixteen cross-stress identities and eight limiting short-weight
equations form a `24×14` affine system in the intrinsic x/gamma variables.
The verifier checks rank 14 and the unique solution

\[
\begin{aligned}
 x&=(0,-r,\tfrac12-u,-u,\tfrac12-r,0,0,0),\\
 \gamma&=(0,r/2,\tfrac18-u/2,\tfrac38-u/2,
                 r/2,\tfrac14,\tfrac18,\tfrac18).
\end{aligned}                                                   \tag{7}
\]

The fourteen non-anchor cross-edge equations have rank five in the five
free zeta coordinates. Substitution verifies the necessary solution

\[
\begin{aligned}
 \zeta_1=\zeta_4&=r/2-4ru,\qquad
 \zeta_5=\tfrac14-2u,\\
 \zeta_6=\zeta_7&=4u^2-2u+\tfrac18,
 \qquad\zeta_2=\gamma_2,\quad\zeta_3=\gamma_3.
\end{aligned}                                                   \tag{8}
\]

In particular, in the face chart,

\[
 h_{23}\to\tfrac12,\quad
 \gamma_{23}\to\tfrac14,\quad
 U_6-U_2\to-u,\quad
 \zeta_6-\gamma_2\to4u^2-\tfrac32u.            \tag{9}
\]

These are necessary limits of every realization; a planar reference
solution at positive t is not being assumed.

## 4. The B-cap determinant has the forbidden sign

Subtracting endpoints in the actual cap determinant gives the exact
identity

\[
\begin{aligned}
 [2367]=2t\{&Z_6(h_{23}\Delta\zeta_{67}
                         +\gamma_{23}\Delta U_{67})\\
             &-\Delta Z_{67}
               [h_{23}(\zeta_6-\gamma_2)
                         +\gamma_{23}(U_6-U_2)]\}.
\end{aligned}                                                   \tag{10}
\]

The bracketed coefficient in the second line converges, by (9), to

\[
 \tfrac12(4u^2-\tfrac32u)+\tfrac14(-u)
       =-u(1-2u)<0.                            \tag{11}
\]

The first line divided by `delta eta` tends to zero: `Z6/delta→0`,
while both edge increments in parentheses are `O(eta)` by (5).
Using (6) in the second line therefore gives

\[
 \boxed{\displaystyle
 \frac{[2367]}{2t\delta\eta}\longrightarrow u(1-2u)>0.}
                                                               \tag{12}
\]

Thus the actual cap determinant is positive eventually, contradicting
`[2367]≤0` from (2). The edge-relative estimate in the first line of
(10) is what makes this argument uniform when eta, delta, and t vanish
at unrelated rates.

## Reproduction

```sh
python3 research/type7_completion/exhaustive_two_single_blowup.py /tmp/type7-two-single
g++ -O3 -std=c++17 research/orientation_checkpoint/check_unsat.cpp -o /tmp/type7-two-single-checker
/tmp/type7-two-single-checker < /tmp/type7-two-single/two_single_virtual67.cnf
/tmp/type7-two-single-checker < /tmp/type7-two-single/two_single_model_coverage.cnf
```

Require explicit `UNSAT nodes ...` output from both independent replays.
The JSON output records the sixteen canonical maps, the thirty-two
other one-zero-per-cap orders, and all thirteen factored direction links.
The symbolic checks verify the two necessity ranks, the exact determinant
identity, its strict limiting coefficient, and the positive coordinate
change.
