# Ray 3: all two-line blow-ups with exactly three zero weights

## Result and finite cover

No common-line ray-3 sequence can have a first transverse blow-up onto
two distinct lines with exactly three vanishing limiting short-edge
weights. The proof covers every relative rate of the collapsing edges,
the transverse width, and `t=1/y²`.

The complete weak-order cover contains 176 such orders: 88 have two zero
A weights and one zero B weight, and 88 have the reverse distribution.
The verifier `exhaustive_three_zero_blowup.py` maps all of them by the
checked marked symmetries and horizontal reflection to the six families
below. Each cap has perimeter one in the original horizontal seminorm.

For the first five families use a moving affine frame
`0=(0,0,0), 2=(0,0,1), 5=(1,0,0), 7=(0,1,1)`. Its transverse basis
vectors are denoted E and F. The limiting A cap is a triple cluster
`A0=A1=A4=0`, with tip `A5=E`. The B cap is
`(0,lambda F,mu F,F)` at axial level one.

| Case | Complete B parameter cell | Collapsed B edge | Marked orders |
|---|---|---|---:|
| 0 | `0<lambda<1`, `mu=1` | 67 | 32 |
| 1 | `lambda<0`, `mu=1` | 67 | 32 |
| 2 | `lambda>1`, `mu=1` | 67 | 32 |
| 3 | `lambda=0`, `mu<0` | 23 | 32 |
| 4 | `lambda=mu<0` | 36 | 32 |
| 5 | Split A: `A0=A1=0`, `A4=A5=E`; B is `(0,F,lambda F,lambda F)`, `0<lambda<1` | 67 | 16 |

The canonical maps are checked against all 176 rows from
`common_line_edge_collapse.check`, not inferred from a few pictures.
This is an asymptotic research theorem under the existing geometric
necessity audit, not a fixed-height or Lean exclusion.

## 1. Three independently normalized virtual edges

For the triple-cap cases put `a=01` and `b=14`, with intrinsic weights
alpha and beta. Normalize each edge at its own stretched transverse
maximum norm. There are three exhaustive subsequence cases: a dominates,
the scales are comparable, or b dominates. In the comparable case the
sum `A=a+b` is normalized by their common maximum; its limit may be zero.
In the other cases its normalized direction agrees with the dominant
edge. No relation to the collapsing B edge's scale is assumed.

The two-edge formula in `remaining_two_line_triple.py` already records
all nonzero leading brackets, the coordinate-sum sign rules, and the
sign of `det(a,b)`. Add the independently normalized collapsed B edge d.
The exact planar rank-two relations for `E,F,a,b,d` constrain the signs
of `det(a,d)` and `det(b,d)`. The sum rule also constrains `det(A,d)`.

Fourteen additional four-point brackets factor d, or a product of d and
one A edge. Every scalar coefficient is a signed difference of two B
positions. Its sign is constant throughout the corresponding full
parameter cell in the table. The verifier checks this symbolic factor
property before evaluating a representative of the cell.

For the split case use `a=01`, `c=45`, and `d=67`, with three independent
scales. The same construction for `E,F,a,c,d` has twenty nonzero constant
brackets and forty factored direction links. All coefficients are
`±1`, `±lambda`, or `±(lambda-1)`.

These are necessary sign statements even for arbitrarily short edges.
Subtracting endpoints factors each actual edge before division. Relative
axial increments are `O(t h)`; after division by an edge's stretched
scale they tend to zero. A bracket containing two collapsed edges is
divided by the product of their own scales. No convergence rate for an
unrelated point is used. Leading zero brackets impose no sign condition.

## 2. The finite consequences

Sixteen CNFs cover all cases and A-scale hierarchies. Nine are directly
UNSAT. The other seven are UNSAT implications establishing the following
complete list of remaining patterns and necessary cap signs.

| Case | Remaining hierarchy | Required directions | Required generic cap sign |
|---|---|---|---|
| 0 | b dominates a | `a=-F`, `b=-E` | `[0145]≥0` |
| 1 | none | — | — |
| 2 | any of the three | `d67=-E` | `[2367]≥0` |
| 3 | a dominates b | `a=E`, `b=F` | `[0145]≤0` |
| 4 | a dominates b | `a=E`, `b=F` | `[0145]≤0` |
| 5 | independent scales | `d67=-E` | `[2367]≥0` |

Here an equality to a signed basis vector specifies direction, not
length. The CNFs prove the direction and generic cap sign together.
The inequalities displayed are the resulting necessary inequalities for
actual, possibly zero, brackets.

Triple formulas have 433 variables and 9,966–9,997 clauses; the split
formula has 427 variables and 9,801 clauses. The complete 1,888-model
coverage formula is replayed separately.

## 3. Cases 3 and 4: endpoint versions of the height -4 argument

In physical horizontal coordinates both cases have

```
A=(0,0,0,1/2),
B=(0,u,v,-w),  w=1/2-v>0,
```

with `u=0` in case 3 and `u=v` in case 4. The already verified relative
identities in `remaining_two_line_triple.md` remain valid at both
endpoints. The coefficient matrices in the intrinsic reconstruction
have constant rank, and every limiting identity is polynomial in u and
v.

More explicitly, the forced physical unit direction of a is positive
horizontal. The limiting B short weights and signed steps are

\[
 (u,v-u,\tfrac12,w),\qquad(u,v-u,-\tfrac12,w).
\]

The four cross stresses involving a, divided by alpha, still converge
to `(0,0,1,0)`, including when the first or second B weight is zero.
Consequently

\[
 c_0/\alpha\to2,\quad\gamma_{01}/\alpha\to\tfrac12,
 \quad\rho_1/\alpha\to-\tfrac12-2v,
 \quad\rho_5\to\tfrac34-v.
\]

The forced directions have nonzero physical horizontal components.
They therefore compare the stretched scales with alpha and beta and
imply

\[
 a_x/\alpha\to2,\quad a_y/\alpha\to0,
 \quad b_x/\beta\to0,\quad b_y/\beta\to1/w,
 \quad\beta/\alpha\to0.
\]

Polarization along the actual axis 02 gives
`a_z/(t alpha)→-4` and `b_z=O(t beta)` in the moving frame. Hence

\[
 \frac{[0145]}{t\alpha\beta}
 =\frac{a_yb_z-a_zb_y}{t\alpha\beta}
 \longrightarrow\frac4w>0,
\]

contradicting the required nonpositive cap sign. A positive length for
the collapsed B edge is not used in this calculation.

## 4. Case 0: the reversed dominant edge has height +4

Use physical coordinates

```
A=(0,0,0,1/2),
B=(0,-u,-1/2,-1/2),  0<u<1/2.
```

The forced directions are `a=-F`, `b=-E`, and b dominates a. Since the
physical components of E and F are `1/2` and `-1/2`, respectively,

\[
 a_x/\alpha\to0,\quad a_y/\alpha\to-2,
 \quad b_x/\beta\to-2,\quad b_y/\beta\to0,
 \quad\alpha/\beta\to0.                        \tag{1}
\]

The rank-fourteen intrinsic stress reconstruction gives

\[
\begin{aligned}
 x&=(0,0,0,-u,\tfrac12,0,0,0),\\
 \gamma&=(0,0,-\tfrac18,u/2-\tfrac18,
                 0,\tfrac14,\tfrac18,\tfrac18).
\end{aligned}                                                   \tag{2}
\]

Let `g_b=gamma14`. The exact stress identity

\[
 R(14,23)=g_b+\beta/2
\]

has `R(14,23)/beta→0`: both normalized b and the noncollapsed B23 edge
point in the negative physical horizontal direction. Thus
`g_b/beta→-1/2`.

For squared spatial distances set

\[
 T_b=D_{14}+D_{12}-D_{24}.
\]

Direct expansion gives the exact identity

\[
 T_b=\beta(1-2x_2+2x_1)+g_b
                   +2t(\gamma_2-\gamma_1)g_b.                 \tag{3}
\]

Equations (2) and (3) imply `T_b/beta→1/2`. In actual physical vectors,

\[
 2b\mathbin{\cdot}r_2=T_b+2b\mathbin{\cdot}r_1.
\]

The last term divided by beta is `O(alpha)→0`. Thus the relative
polarization of b along 02 tends to `1/2`. Also (2) gives
`rho5=D05-D25+D02→3/4`. The normalized axial correction has prefactor
`1/(2|02|²t)→2`. Using (1) to change to the moving frame yields

\[
 \frac{b_z}{t\beta}\longrightarrow
       2\bigl(\tfrac12-(-2)\tfrac34\bigr)=4.                   \tag{4}
\]

The contribution of the F anchor vanishes because `b_y/beta→0`; its
axial correction divided by t is bounded. The corresponding bound for
the other short edge is `a_z=O(t alpha)`.

The exact cap identity now gives

\[
 \frac{[0145]}{t\alpha\beta}\longrightarrow(-2)4=-8<0,
\]

contradicting its required nonnegative sign. Every discarded remainder
has an explicit factor alpha or beta before division, so this is uniform
in all other collapse rates.

## 5. Cases 2 and 5: the common B-cap obstruction

Positively rescale the F coordinate so that B3 is its unit anchor.
Both cases then have physical coordinates

```
B=(0,-1/2,-u,-u),  0<u<1/2.
```

The A cap is `(0,0,0,1/2)` in case 2, and `(0,0,1/2,1/2)` in case 5.
In both cases d67 is forced to point along -E. The frame uses transverse
anchors `05` and `23`; relative to the positively oriented face-023
chart its determinant is negative. Thus the necessary nonnegative cap
in section 2 means a nonpositive `[2367]` in the face chart.

The proof of `exhaustive_two_single_blowup.md` now applies to the B cap.
For case 2 the rank-fourteen and rank-five identities there are evaluated
at `r=0`; their coefficient matrices remain full rank. For the split
case the verifier checks the separate necessary solution

\[
\begin{aligned}
 x&=(0,0,\tfrac12-u,-u,0,0,0,0),\\
 \gamma&=(0,0,\tfrac18-u/2,\tfrac38-u/2,
                 \tfrac14,\tfrac14,\tfrac18,\tfrac18),\\
 \zeta_1&=0,\quad
 \zeta_4=\zeta_5=\tfrac14-2u,\quad
 \zeta_6=\zeta_7=4u^2-2u+\tfrac18.
\end{aligned}
\]

The needed B quantities are identical in the two cases:

\[
 h_{23}\to\tfrac12,\quad\gamma_{23}\to\tfrac14,
 \quad U_6-U_2\to-u,\quad
 \zeta_6-\gamma_2\to4u^2-\tfrac32u.
\]

Let `eta=h67>0` and choose `delta=-2 Z5>0` in the face chart. The forced
virtual direction gives `Delta Z67/(delta eta)→1`; also `Z6/delta→0`.
The exact identity

\[
 [2367]=2t\{Z_6(h_{23}\Delta\zeta_{67}+\gamma_{23}\Delta U_{67})
 -\Delta Z_{67}[h_{23}(\zeta_6-\gamma_2)+\gamma_{23}(U_6-U_2)]\}
\]

therefore implies

\[
 \frac{[2367]}{2t\delta\eta}\longrightarrow u(1-2u)>0.
\]

This contradicts its required face-chart sign. The first term is
`o(delta eta)` by the edge-relative height bound, regardless of the
ratios of eta, delta, and t. These two cases complete the 176-order cover.

## Reproduction

```sh
python3 research/type7_completion/exhaustive_three_zero_blowup.py /tmp/type7-three-zero
g++ -O3 -std=c++17 research/orientation_checkpoint/check_unsat.cpp -o /tmp/type7-three-zero-checker
```

Replay all seventeen generated CNFs with the independent checker,
requiring explicit `UNSAT nodes ...` output. Sixteen are the direction
implications or direct contradictions; the seventeenth certifies the
complete 1,888-model cover. The JSON records every marked canonical map
and the symbolic factors of all added direction links. Exactly-four-zero
two-line orders and other blown-up shape classes are separate questions.
