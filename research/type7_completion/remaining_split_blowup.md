# Split-pair cap with four positive partner weights

This excludes the 16 two-line blow-up orders whose checked canonical
representative is

\[
A=(0,0,\tfrac12,\tfrac12),\qquad
B=(0,-u,0,\tfrac12-u),\qquad 0<u<\tfrac12.
\]

The entries are ordered as `A=(0,1,4,5)` and `B=(2,3,6,7)` and give the
original physical horizontal coordinates on the two stretched lines.
The A edges `01` and `45` collapse, while all four B edge weights have
positive limits. The two stretched lines are distinct. Physical lengths
are measured by the original horizontal seminorm, not the Euclidean
length in the stretched picture.

The result excludes these blow-up limits of an unbounded sequence. It
does not supply an explicit height threshold or exclude the entire
ray-3 marking at the target height.

## 1. Checked order cover and short-edge directions

`remaining_split_blowup.py` reuses the complete 1,888-model orientation
formula and the exact 624 zero-stress two-line order cover. Exactly 16
orders map to the displayed representative by one of the 16 checked
phase symmetries and a horizontal reflection. Eight have the collapsed
pair in cap A and eight in cap B.

Choose the intrinsic-face `023` spatial gauge. Write the incidence
coordinates as

\[
P_i=(U_i,Z_i,c_i-2tH_i),\quad t=y^{-2},\quad c_i=\mathbf1_{i\in B}.
\]

Here `U2=x2`, `U3=x3`, `H2=gamma2`, `H3=gamma3`, and `Z2=Z3=0`.
Reflect the normal axis if necessary and set \(\delta=Z_4>0\). The
two-line blow-up has

\[
(Z_1,Z_4,Z_5,Z_6,Z_7)/\delta\longrightarrow(0,1,1,0,0).
\]

After a bounded affine shear placing the B-line origin at zero, the
stretched transverse macro coordinates can be written as

\[
A_0=A_1=(0,0),\quad A_4=A_5=(\tfrac12,1),\qquad
B_2=B_6=(0,0),\quad B_3=(-u,0),\quad B_7=(\tfrac12-u,0).
\]

The checker retains the separately normalized directions of edges `01`
and `45`. A bracket containing one of these edges is divided by that
edge's positive stretched length before taking the limit. The relative
axial bound makes the normalized third-coordinate increment tend to
zero. Brackets whose limiting determinant is zero impose no sign.

All coefficient signs are checked over the whole interval
\(0<u<1/2\): each is affine in \(u\), and its two endpoint values have
the same weak sign with at least one nonzero. No parameter sample is
used to justify an interval-wide sign.

The necessary orientation formula forces

\[
01\longrightarrow-\text{B-line direction},\qquad
45\longrightarrow+\text{B-line direction}.
\]

The CNF expressing a failure of either conclusion is independently
`UNSAT`. Put \(a=h_{01}>0\) and \(b=h_{45}>0\). The physical edge
norms and these forced stretched directions then give

\[
U_1/a\to-1,\quad (U_5-U_4)/b\to1,\qquad
Z_1=o(\delta a),\quad Z_5-Z_4=o(\delta b).
\tag{1}
\]

This argument allows every relative rate of \(a,b,\delta,t\).

## 2. A regular metric chart at the two collapsed edges

Use the three free intrinsic parameters

\[
x_1=-a,\qquad x_3=x_2-u,\qquad x_5=x_4-b.
\]

The other 21 intrinsic and spatial axial/horizontal variables are
dependent. The five normal coordinates \(Z_i\), \(i=1,4,5,6,7\), are
external parameters. Replace the two short-edge metric equations by
the signed length defects

\[
\mu_a=a+U_1,\qquad \mu_b=b-(U_5-U_4).
\tag{2}
\]

The regularized equations have an exact flat solution for every
\(a,b,u,t\). Its intrinsic horizontal and spatial horizontal coordinates
are

\[
x=(0,-a,u-a,-a,b-a,-a,\tfrac12-u-a,-a),
\]
\[
U=(0,-a,u-a,-a,\tfrac12-a-b,\tfrac12-a,u-a,\tfrac12-a).
\]

Its normal coordinates vanish and \(H=\gamma\). With \(q=4u-1\), the
seven nonzero-index intrinsic axial coordinates are

\[
\begin{aligned}
\gamma_1&=-aq/2,&
\gamma_2&=(1-4a)q/8,&
\gamma_3&=\gamma_2+u/2,\\
\gamma_4&=(1-2a-2b)q/4,&
\gamma_5&=(1-2a)q/4,&
\gamma_6&=\gamma_2,&
\gamma_7&=(1-4aq)/8.
\end{aligned}
\]

The checker substitutes this family into all 21 metric equations and
obtains the zero polynomial, including all terms involving \(t\).
Separately, the limiting affine stress equations have rank 14 and the
cross-distance height equations have rank 5. They force the corner
values of this family for every actual realization approaching the
displayed macro geometry.

At \(a=b=t=0\), the 21-by-21 Jacobian of the regularized system has
determinant

\[
-4096u(2u-1)^2\ne0.
\tag{3}
\]

The implicit-function chart is therefore uniform near any limiting
\(u\in(0,1/2)\), including \(a=b=0\). This removes both disappearing
edge lengths from its denominators.

## 3. Both defects are negligible compared with the squared width

Let

\[
D_a=H_1-\gamma_1,\qquad
D_b=(H_5-H_4)-(\gamma_5-\gamma_4).
\]

The exact flat family has \(D_a=D_b=0\). Normal coordinates enter the
regularized equations only through quadratic expressions. Smoothness
of the regular chart consequently gives, uniformly along the sequence,

\[
|D_a|+|D_b|\le C\bigl(|\mu_a|+|\mu_b|+\delta^2\bigr).
\tag{4}
\]

Restore the two omitted metric equations. They are exactly

\[
\mu_a(2a-\mu_a)=Z_1^2+t(H_1^2-\gamma_1^2),
\]
\[
\mu_b(2b-\mu_b)=(Z_5-Z_4)^2+
t\bigl((H_5-H_4)^2-(\gamma_5-\gamma_4)^2\bigr).
\tag{5}
\]

By (1), the two denominators on the left are comparable to \(a\) and
\(b\). The established relative axial estimates bound the sums of the
two axial increments by \(Ca\) and \(Cb\). Equations (1), (4), and
(5), with \(M=|\mu_a|+|\mu_b|\), imply

\[
M\le o(\delta^2(a+b))+Ct(M+\delta^2).
\]

Absorb \(CtM\) for sufficiently small \(t\). Since \(a,b,t\to0\),

\[
\boxed{\ |\mu_a|+|\mu_b|=o(\delta^2).\ }
\tag{6}
\]

No lower bound on either edge, and no comparison between their rates,
has been used.

## 4. The nonedge `26` has a forced second-order displacement

The exact flat family has \(U_6=x_2\) and \(H_6=\gamma_2\) for every
\(a,b,u,t\). The checker computes the following derivatives of the
regular solution at \(a=b=t=0\). The columns are the coefficients of
\(\mu_a,\mu_b,\delta^2\), with normal profile \((0,1,1,0,0)\):

| Quantity | \(\mu_a\) | \(\mu_b\) | \(\delta^2\) |
|---|---:|---:|---:|
| \(U_6-x_2\) | \((1-2u)/2\) | \(u\) | \(-1/2\) |
| \(H_6-\gamma_2\) | \((2u-1)/4\) | \(u/2\) | \(-(4u-1)/4\) |

The all-parameter flat identity removes any error independent of the
defects and normal coordinates. Smoothness, the normal profile, and (6)
therefore imply

\[
U_6-x_2=-\tfrac12\delta^2+o(\delta^2),\qquad
H_6-\gamma_2=O(\delta^2).
\tag{7}
\]

In particular, the vertices `2` and `6` have a nonzero transverse
separation for every sufficiently late member of the sequence.

Normalize that separation in the stretched plane by

\[
\kappa=\max\{\delta^2,|Z_6|/\delta\}>0.
\]

After taking a subsequence its normalized transverse direction
\((d_x,d_y)\) is nonzero and satisfies \(d_x\le0\). If
\(\kappa=\delta^2\), its horizontal component tends to \(-1/2\);
if \(\kappa=|Z_6|/\delta\), its vertical component has absolute value
one. Equation (7) also gives

\[
\frac{2t(H_6-\gamma_2)}{\kappa}=O(t)\longrightarrow0.
\]

Thus this normalized nonedge direction is planar even though no
relative axial estimate for arbitrary nonedges was assumed. The bounded
shear used in Section 1 changes its horizontal increment only by
\(O(t\delta^2)\), preserving the limiting conclusion \(d_x\le0\).

## 5. The final finite contradiction

Retain the already forced directions `01=-B` and `45=+B`, and add the
virtual direction of `26`. For every bracket containing `26`, divide
by \(\kappa\); when it also contains `01` or `45`, divide by that
edge's own positive scale as well. Multilinearity makes these joint
normalizations exact without a relative-scale hypothesis. All normalized
third-coordinate increments vanish by the preceding estimates.

The resulting directional atoms are \(d_x,d_y\), and
\(F=d_y-2d_x\). The checker adds their exact sign-addition consequences,
the nonzero-direction disjunction, and \(d_x\le0\). Every coefficient
sign is again checked throughout \(0<u<1/2\). Zero limiting brackets
remain unrestricted. The full necessary orientation/linking formula
with these conditions is `UNSAT`.

An independent exhaustive Boolean checker confirms the first direction
implication in 345 search nodes and the final contradiction in 11 nodes.
The proof does not use the separate 78 finite-height chamber exclusions.

## Reproduction

```sh
python3 research/type7_completion/remaining_split_blowup.py /tmp/type7-split
g++ -O3 -std=c++17 research/orientation_checkpoint/check_unsat.cpp -o /tmp/type7-sign-check
/tmp/type7-sign-check < /tmp/type7-split/split_required_directions.cnf
/tmp/type7-sign-check < /tmp/type7-split/split_nonedge26.cnf
```

The exported `split_model_coverage.cnf` is the same base formula with all
1,888 primary models blocked. Its clause multiset was checked equal to
the independently RUP-verified chamber coverage formula. The exported
`split_cells.json` records a checked canonical map for each of the 16
orders.
