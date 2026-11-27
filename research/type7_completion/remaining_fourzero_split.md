# Four zero weights: a triple cluster and two pairs

This excludes the remaining **32** four-zero two-line orders. Together
with the separate 48-order proof in `remaining_fourzero_blowup.md`, it
excludes all 80 orders with two vanishing short weights in each cap.
The canonical rank orders are

\[
A=(0,0,0,1),\qquad B=(0,1,1,0),
\]

where `A=(0,1,4,5)`, `B=(2,3,6,7)`, and the physical distance between
ranks 0 and 1 is `1/2`. The checker records a marked phase symmetry and
horizontal reflection taking every one of the 32 orders to this form.
This is an obstruction to unbounded sequences with this blow-up limit.
It does not give an explicit height threshold or finish a whole marking.

The decisive extra direction is that of the coincident **nonedge 04**.
A regular four-defect metric chart shows that its first nonzero physical
horizontal displacement has the opposite sign from the small edge 01.
Keeping that nonedge at its own scale makes all three necessary
orientation formulas contradictory.

## 1. The four edge directions

Let `E` and `F` be the distinct stretched transverse lines of A and B,
with positive physical horizontal increments `1/2`. Normalize each of

\[
a=01,\quad b=14,\quad c=36,\quad d=72
\]

separately. The height implications already proved in
`remaining_fourzero_blowup.md` apply to this binary corner as well.
After adding these individually verified implications, the necessary
orientation formula forces

\[
a_x\leq0,\quad a_y\leq0,\quad a\ne0,
\qquad b\parallel+E,\quad c\parallel-E,\quad d\parallel+E.
\tag{1}
\]

The checker proves (1) for all three possible relative scales of 01
and 14 by adding its negation to each formula and checking `UNSAT`.
It reconstructs every used height implication from the exact relative
stress identities, rank-14 corner system, checked symmetry, and linear
interval sign test. Enumeration only selects useful valid implications;
missing a suggested implication could not make the final formula
unsound. Both global orientations and all zero sign boundaries remain.

Every vector in (1) has nonzero physical horizontal projection. Thus
its stretched length is comparable to its actual short weight, and
its normal displacement is `O(δ h)` when its weight is `h`. This
conclusion holds for each edge independently; their ratios are free.

## 2. A regular chart through four zero edges

Use the exact face-023 gauge from `remaining_null_chart.md`:

\[
r_i=(U_i,-y c_i/2+H_i/y,Z_i),\qquad t=y^{-2},
\]

where `c_i` is 0 on A and 1 on B. The anchors have

\[
U_0=H_0=Z_0=0,\quad
(U_2,H_2,Z_2)=(x_2,\gamma_2,0),\quad
(U_3,H_3,Z_3)=(x_3,\gamma_3,0).
\]

Here `U` points opposite the positive physical horizontal direction
used in the canonical order: the limiting B step 23 has `U` increment
`−1/2`. Reflect the normal coordinate, if needed, and put `δ=Z5>0`.
The two-line limit gives

\[
Z_5=\delta,\qquad Z_1,Z_4,Z_6,Z_7=o(\delta).
\tag{2}
\]

There are 24 intrinsic/extrinsic variables before choosing the three
free weights. Choose

\[
a=h_{01},\quad c=h_{36},\quad d=h_{27},\qquad
x_1=-a,\quad x_6=x_3+1/2-c,\quad x_7=x_2-1/2+d.
\]

Write `b=h14`, now a dependent variable. Replace the four small-edge
metric equations by their signed horizontal defects:

\[
\begin{aligned}
\mu_a&=a-U_1,&
\mu_b&=b+U_4-U_1,\\
\mu_c&=c-U_6+U_3,&
\mu_d&=d-U_7+U_2.
\end{aligned}
\tag{3}
\]

The signs in (3) are forced by (1). The resulting system has 21
equations in 21 dependent variables. At `a=c=d=t=0` its exact Jacobian
determinant is

\[
\boxed{2048}.
\tag{4}
\]

The corner values are independently forced by the rank-14 affine
stress equations and rank-5 anchor-distance equations. They are not
assumed from the reference family below. The relevant spatial values
are `U1=U4=0`, `U5=−1/2`, `U6=0`, `U7=1/2` and
`H1=H4=0`, `H5=−3/4`, `H6=−1/8`, `H7=1/8`.

Equation (4) gives one uniform smooth implicit solution near the
corner, including arbitrarily unequal positive values of the three
free weights and the dependent fourth weight.

## 3. An exact reference family for every t

A reference solution with `Z=0` is obtained from the exact flat family
by the checked phase symmetry

\[
p=(1,0,7,6,5,4,3,2),\qquad A_p=-I,
\]

using its original parameters `r=a`, `u=1/2−c`, `z=d`. Translating
vertex 0 and placing face 023 in the stated gauge gives an exact
planar family. The gauge change is the rational isometry

\[
M=\frac1{4+t(4a-1)^2}
\begin{pmatrix}
4-t(4a-1)^2&4(4a-1)\\
-4t(4a-1)&4-t(4a-1)^2
\end{pmatrix}
\]

on the two coordinates `(U,−c_i/2+t H)`, whose metric is
`diag(1,1/t)`. The checker verifies `Mᵀ diag(1,1/t) M=diag(1,1/t)`
and all 24 original metric equations by exact rational identities.
The denominator tends to 4 and is positive for `t≥0`.

The key features of this family, denoted by a superscript `0`, are

\[
b^0=a,\qquad U_4^0=H_4^0=\gamma_4^0=0,
\tag{5}
\]

and

\[
\mu_a^0=\mu_b^0=
\frac{8a^2t(4a-1)}{4+t(4a-1)^2},\qquad
\mu_c^0=\mu_d^0=0.
\tag{6}
\]

The reference defects need not vanish. For each of the four edges,
its reference axial increments and defect divided by its own weight
extend smoothly to the corner. The checker verifies this divisibility
and the regular denominators explicitly. Thus their relative bounds
are uniform even as one weight becomes much smaller than the others.

## 4. Comparing defects without dividing by another edge

Put

\[
\bar\mu_i=\mu_i-\mu_i^0,\qquad M_\mu=\sum_i|\bar\mu_i|.
\]

The regular implicit solution and its quadratic dependence on the
normal coordinates give the uniform estimate

\[
\|\text{actual variables}-\text{reference variables}\|
 =O(M_\mu+\delta^2).
\tag{7}
\]

This includes `b−a`, all axial increments, and all horizontal
coordinates. No division by a collapsing weight occurs in (7).

For any one of the four removed edges, let `h` be its actual weight,
`μ` its signed defect, `D=ΔH−Δγ`, and `S=ΔH+Δγ`. Its exact metric
equation is

\[
\mu(2h-\mu)=(\Delta Z)^2+tDS.
\tag{8}
\]

The relative axial bounds give `|D|,|S|≤C h`. By (1), the signed
horizontal projection divided by `h` tends to 1, so `|μ|≤h/2`
eventually. The same statements hold for the reference family by the
explicit checks following (6).

The function

\[
F(D,S,h,\mu)=\frac{DS}{2h-\mu}
\]

is uniformly Lipschitz on the convex relative cone

\[
h>0,\qquad |D|,|S|\leq C h,\qquad |\mu|\leq h/2.
\tag{9}
\]

Indeed its four first derivatives are uniformly bounded there:
`S/(2h−μ)`, `D/(2h−μ)`, `−2DS/(2h−μ)²`, and `DS/(2h−μ)²`.
This comparison remains uniform when the actual and reference weights
differ, including the dependent pair `b` and `a`.

Subtract the reference version of (8), after division by `2h−μ`.
The normal bound `ΔZ=O(δ h)` from (1), the Lipschitz estimate, and
(7) give

\[
|\bar\mu_i|\leq C\delta^2 h_i+Ct(M_\mu+\delta^2).
\]

All four `h_i` tend to zero. Summing and absorbing the `Ct Mμ` term
therefore proves

\[
\boxed{M_\mu=o(\delta^2)}.
\tag{10}
\]

In particular this argument imposes no comparison of a short weight
with `t`, `δ`, another short weight, or the new nonedge scale.

## 5. The forced nonedge displacement

Differentiate the regular system in the normal-square profile (2).
The exact inverse Jacobian gives the responses

| Quantity | Coefficient of `δ²` |
|---|---:|
| `U4` | `−1/2` |
| `H4` | `−1/4` |
| `γ4` | `−1/4` |
| `h14` | `1/2` |

The checker derives these coefficients from the 21 equations rather
than treating them as certificate inputs. Smooth dependence, (5), and
(10) now give

\[
U_4=-\delta^2/2+o(\delta^2),\qquad
H_4=-\delta^2/4+o(\delta^2).
\tag{11}
\]

Define the positive nonedge normalization

\[
\kappa=\max\{\delta^2,|Z_4|/\delta\}.
\]

In the stretched `E,F` basis, the normalized nonedge 04 has a nonzero
subsequential limit `e=(e_x,e_y)`. Equation (11) and the negative
orientation of `U` give

\[
e_x+e_y\geq0.
\tag{12}
\]

Its axial increment divided by `κ` tends to zero, because
`t H4/κ=O(t)`. The two moving transverse basis vectors have horizontal components
`−1/2+o(1)`, so replacing their components by `−1/2` changes the
horizontal expression by `o(κ)`. The axial shear contributes a further
`O(t κ)`. Both errors divided by `κ` tend to zero and preserve (12). If `κ≫δ²`, its physical projection can be zero;
this boundary is explicitly retained.

## 6. The final three orientation contradictions

Keep the normalized directions `a=01` and `e=04` independently.
They have three possible scale relations. In a common leading
normalization the direction of 14 is respectively `−a`, `e−a`, or
`e`. In the comparable case the positive limiting ratio is absorbed
into `a` and `e`. The difference cannot vanish, since `a_x+a_y<0`
and `e_x+e_y≥0`.

The checker uses the following formal points, with positive small
parameters:

\[
\begin{array}{c|c@{\quad}c|c}
0&(0,0,0)&1&(\epsilon a_x,\epsilon a_y,0)\\
4&(\kappa e_x,\kappa e_y,0)&5&(1,0,0)\\
2&(0,0,1)&3&(0,1,1)\\
6&(-\zeta,1,1)&7&(-\eta,0,1).
\end{array}
\]

For each bracket it divides out the actual factors associated with
01, 04, 36, and 27 whenever the corresponding pair is present. In
particular a bracket containing 014 is divided by `εκ`, retaining
`det(a,e)` at unequal scales. A bracket containing 14 but not 0 uses
the common 01/04 cluster scale. Every resulting expression is checked
to be a previously constrained determinant or component.

The necessary formulas retain the full original topology, the
component inequalities in (1) and (12), nonzero `a` and `e`, the
positive-E direction of 14, exact vector-addition sign relations, and
all rank-two determinant sign identities. Vanishing leading brackets
remain unrestricted. All three formulas are `UNSAT`.

## Reproduction and independent checks

```sh
python3 research/type7_completion/remaining_fourzero_split.py /tmp/type7-fourzero-split
g++ -O3 -std=c++17 research/orientation_checkpoint/check_unsat.cpp -o /tmp/type7-sign-check
```

The script emits three `fourzero_split_directions_*.cnf` formulas and
three `fourzero_split_nonedge04_*.cnf` formulas. Replay all six with the
independent checker and require explicit `UNSAT nodes ...` output.
The cell ledger binds the result to all 32 marked orders; the proof
ledger includes every exact relative-height implication. The exported
model-coverage formula is the same clause multiset as the independently
RUP-checked 1,888-model coverage formula used by the chamber compiler.

Neither numerical algebra nor a nonlinear solver result is used in
this proof. The exact symbolic checks establish the algebraic premises;
the displayed uniform implicit-function and relative-cone argument
establishes the scale-independent consequence; the independent Boolean
checks finish the finite cases.
