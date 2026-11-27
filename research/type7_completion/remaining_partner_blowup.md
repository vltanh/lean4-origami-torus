# Ray 3: the unique collapsed edge cannot belong to the noncollinear cap

## Result and coverage

Consider a common-line ray-3 limit whose first normal blow-up has a
collinear cap A and a noncollinear cap B. There is no such sequence
with all four A weights positive and exactly one zero B weight.
No comparison of the normal width, collapsed edge length, and
`t=1/y²` is assumed.

The exact degenerate-norm cover has 32 such cells. Checked marked
symmetries and coordinate reflections put sixteen in each of these
families, with cyclic labels `A=(0,1,4,5)`, `B=(2,3,6,7)`:

| Family | Blown-up A coordinates | Blown-up B coordinates | Parameters |
|---|---|---|---|
| Collapsed base 67 | `(0,0),(r,0),(1/2,0),(r,0)` | `(0,0),(u,0),(1/2,1),(1/2,1)` | `0<r,u<1/2` |
| Collapsed leg 36 | `(0,0),(r,0),(1/2,0),(r,0)` | `(0,0),(1/2,0),(1/2,1),(z,1)` | `0<r,z<1/2` |

The verifier `remaining_partner_blowup.py` checks all 32 mappings and
the finite sign implications. Multiple-zero-weight cells are outside
this theorem. The result is an asymptotic research exclusion under the
existing geometric necessity audit, not a numerical-height or Lean
theorem.

## 1. The required signs and reference family

In both families the nonzero limiting mixed brackets force the same
four weak signs used in `remaining_flat_blowup.md`:

\[
 -[0124]\geq0,\quad [0146]\geq0,\quad
 [0345]\geq0,\quad [1256]\geq0.                 \tag{1}
\]

For the collapsed base, the signs additionally force

\[
 [0167]\geq0,\qquad [0467]\leq0,\qquad
 [0267]\geq0.                                  \tag{2}
\]

These implications are separate replayable UNSAT certificates. They
allow either global orientation and fix no zero limiting bracket.

Use the exact face-023 metric chart, with incidence coordinates
`(P_i,Z_i,c_i-2t*zeta_i)`, where `P=-U`, c is zero on A and one on B,
and anchors 0,2,3 have normal coordinate zero. The short edge 23 has a
positive limiting weight in both canonical families, so this moving
plane is well conditioned. Set `delta=Z6>0`. The limiting profile is

\[
 Z_7/\delta\to1,\qquad Z_1/\delta,Z_4/\delta,Z_5/\delta\to0. \tag{3}
\]

The necessary reference family is exactly (3) of
`remaining_flat_blowup.md`, evaluated at `z=1/2` or `u=1/2` respectively.
Its intrinsic and height uniqueness checks continue to hold at these
endpoints: their constant coefficient matrices have ranks fourteen
and five. The reference family satisfies all metric equations exactly
at every t. The previous metric Jacobian degenerates at the collapsed
edge; the following replacement removes that degeneracy.

## 2. A signed horizontal length defect

Write `beta>0` for the actual collapsed edge's horizontal intrinsic
weight. Define its signed horizontal length defect by

\[
 \mu=\begin{cases}
 h_{67}-(U_7-U_6),&\text{collapsed base 67},\\
 h_{36}+(U_6-U_3),&\text{collapsed leg 36}.
 \end{cases}                                    \tag{4}
\]

This is a definition made on the actual configuration. It imposes no
extra sign or magnitude restriction.

Retain the other twenty metric equations and replace just the
collapsed edge's squared metric equation by the linear equation (4).
Treat mu as an additional parameter. Every actual configuration
satisfies this modified system with its own value of mu. Sufficiency
of the modified system is unnecessary.

Choose the three free planar parameters to be the **actual** short
weights

\[
 r=h_{01}=-x_1,\qquad u=h_{23}=x_2-x_3,\qquad
 z=h_{72}=x_7-x_2+\tfrac12.
\]

They belong to `(0,1/2)` at every finite member of the sequence. The
twenty-one dependent planar variables are the remaining intrinsic
coordinates and the five U and five zeta coordinates.

At `t=mu=0` on the reference family, the two modified Jacobian
determinants are

\[
\begin{array}{ll}
 \text{leg 36, }u=\tfrac12:
 &16384r^2z(2r-1)^2(2z-1),\\
 \text{base 67, }z=\tfrac12:
 &8192r^2(2r-1)^2(2u-1).
\end{array}                                                   \tag{5}
\]

Both are nonzero in their stated parameter ranges. They are verified
by exact symbolic determinants. Thus all dependent planar variables
are analytic functions of t, r,u,z, mu, and the five normal coordinates
in a neighborhood of any proposed limiting configuration. Their
derivatives are uniformly bounded in that neighborhood.

## 3. A uniform expansion of the positive bracket combination

As before, put

\[
 N=4+t(4r-1)^2,\qquad D=4+t(32ru-8r-8u+1)>0,
\]

and take the weighted sum L of (1) with weights

\[
 ((1-2u)N/D,\ 2uN/D,\ N/D,\ 1).
\]

All weights are positive at each actual finite configuration, including
in the leg case because its parameter u is `h23<1/2`. Thus `L≥0`.
On the reference family its exact linear dependence on the normal
coordinates is

\[
 L_0=-4r(\tfrac12-r)u\,t\,\frac ND\,Z_6.       \tag{6}
\]

The modified metric equations remain even under simultaneous
`Z→-Z`. At `mu=0` the solved planar correction starts at degree two in
Z, with remainder `O(|Z|^4)`. Since determinants are linear in Z when
planar coordinates are fixed, L's correction starts at degree three,
with remainder `O(|Z|^5)`.

For general mu, the difference from the `mu=0` solution factors mu
exactly, by analytic differentiation. The resulting correction to L
is mu times a linear function of Z with coefficients continuous in
all parameters and Z. Using (3), the actual expansion is therefore

\[
 L=-c_n t\delta+\mu\delta(k+o(1))
                     +\delta^3(K+o(1)),         \tag{7}
\]

where

\[
 c_n=4r_n(\tfrac12-r_n)u_nN_n/D_n\longrightarrow c>0,
\]

and the exact coefficients are

| Family | Defect coefficient k | Cubic coefficient K |
|---|---:|---:|
| Leg 36 | `-r` | `-(1/2-r)/(2z)` |
| Base 67 | `r` | `-r/(1-2u)-(1/2-r)` |

The verifier obtains both columns by inverting the full modified
twenty-one-equation Jacobian: once with the unit defect forcing and
once with the quadratic normal forcing. At `t=0` and the unit profile
in (3), the Farkas functional is exactly `P5-P1=U1-U5`, which is also
checked symbolically.

The remainders in (7) are uniform as t, mu, and delta tend to zero
together. No division by these parameters enters the implicit-function
argument. In particular, the coefficient of `mu delta` is
`k+o(1)` even when mu is much larger than t or `delta²`; terms such as
`mu² delta` are included in that coefficient. The cubic remainder at
`mu=0` is controlled independently. It remains to use metric bounds on
the actual defect.

## 4. The collapsed leg cannot evade the negative terms

Every spatial component of an edge is bounded by its length. The exact
short-edge metric and the uniform gamma bound give

\[
 |\Delta U|\leq |E|
 =\beta\sqrt{1+t(\gamma_e/\beta)^2}
 \leq\beta(1+t)
\]

for the relevant small t. Consequently, in the leg case,

\[
 \mu=\beta+\Delta U\geq-t\beta,
 \qquad \beta\to0.                              \tag{8}
\]

Its defect coefficient tends to `-r<0`. When mu is nonnegative, its
term in (7) is nonpositive. When mu is negative, (8) bounds the
possible positive contribution by `O(t beta delta)=o(t delta)`.
The linear coefficient c is positive and the cubic coefficient K is
strictly negative. Thus (7) is strictly negative eventually, at every
relative rate. This contradicts `L≥0` and excludes all sixteen leg
cells.

## 5. The collapsed base has a negligible defect

For this case the sign implications (2) determine the edge's direction
at its own stretched scale. Normalize edge 67 by

\[
 m=\max(|\Delta X_{67}|,|\Delta Z_{67}|/\delta),
\]

where X is the affine transverse coordinate setting the longitudinal
anchor to zero. Its difference from `P=-U` on this short edge is
`O(t beta)`. The uniform relative bounds give `m≥c beta` and axial
increment divided by m tending to zero. A subsequence has a nonzero
normalized stretched direction `(v_x,v_y)`.

All three brackets in (2) factor the actual edge 67. Their leading
forms are respectively

\[
 -rv_y,\qquad -v_y/2,\qquad -v_x+v_y/2.
\]

Their required signs force `v_y=0`, `v_x<0`. The physical edge metric
then compares m with beta, exactly as in the adjacent-collapse proof,
and gives

\[
 (U_7-U_6)/\beta\to1,\qquad
 (Z_7-Z_6)/(\delta\beta)\to0.                   \tag{9}
\]

Every determinant implication here factors edge 67 before division.
The other rows only have to converge; their errors can be arbitrarily
larger than beta before that factor is removed.

The exact collapsed-edge equation, which remains true of the actual
configuration, can now be written

\[
 (\beta+\Delta U)\mu
  =(\Delta Z)^2+t\big((\Delta\zeta)^2-(\Delta\gamma)^2\big).
\]

The relative bounds `|Delta zeta|<7 beta` and
`|Delta gamma|<(1/2+t)beta`, together with (9), imply

\[
 |\mu|\leq O(t\beta)+o(\delta^2\beta)
           =o(t+\delta^2).                       \tag{10}
\]

The denominator `beta+Delta U` is bounded below by beta eventually,
by (9); this uses the positive actual beta, not any limiting lower
bound. The factor beta on the right of (10) tends to zero, however
small beta is relative to delta or t.

The defect term in (7) is consequently `o(t delta+delta³)`. Its two
remaining leading coefficients have strict negative signs. Again
`L<0`, contradicting `L≥0`. This excludes all sixteen base cells and
finishes the 32-cell theorem.

## Reproduction

```sh
python3 research/type7_completion/remaining_partner_blowup.py /tmp/type7-partner-blowup
g++ -O3 -std=c++17 research/orientation_checkpoint/check_unsat.cpp -o /tmp/type7-partner-checker
/tmp/type7-partner-checker < /tmp/type7-partner-blowup/partner_base67_required_signs.cnf
/tmp/type7-partner-checker < /tmp/type7-partner-blowup/partner_leg36_required_signs.cnf
/tmp/type7-partner-checker < /tmp/type7-partner-blowup/partner_blowup_model_coverage.cnf
```

Require explicit `UNSAT nodes ...` output. The JSON records all 32
canonical mappings and the exact regularized determinants and
coefficients. The intrinsic/height necessity ranks and exact reference
family are checked by the shared flat-family verifier, including their
endpoint parameter values.
