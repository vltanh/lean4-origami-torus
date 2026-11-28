# Ray 3: two collapsed weights in the noncollinear cap

## Result and finite coverage

Consider a common-line ray-3 sequence whose first normal blow-up has
one collinear cap and one noncollinear cap. Such a sequence cannot
have all four weights of the collinear cap positive and exactly two
zero weights of its partner. There is no restriction on the relative
rates of the two collapsed lengths, normal width, and `t=1/y²`.

The exact degenerate-norm cover contains 24 cells of this kind. The
verified marked symmetries and coordinate reflections give two families:

| Family | Collinear cap `A=(0,1,4,5)` | Noncollinear cap `B=(2,3,6,7)` | Count |
|---|---|---|---:|
| Adjacent zeros 36 and 67 | `(0,0),(r,0),(1/2,0),(r,0)` | `(0,0),(1/2,0),(1/2,1),(1/2,1)` | 16 |
| Opposite zeros 36 and 72 | same A | `(0,0),(1/2,0),(1/2,1),(0,1)` | 8 |

In both rows `0<r<1/2`. The proof extends the exact signed-length-defect
argument in `remaining_partner_blowup.md`; all its coordinate and
orientation conventions are retained. In particular, the actual
positive free weights are `r=h01`, `u=h23`, `z=h72`, incidence coordinates
are `(P,Z,c-2t*zeta)` with `P=-U`, and

\[
 \delta=Z_6>0,\qquad Z_7/\delta\to1,\qquad
 Z_1/\delta,Z_4/\delta,Z_5/\delta\to0.                 \tag{1}
\]

The positive limiting weight of edge 23 makes this face gauge well
conditioned. The rank-fourteen intrinsic-stress and rank-five axial
necessity checks remain valid at both endpoints, so the actual planar
limit is the stated reference family.

## 1. Replace the two singular equations by their actual defects

For an oriented collapsed short edge e, write `beta_e>0` for its actual
intrinsic horizontal weight. Define

\[
 \mu_{36}=\beta_{36}+(U_6-U_3),\qquad
 \mu_{67}=\beta_{67}-(U_7-U_6),\qquad
 \mu_{72}=\beta_{72}-(U_2-U_7).                    \tag{2}
\]

Retain nineteen metric equations and replace the two collapsed-edge
equations by these two linear definitions. Each actual configuration
satisfies the resulting system with its own two values of mu. The
reference planar family satisfies the modified system at both zero
defects, for every t and nearby r,u,z.

At the limit `t=mu_1=mu_2=0`, the determinant of the full twenty-one
variable planar Jacobian is, in both cases,

\[
 8192r^2(2r-1)^2\ne0.                              \tag{3}
\]

This yields an analytic implicit solution jointly in t, the three free
weights, both defects, and the five normal coordinates. Its derivatives
are uniformly bounded near any proposed limiting configuration. No
division by a collapsed length, t, or delta occurs in this step.

## 2. The positive bracket combination

The required four weak signs are the same as in the single-collapse
proof:

\[
 -[0124]\geq0,\quad [0146]\geq0,\quad
 [0345]\geq0,\quad [1256]\geq0.
\]

Let L be their positive combination with weights
`((1-2u)N/D, 2uN/D, N/D, 1)`, where

\[
 N=4+t(4r-1)^2,\qquad D=4+t(32ru-8r-8u+1)>0.
\]

Here the actual `0<u<1/2` ensures positivity even though `u→1/2`.
Thus `L≥0`. Its exact reference-family linear term is

\[
 -c_n t\delta,\qquad
 c_n=4r_n(\tfrac12-r_n)u_nN_n/D_n\longrightarrow c>0.
\]

The multivariable implicit-function argument in the single-collapse
proof gives the uniform expansion

\[
 L=-c_n t\delta+
      \delta\sum_{e}\mu_e(k_e+o(1))+
      \delta^3(K+o(1)).                            \tag{4}
\]

To see uniformity with two defects, integrate the derivative of the
analytic solution along the straight segment from `(0,0)` to their
actual pair. The difference factors as the sum of each defect times a
continuous coefficient. Simultaneous normal reversal leaves every
modified equation invariant; at zero defects the planar correction is
quadratic with remainder `O(|Z|⁴)`. Since each bracket is linear in Z
for fixed planar variables, its remainder is `O(|Z|⁵)`. This proves
(4) for arbitrary joint rates, including defects much larger than
`t+delta²`.

The verifier computes the exact coefficients from the entire modified
Jacobian:

| Family | First defect coefficient | Second defect coefficient | Cubic K |
|---|---:|---:|---:|
| Adjacent 36,67 | `-r` | `r` | `r-1/2` |
| Opposite 36,72 | `-r` | `r-1/2` | `0` |

## 3. Adjacent collapsed edges

The same macro point signs as in the single collapsed-base case force
`[0167]≥0`, `[0467]≤0`, and `[0267]≥0`. Their factored leading forms
force the independently normalized stretched direction of edge 67 to
be horizontal and negative. The argument does not use strict separation
between the horizontal positions of vertices 3 and 6. Consequently,
exactly as in that proof,

\[
 |\mu_{67}|\leq O(t\beta_{67})+
                 o(\delta^2\beta_{67})
                 =o(t+\delta^2).                 \tag{5}
\]

For edge 36, the component length bound gives
`mu_36≥-t beta_36`. Its coefficient in (4) is strictly negative.
A positive defect only decreases L; a negative defect contributes at
most `O(t beta_36 delta)=o(t delta)`. The second defect contributes
`o(t delta+delta³)` by (5), and `K=r-1/2<0`. Hence `L<0` eventually,
a contradiction. This covers all sixteen adjacent cases.

## 4. Opposite collapsed edges

Both defect coefficients in (4) are strictly negative. Even though
its cubic coefficient is zero, the original collapsed-edge equations
give a stronger positive lower bound on the defects.

For either edge let q be the signed U displacement subtracted from
beta in (2). The exact short-edge metric and relative gamma bound imply
for sufficiently small t

\[
 q^2+(\Delta Z)^2\leq\beta^2(1+t).
\]

Concavity of the square root yields, without any sign assumption on q,

\[
 \mu=\beta-q
 \geq -t\beta+\frac{(\Delta Z)^2}{3\beta}.        \tag{6}
\]

Indeed, first bound q by the positive square root, then use
`sqrt(A-b)≤sqrt(A)-b/(2sqrt(A))` with `A=beta²(1+t)`.
For edge 36, `Delta Z=delta` exactly. For edge 72,
`Delta Z=-Z7` and `Z7/delta→1`.

Write the two coefficients in (4) as `-a_e`, where the positive a_e
are eventually bounded above and below independently of all small
parameters. Because `mu_e+t beta_e` is nonnegative by (6),

\[
 -a_e\mu_e\leq
 -a_*\frac{(\Delta Z_e)^2}{3\beta_e}+A_*t\beta_e
\]

for fixed `a_*,A_*>0`. Substitution into (4), using both `beta_e→0`,
therefore gives

\[
 L\leq -(c+o(1))t\delta
 -\frac{a_*}{3}\delta
       \left(\frac{\delta^2}{\beta_{36}}
                    +\frac{Z_7^2}{\beta_{72}}\right)
 +o(\delta^3)<0
\]

eventually. The middle term absorbs the cubic remainder since both
denominators tend to zero. This uses only their actual positivity and
imposes no comparison between either length and delta or t. It
contradicts `L≥0` and covers all eight opposite cases.

## Reproduction and scope

```sh
python3 research/type7_completion/remaining_double_partner_blowup.py /tmp/type7-double-partner
g++ -O3 -std=c++17 research/orientation_checkpoint/check_unsat.cpp -o /tmp/type7-double-checker
/tmp/type7-double-checker < /tmp/type7-double-partner/double_partner_adjacent36_67_required_signs.cnf
/tmp/type7-double-checker < /tmp/type7-double-partner/double_partner_opposite36_72_required_signs.cnf
/tmp/type7-double-checker < /tmp/type7-double-partner/double_partner_model_coverage.cnf
```

Require explicit `UNSAT nodes ...` output. The two sign certificates
are the same necessary sign implications already used in the two
single-collapse families; the verifier regenerates them independently.
The JSON records all 24 canonical mappings and both exact regularized
metric identities. This is an asymptotic research exclusion under the
existing geometric necessity audit, not a fixed-height or Lean theorem.
