# Ray 3: the positive-weight one-flat/one-trapezoid blow-up

## Result and remaining scope

Suppose a canonical ray-3 sequence has `y→∞`, a common-line transverse
limit, and all eight limiting short-edge weights positive. A first
normal blow-up of this line cannot have exactly one collinear cap and
one noncollinear cap. The proof below is uniform in the ratio of the
normal width to `1/y` or `1/y²`.

This excludes all 24 positive-weight cells in the complete
degenerate-norm classification below. It does not exclude the 1,268
cells in which at least one edge weight vanishes, and supplies neither
a numerical height threshold nor a Lean theorem.

The finite checks and exact symbolic identities are in
`remaining_flat_blowup.py`. The necessary geometric premises are those
of `geometric_audit.md`, and the uniform cap estimates are those of
`relative_cap_bounds.md`.

## 1. The complete degenerate-norm cover

After blowing up the transverse coordinate normal to a common line,
the limiting physical edge weights are `h=|Delta X|`. Their values do
not include the blown-up normal coordinate. If one blown-up cap is
collinear, a shear in the normal coordinate makes its line horizontal
without changing these weights.

Reuse the 4,786 necessary weak-order cells from
`remaining_one_collinear.py`, but retain only the horizontal stress
`F0`; there is no Euclidean norm-excess term at this scale. The exact
bilinear gap coefficients have a strict fixed sign in 3,494 cells.
They all vanish in the remaining 1,292 cells. No cell has mixed-sign
coefficients.

The surviving A shapes consist of 1,148 triple clusters, 80 opposite
pair coincidences, and 64 adjacent pair coincidences. Exactly 24 cells
have all eight horizontal edge differences nonzero. The verifier maps
each by a checked marked symmetry and horizontal/normal reflections to

```
A: (0,0), (r,0), (1/2,0), (r,0),
B: (0,0), (u,0), (1/2,1), (z,1),
0<r,u,z<1/2.
```

The orders are cyclically `A=(0,1,4,5)` and `B=(2,3,6,7)`.
The three possible relative orders of u and z are all included.
Independent positive scaling of the normal coordinate has set B's
height to one; each original cap perimeter remains one.

The full necessary orientation and linking formula, with either global
orientation allowed, forces these four weak signs in this cell:

\[
 -[0124]\geq0,\qquad [0146]\geq0,\qquad
 [0345]\geq0,\qquad [1256]\geq0.                 \tag{1}
\]

Only nonzero limiting mixed brackets are fixed when deriving (1).
The actual four-brackets in (1) can vanish. The verifier exports an
UNSAT CNF asserting the fixed limiting signs and a violation of at least
one required sign, so this implication can be independently replayed.

## 2. An exact planar metric family

Use the quadratic face-023 chart from `remaining_null_chart.md`, with
`t=1/y²`. Its free spatial coordinates are `(U_i,Z_i,zeta_i)` for
`i=1,4,5,6,7`, while

```
U0=Z0=zeta0=0,
U2=x2, Z2=0, zeta2=gamma2,
U3=x3, Z3=0, zeta3=gamma3.
```

For an edge ij, put `ell=c_j-c_i`, with c zero on A and one on B.
The exact metric polynomial is

\[
 (\Delta U)^2+(\Delta Z)^2-X_{ij}^2
 -\ell\Delta\zeta-2k_{y,ij}\Delta\gamma
 +t\big((\Delta\zeta)^2-(\Delta\gamma)^2\big)=0. \tag{2}
\]

The three anchor equations are tautological; there are 21 other
equations. Incidence coordinates with the orientation used below are
`(P_i,Z_i,c_i-2t*zeta_i)`, where `P_i=-U_i`. The sign certificate allows
either orientation, so this horizontal reflection changes no premise.

Let `s=1/2-r`, `d=1/2-2r`, and `g2=r-1/8`. There is the following
exact planar solution of all 21 equations, for every t:

\[
\begin{aligned}
 P&=(0,r,0,u,\tfrac12,r,\tfrac12,z),\\
 x&=(0,-r,0,-u,0,r-\tfrac12,0,z-\tfrac12),\\
 \gamma&=(0,r/2,g2,g2+du,r-\tfrac14,r/2,g2+d/2,g2+dz),\\
 \zeta&=\gamma,\qquad Z=0.
\end{aligned}                                                   \tag{3}
\]

All equalities in (3) are verified symbolically against the archived
cocycle. The common-line metric limit is forced to be this family.
The sixteen exact cross-stress residuals are affine in all fourteen
intrinsic x/gamma unknowns. Together with the eight prescribed short
horizontal weights, their `24×14` coefficient matrix has rank 14.
Substitution verifies that (3) is its solution, proving uniqueness.
In particular `x2=0`, `gamma2=r-1/8` are necessary, not additional
choices. With these intrinsic values and the limiting horizontal
positions fixed, the fourteen non-anchor cross-edge equations have
rank five in the five free zeta variables. Their unique solution is
`zeta=gamma`. The verifier checks both ranks and both substitutions
exactly.

The family itself is a reference configuration. Several nearest-lift
inequalities are equalities there, and its vertices are coplanar.
No admissible embedding or strict nearest-lift witness is being claimed.

Because u is positive, face 023 gives a well-conditioned moving plane
for the normal blow-up. Its short edge 23 is a horizontal base of the
displayed trapezoid. In this face chart the canonical profile is

\[
 \delta=Z_6>0,\quad Z_7/\delta\to1,\quad
 Z_1/\delta,Z_4/\delta,Z_5/\delta\to0.             \tag{4}
\]

The other two free coordinates are identically zero on anchors 2 and 3.

## 3. Uniform metric control near the family

There are 24 planar variables: fourteen intrinsic x/gamma variables,
five U variables, and five zeta variables. Choose `x1,x3,x7` as the
three free parameters, equivalently `r=-x1`, `u=-x3`, `z=x7+1/2`.
For the other 21 variables the exact Jacobian determinant of (2) at
`t=0`, on (3), is

\[
 16384\,r^2z(2r-1)^2(2u-1)(2z-1)\ne0.           \tag{5}
\]

Thus near any fixed interior limiting triple `(r,u,z)`, the implicit
function theorem solves all planar variables analytically in t, these
three parameters, and the five normal coordinates. Its inverse and
Taylor coefficients are uniformly bounded in a neighborhood of that
limit. This statement uses no uniform lower bound across different
possible limiting triples; along each proposed sequence its positive
limits suffice.

Equation (2) depends on the normals only through squared differences.
Uniqueness therefore makes the solved planar coordinates even under
`Z→-Z`. Their correction from (3) starts at degree two in Z, with a
remainder `O(|Z|^4)`. In particular no term of order `|Z|²/t` occurs.

## 4. A positive bracket combination

Put

\[
 N=4+t(4r-1)^2,\qquad
 D=4+t(32ru-8r-8u+1).
\]

For `0<r,u<1/2`, `N≥4` and `D≥4-3t>0` when `t≤1/64`.
Use the positive weights

\[
 w=\big((1-2u)N/D,\ 2uN/D,\ N/D,\ 1\big)
\]

on the four expressions in (1), and denote their sum by `L`.
At the exact planar family, for **every** vector of normal coordinates,
direct determinant expansion gives

\[
 L_\mathrm{linear}
 =-4r(\tfrac12-r)u\,t\,\frac ND\,Z_6.            \tag{6}
\]

This is an identity at finite t, not merely its leading expansion.
In particular all dependence on `Z1,Z4,Z5,Z7` cancels. The verifier
checks its polynomial version after multiplying by D.

## 5. The cubic metric correction has the same strict sign

Substitute the analytic planar solution from Section 3 into L. Every
four-bracket is linear in the normal coordinates when the planar
coordinates are fixed. Therefore the first correction to (6) is cubic,
with a remainder `O(|Z|^5)` uniformly near the chosen interior limit.

At `t=0` and the unit profile `(Z1,Z4,Z5,Z6,Z7)=(0,0,0,1,1)`, the
first three weighted determinants vanish even after planar corrections.
The remaining determinant equals `P5-P1`. Solving the complete 21 by
21 linearized metric system with the quadratic normal forcing gives
its coefficient

\[
 K=-\frac{r}{1-2u}-\frac{1/2-r}{2z}<0.           \tag{7}
\]

The verifier inverts the exact symbolic Jacobian and checks (7).
An independent interpretation comes from the stress: the two sloping B
legs acquire positive norm excesses `delta²/[2(1/2-u)]` and
`delta²/(2z)`. The zero-stress condition forces `P1-P5` to have the
opposite of the coefficient in (7).

Using (4), continuity of the cubic form, and (6), the actual expression
along the sequence is consequently

\[
 L=-c_n t\delta+\delta^3(K+o(1)),\qquad
 c_n=4r_n(\tfrac12-r_n)u_nN_n/D_n\longrightarrow
      4r(\tfrac12-r)u>0.                         \tag{8}
\]

The `O(delta^5)` remainder has been absorbed in `o(delta^3)`.
Both displayed terms in (8) are negative eventually, whatever the
relative rates of t and delta. On the other hand, (1) and the positive
weights require `L≥0`. This contradiction proves the claimed exclusion.

## Reproduction

```sh
python3 research/type7_completion/remaining_flat_blowup.py /tmp/type7-flat-blowup
g++ -O3 -std=c++17 research/orientation_checkpoint/check_unsat.cpp -o /tmp/type7-flat-checker
/tmp/type7-flat-checker < /tmp/type7-flat-blowup/flat_blowup_required_signs.cnf
/tmp/type7-flat-checker < /tmp/type7-flat-blowup/flat_blowup_model_coverage.cnf
```

Require explicit `UNSAT nodes ...` output for both CNFs. The JSON output
records the complete 1,292-cell zero-cost cover and all 24 checked
canonical mappings. The remaining zero-weight cells require a separate
argument; the invertibility and positive coefficients above are used
only at interior parameter limits.
