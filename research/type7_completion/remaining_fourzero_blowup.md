# Four zero weights: two triple clusters

Among the 624 two-line zero-stress orders, exactly 80 have two vanishing
short-edge weights in each cap. Their four checked phase/reflection
orbits have the following representatives. Coordinates in this table
are ranks; the physical distance between ranks 0 and 1 is `1/2`.

| Orbit | A order, vertices `0145` | B order, vertices `2367` | Orders | Result here |
|---|---|---|---:|---|
| 0 | `(0,0,0,1)` | `(0,0,0,1)` | 16 | Excluded |
| 1 | `(0,0,0,1)` | `(0,0,1,0)` | 16 | Excluded |
| 2 | `(0,0,0,1)` | `(0,1,1,0)` | 32 | Open |
| 3 | `(0,0,0,1)` | `(1,0,1,1)` | 16 | Excluded |

The 48 excluded orders have a three-vertex cluster in **both** caps.
The remaining 32 have a triple cluster and two pairs. No order with
two pairs in both caps survives the prior macro orientation/stress
calculation.

`remaining_fourzero_blowup.py` checks the order cover, all metric
identities, all height-sign implications, and the necessary Boolean
formulas described below. This is an exclusion of these limits of
unbounded sequences. It does not supply an explicit height threshold
or complete a whole marking at the target height.

## 1. Four separately normalized directions

Use transverse bases `E` and `F` along the two distinct stretched lines.
Choose their signs so that both have physical horizontal increment
`1/2`. The cap levels are 0 and 1. In cap A write the consecutive small
edge vectors as `a=01`, `b=14`. The two small B edge vectors are:

| Orbit | `c` | `d` |
|---|---|---|
| 0 | `23` | `36` |
| 1 | `23` | `72` |
| 2 | `36` | `72` |
| 3 | `67` | `72` |

Each actual edge is normalized by its own positive stretched length.
Its axial increment divided by that length tends to zero: the relative
axial bound controls it by `O(t)` times its physical length, and the
stretched length dominates the physical transverse length. Here
\(t=y^{-2}\to0\).

A triple cluster has three possible relative-scale cases: the first
edge dominates, the two are comparable, or the second dominates.
If they are comparable, absorb their positive limiting ratio into the
two direction vectors and retain their sum. If one dominates, the
cluster's nonedge direction has that dominant leading vector. The
individual subdominant edge direction is still retained separately.
A zero sum is permitted.

For every four-bracket, the checker divides by every actual small-edge
factor that its vertices contain. For a collapsed nonedge pair, it
uses the containing cluster's scale and the selected hierarchy. These
are exact multilinear factorizations. The remaining limiting
determinant is either a constant, a direction component, a determinant
of two retained directions, or zero. A zero limiting determinant adds
no sign constraint.

The necessary CNF includes nonzero individual directions, exact sign
consequences of vector addition, and all rank-two three-term
Grassmann--Pluecker sign identities for the two bases, four edge
directions, and applicable cluster sums. Every bracket expression is
checked to be one of those already constrained expressions.

For the three orbits with two triple clusters there are 27 hierarchy
branches. Nine are already contradictory at this stage. The other
18 require the relative metric height calculation below. The complete
embedding/orientation/linking formula remains present, with both
global orientations allowed.

## 2. Exact corner data and relative stress identities

Let `Rij` be the exact cross-ring stress, with ring edges indexed in
`A=(0,1,4,5)` and `B=(2,3,6,7)`. For every selected binary B order the
checker solves the corner equations

\[
R_{ij}=h_{A,i}h_{B,j}-e_{A,i}e_{B,j},\qquad X_{A,i}=-h_{A,i},\quad
X_{B,j}=-h_{B,j}.
\]

Here `e` is the original physical horizontal step and `h=|e|`.
These 24 affine equations have rank 14 and uniquely determine the
seven intrinsic horizontal and seven intrinsic axial corner values.
All calculations use exact rational arithmetic.

For the small edge `01`, put \(\alpha=h_{01}>0\) and
\(c_0=-x_2+1/4+2\gamma_2\). The following identities are checked before
taking limits:

\[
c_0=2(R_{02}+R_{03}),\qquad
\gamma_{01}=\alpha/2-R_{01}.
\tag{1}
\]

If the normalized virtual direction has nonzero physical horizontal
projection, let \(\sigma\in\{-1,1\}\) be the limiting physical unit
direction. Divide the actual edge by \(\alpha\) before taking limits.
The relative axial bounds and the original transverse collapse give

\[
R_{0j}/\alpha\longrightarrow h_{B,j}-\sigma e_{B,j}.
\tag{2}
\]

This remains valid when one or both B short-edge weights vanish.
No comparison between their rates and \(\alpha\) is required.

For actual squared spatial distances, define

\[
\rho_1=D_{01}-D_{12}+D_{02},\qquad
\rho_A=D_{05}-D_{25}+D_{02}.
\]

Their exact intrinsic formulas are

\[
\begin{aligned}
\rho_1&=-c_0+(1-2x_2)\alpha+\gamma_{01}
                         +2t\gamma_2\gamma_{01},\\
\rho_A&=x_5+1/4+2x_5x_2+\gamma_5-2\gamma_2
                         +2t\gamma_5\gamma_2.
\end{aligned}
\tag{3}
\]

Equations (1)--(3) determine the finite limit
\(r_O(\sigma)=\lim\rho_1/\alpha\) for each binary B corner `O`.

Choose B vertices `j0,j1` at physical ranks 0 and 1. Put
\(\rho_B=2(P_{j1}-P_{j0})\cdot P_2\), where vertex 0 is the origin.
Its corner value is obtained exactly as

\[
\rho_B=\lim(D_{0j1}-D_{0j0})
 -\bigl((1/2-P_2)^2-P_2^2\bigr).
\tag{4}
\]

The first difference has no common `y²/4` term. The second term is the
limiting difference of the two within-cap squared distances. Formula
(4) does not require the pairs `2,j0` and `2,j1` to be graph edges:
their limiting physical distances are known from the displayed macro
geometry.

## 3. The relative height of an individual small edge

Use the moving affine frame with transverse basis
\(P_5\), \(P_{j1}-P_{j0}\), and long vector \(P_2\). Let the components
of edge `01`, divided by its actual physical weight \(\alpha\), tend
to \((a_x,a_y)\) in the two transverse bases. Since both bases have
physical horizontal step `1/2`,

\[
a_x+a_y=2\sigma.
\tag{5}
\]

Taking the dot product of the frame decomposition with \(P_2\) gives
the exact axial coefficient. Since \(1/(2|02|^2t)\to2\), its limit is

\[
K_O(a_x,a_y)
 =\lim\frac{a_z}{t\alpha}
 =2\bigl(r_O(\sigma)-a_x\rho_A-a_y\rho_B\bigr).
\tag{6}
\]

The checker uses this implication only when the two component signs
agree weakly and at least one is nonzero. Such a direction has nonzero
physical projection, so the rescaling by physical weight is justified.
In particular, same-sign components give the exact open ranges
\(a_y\in(0,2)\) or \((-2,0)\); an axis direction gives the singleton
`0`, `2`, or `-2`.

Define the height for a pure A-line direction by

\[
C_O(\sigma)=2\bigl(r_O(\sigma)-2\sigma\rho_A\bigr).
\]

Then (5)--(6) give

\[
K_O=C_O(\sigma)+2(\rho_A-\rho_B)a_y.
\tag{7}
\]

For example, in orbit 0 the exact corner values are
\(\rho_A=1/4\), \(\rho_B=-1/4\),
\(C_O(1)=-2\), and \(C_O(-1)=0\).

The marked reflection

\[
p=(4,1,6,3,0,5,2,7)
\]

sends the second small A edge to the reverse of edge `01` and fixes
the far A vertex. It changes the B order to
\(O'=(O_2,O_1,O_0,O_3)\). Applying the same exact calculation yields
the small height for `14`. The checker verifies, for every corner
used in a certificate,

\[
\rho_A-\rho_B=\rho'_A-\rho'_B.
\tag{8}
\]

These calculations can use different vertices within the same macro
cluster as anchors. Their transverse differences are `o(δ)` and their
axial corrections divided by `t` tend to zero by the relative edge
bounds. Thus the limiting height functional divided by `t` is the
same. Moving the long anchor to the other B cluster changes it by the
B-line basis vector and does not change that functional. This ensures
that the two edge-height limits are compared in one moving frame,
even when the two small edges collapse at very different rates.

## 4. A linear sign certificate for the cap volume

Put \(\beta=h_{14}>0\), and write the physical-weight-normalized
transverse components of the second edge as \((b_x,b_y)\), with
\(b_x+b_y=2\sigma_b\). In the moving frame the far A vertex is
`(1,0,0)`, so

\[
[0145]=a_y^{\rm actual}b_z^{\rm actual}
       -a_z^{\rm actual}b_y^{\rm actual}.
\]

Equations (7)--(8) cancel the quadratic terms and give

\[
\boxed{\quad
\lim\frac{[0145]}{t\alpha\beta}
 =-C_{O'}(-\sigma_b)a_y-C_O(\sigma_a)b_y.
\quad}
\tag{9}
\]

This is a linear expression in two components with exact rational
coefficients. The checker evaluates its endpoints on the ranges forced
by a direction-sign pattern. If all endpoint values are nonnegative
and at least one is positive, the expression is strictly positive:
every non-singleton range has an open interior, and a nonzero affine
function cannot vanish at an interior point while being nonnegative
on the whole box. The negative case is analogous. Cases without a
proved strict sign add no implication.

Each accepted implication has the form “this complete direction-sign
pattern forces this sign of the A-cap bracket.” Marked phase maps can
apply the same statement to the B cap. Swapping the two caps swaps the
two transverse bases and reverses the level axis, so these two
orientation reversals cancel. A common horizontal reflection reverses
both transverse bases and also preserves orientation. The checker
therefore applies the explicitly computed vertex-order parity to the
conclusion.

In orbit 0, for instance, the remaining direction formula forces
`a=+E`, `b=+F`, and a negative A-cap bracket, after the checked
triplet reflection if needed. Equation (9) instead gives the positive
limit `4`. The other two excluded orbits use the same calculation,
sometimes after exchanging the caps.

## 5. What the computer checks

For each of the 27 hierarchy branches, SAT suggests component-sign
patterns. Every height implication added for one of those patterns is
then reconstructed using only exact stress identities, exact rank-14
corner data, checked symmetries, and the linear interval check in (9).
The final CNF is independently checked as `UNSAT`.

Completeness of the pattern producer is unnecessary: omitting a pattern
would only omit a valid implication and weaken the final CNF. No SAT
model, numerical tolerance, or nonlinear solver result is used as a
metric proof. The independent Boolean replay proves all branches after
these individually valid implications have been added.

The exported model-coverage CNF is exactly the same clause multiset as
the independently RUP-checked 1,888-model chamber coverage formula.
The order ledger records every map for the 80 orders and distinguishes
the 48 excluded orders from the 32 open triple/split orders.

```sh
python3 research/type7_completion/remaining_fourzero_blowup.py /tmp/type7-fourzero
g++ -O3 -std=c++17 research/orientation_checkpoint/check_unsat.cpp -o /tmp/type7-sign-check
```

Replay all 27 files named `fourzero_[013]_*.cnf` with the independent
checker, requiring explicit `UNSAT nodes ...` output for each one.
`fourzero_height_certificates.json` records the sign pattern, marked
map, exact coefficients, component ranges, and resulting cap sign of
every height implication.
