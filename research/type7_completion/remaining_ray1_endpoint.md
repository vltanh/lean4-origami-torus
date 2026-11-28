# The marking-1 mask-04 endpoint: uniform relative data

The preceding first-stretch theorem leaves four equivalent endpoints.
Use the canonical one

\[
h:=h_1\longrightarrow0,\qquad h_i\longrightarrow\tfrac12\quad(i\ne1).
\]

Set `d_i=1/2-h_i` for `i!=1`. At every finite point of the sequence,

\[
h=\sum_{i\ne1}d_i,\qquad 0<d_i<h.
\tag{1}
\]

In the bounded axis-01 coordinates, rotate the transverse plane so that
`P3` is on the positive horizontal axis. Write `P_i=(P_ix,Z_i)` and
let `delta=max |Z_i|` be the first transverse width. The limiting points
are

\[
P=(0,0,0,\tfrac12,0,\tfrac12,0,\tfrac12),
\]

along this axis. The upper cluster is `{1,2,4}`, the upper tip is `3`,
and the lower coincident pairs are `{0,6}` and `{5,7}`.

This note supplies exact metric necessities and the Boolean source
binding for the virtual-direction certificates in
`solver_remaining_virtual12.md`. Together they reduce the normalized
horizontal deficit to three boundary regimes. They do not yet exclude
those regimes.

## 1. Complete generic source and unique height constants

The canonical weak-slope formula in
`remaining_ray1_mask04_blowup.py` has exactly 331 primary generic sign
projections. `endpoint_primary_models()` enumerates them afresh and
returns their sorted 70-sign strings. A separate blocking-clause CNF
checks completeness. Six additional direct UNSAT obligations show

\[
Z_2/\delta\longrightarrow0,\qquad Z_4/\delta\longrightarrow0.
\tag{2}
\]

The height and product variables of the bounded axis compactification
remain uniformly bounded. The `14` and `05` equations give `q14,q05->0`
at this corner; the previous middle-step rate argument already gives
`q24,q57->0`. Substituting the corner values into **all 24** compact
metric equations leaves a linear system of rank ten. Its unique
solution is

\[
(H_1,\ldots,H_7)=
(\tfrac14,\tfrac14,-\tfrac14,-\tfrac14,-\tfrac14,-\tfrac18,\tfrac12),
\quad w=-\tfrac18,\quad q_{25}=-\tfrac12,\quad q_{47}=\tfrac34.
\tag{3}
\]

The exact product identities consequently give

\[
b_2/t\longrightarrow\tfrac14,\qquad
b_6/t\longrightarrow-\tfrac14.
\tag{4}
\]

The matrix rank and substitutions are checked symbolically. These are
necessary limits of an actual sequence, rather than a selected metric
witness.

## 2. Exact anchor formulas have no independent small-t error

Put

\[
\begin{gathered}
h_0=\tfrac12-d_0,\quad h_2=\tfrac12-d_2,\quad
v_2=v_1+b_1,\quad v_3=v_1+b_1+b_2,\\
x_1=-h_0,\quad x_2=1-h_0-h,\quad x_3=x_2-h_2,\\
\ell^2=v_1^2+t h_0^2,\qquad D=h_0v_3+v_1x_3.
\end{gathered}
\]

Here `ell->1/2` and `D->1/4`. The actual face `013` gives
`P3x=D/ell>0`. Exact common-axis polarization gives

\[
P_{2x}=\frac{N}{\ell D},\qquad
N=D(v_1x_2+h_0v_2)-(\tfrac12-h)(v_1v_3-t h_0x_3).
\tag{5}
\]

Write

\[
c=h_0h+\tfrac12-h_0-h=d_0-(\tfrac12+d_0)h,
\]

and

\[
G=v_1^2h^2+h_0^2b_1^2-2v_1b_1c
    +t(h_0^2h^2-c^2).
\]

The same polarization gives

\[
|P_2|^2=G/\ell^2,\qquad
Z_2^2=\frac{GD^2-N^2}{\ell^2D^2}.
\tag{6}
\]

The producer verifies the exact polynomial ideal memberships

\[
N-b_1D/2\in(h,d_0,d_2),\qquad
GD^2-N^2\in(h,d_0,d_2)^2+b_1(h,d_0,d_2).
\tag{7}
\]

Their coefficients are uniformly bounded near the endpoint, with no
assumption on the relative rates of `b2,t,h`. By (1),

\[
P_{2x}=b_1/(2\ell)+O(h),\qquad
Z_2^2=O\bigl(h(h+|b_1|)\bigr).
\tag{8}
\]

There is also an exact relative axial formula:

\[
H_1=\frac{h_0^2}{\ell+v_1},\qquad
H_2-H_1=\frac{c-b_1H_1}{\ell}.
\tag{9}
\]

In particular, `H2-H1=O(h+|b1|)` uniformly.

## 3. A four-edge polarization forces b1=O(h1)

Let `Eij` denote the full compact metric residual of edge `ij`.
Symbolic expansion gives exactly

\[
\frac{E_{02}-E_{01}-E_{27}+E_{17}}2
 =P_2\cdot P_7+b_1H_7+(v_7+tH_7)(H_2-H_1)+h h_7-d_0.
\]

Thus every actual sequence satisfies

\[
P_2\cdot P_7+b_1H_7+(v_7+tH_7)(H_2-H_1)=d_0-hh_7.
\tag{10}
\]

By (3), `P7x,H7->1/2`, while `Z7,v7,t->0`. Equations (8)–(9) put
(10) in the form

\[
(1+o(1))b_1+Z_2Z_7=O(h)+o(|b_1|).
\]

The remaining normal product obeys

\[
|Z_2Z_7|\le C|Z_7|\sqrt{h(h+|b_1|)}
 =o(h+|b_1|).
\]

Absorbing the small multiples of `|b1|` proves

\[
b_1=O(h).
\tag{11}
\]

This estimate excludes either sign of an uncontrolled `b1/h1` ratio.
It does not require a comparison with `delta` or `t`.

The factor identities also give the first jet

\[
P_{2x}=b_1-h+2d_2+o(h+|b_1|).
\]

Now (11), (10), and `Z2*Z7=o(h)` refine this to

\[
b_1=d_0-d_2+o(h),\qquad
P_{2x}=d_0+d_2-h+o(h).
\tag{12}
\]

The exact quadratic jet of (6) is

\[
Z_2^2=4\{b_1(h-d_0-d_2)+d_2(h-d_2)\}+o(h^2).
\]

Using (12) gives

\[
Z_2^2=4d_0(h-d_0)+o(h^2).
\tag{13}
\]

The absence of an independent pure-`t` remainder in this step is
precisely what (7) certifies.

## 4. The exact virtual certificates leave three deficit regimes

Take a subsequence with

\[
\alpha=d_0/h\longrightarrow\alpha_*,\qquad
\beta=d_2/h\longrightarrow\beta_*,\qquad
0\le\alpha_*,\beta_*,\quad\alpha_*+\beta_*\le1.
\]

In the first-stretched incidence coordinates, the displacement of
vertex 2 from vertex 1 has horizontal component `P2x`, normal component
`Z2/delta`, and axial component `2[b1+t(H2-H1)]`. If its normal
component were unbounded relative to `h`, a further normalized limit
would be a pure normal direction `(0,+1,0)` or `(0,-1,0)`.
`solver_remaining_virtual12.py` excludes both directions over the
complete 331-model/profile cover. Therefore

\[
Z_2=O(\delta h)=o(h).
\]

Equation (13) forces `alpha_*` to be zero or one. If `alpha_*=1`, then
`beta_*=0`, and the virtual horizontal/axial pair is `(0,2)`. If
`alpha_*=0`, write `r=beta_*`. Equation (12) gives the pair

\[
(a_X,a_Z)=(r-1,-2r),\qquad0\le r\le1,
\]

with a bounded, otherwise unrestricted virtual normal component.
The same certificate package excludes every `0<r<1` by exact
parameter-polynomial Farkas identities. Its replay covers the whole
parameter interval; no sampling assertion is used.

The remaining normalized deficit regimes are consequently

| Regime | Deficit ratios | Compatible primary signs in the virtual relaxation |
|---|---|---:|
| Positive axial direction | `d0/h -> 1` | 172 |
| Negative axial direction | `d2/h -> 1` | 38 |
| Negative horizontal direction | `d0/h,d2/h -> 0` | 15 |

In the third row, the other five deficits sum to `h+o(h)`. The surviving
sign counts describe necessary Boolean/linear relaxations and do not
assert geometric realizations. Excluding these three regimes remains
open in this package.

## 5. An exact all-t reference for further endpoint estimates

The following formal boundary has `h1=0` and all other horizontal
weights equal to `1/2`. It is useful for eliminating spurious pure-`t`
errors in later estimates. Put

\[
A=1+2u+t/4,\quad v_1=v_2=v_4=u+\tfrac12-t/8,\quad
v_3=A/2-ut/A,\quad v_5=v_7=u-t/4,\quad v_6=u.
\]

The intrinsic horizontal coordinates are
`(0,-1/2,1/2,0,-1/2,1/2,0,1/2)`. In a spatial planar gauge, take

\[
U=(0,\tfrac12,\tfrac12,2v_1/A,\tfrac12,\tfrac12,0,\tfrac12),
\]

and normalized axial coordinates `Z_i=v_i`, except
`Z3=v3-t/A`. All normals vanish. Every one of the 24 original metric
equations holds identically for all sufficiently small `t,u`.
Several intrinsic faces are degenerate, so this is a metric reference,
not a torus realization.

The exact map back to the bounded axis-01 gauge is

\[
\ell=\sqrt{v_1^2+t/4},\qquad
P_{ix}=\frac{v_1U_i-Z_i/2}{\ell},\qquad
\zeta_i=\frac{tU_i/2+v_1Z_i}{\ell}.
\tag{14}
\]

Here the physical axial coordinate is `y*zeta_i`; normal coordinates
are unchanged. The producer verifies preservation of the physical
metric, `P1x=0`, and `zeta1=ell`. At the endpoint `P3x->1/2>0`, so the
reference already uses the required positive face-013 transverse
direction. The compact heights are recovered as
`H_i=(zeta_i-z_i)/t`, with the same folded baselines `z_i` as in
`exhaustive_remaining_axis.py`.

A checked one-parameter extension replaces

\[
\begin{aligned}
v_3&=A/2-utp/A,&U_3&=2v_1p/A,&Z_3&=v_3-tp/A,\\
v_5&=u-t/4+\frac{tA(1-p)}{2(A-tp)},& W_3^2&=p(1-p),
\end{aligned}
\]

and leaves every other normal zero. It satisfies 22 metric rows
identically. The two remaining rows, `25` and `45`, both have the
scaled residual

\[
-\frac{tA(1-p)}{A-tp}.
\]

This records a useful signed normal term. No claim that the chosen
22-row extension parametrizes all nearby solutions is made.
For this extension, apply (14) first, then rotate the transverse plane
to send its nonzero vector `P3=(P3x,W3)` to the positive horizontal
axis. Explicitly, with `L=sqrt(P3x^2+W3^2)`, the new transverse
coordinates are `(P3x*P_ix+W3*W_i)/L` and
`(-W3*P_ix+P3x*W_i)/L`. This rotation has positive determinant and
`L->1/2`, so it introduces no vanishing denominator.

## Replay

```sh
python research/type7_completion/remaining_ray1_endpoint.py OUTPUT
python research/type7_completion/solver_remaining_virtual12.py OUTPUT2
```

The endpoint producer checks the rank-ten necessity system, projection
identities, polynomial factor ideals, exact stress polarization,
homogeneous jets, and the all-`t` reference. It writes the seven Boolean
UNSAT obligations and the complete sorted 331-model source. The
virtual-direction package independently rebuilds and replays its exact
fixed and parameter-polynomial Farkas certificates against those sign
strings.
