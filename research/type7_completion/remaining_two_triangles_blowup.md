# The last two-noncollinear-cap common-line blow-up

## Result

There is no unbounded ray-3 sequence whose common-line transverse limit
has a bounded first normal blow-up with **both caps noncollinear**.
The proof covers all 16 zero-cone supports from
`common_line_trapezoids.md`, including arbitrary ratios between the
collapsing short weights, the normal width, and `t=1/y²`.

The finite cover reduces those supports to one triangle pair. A single
necessary bracket sign then contradicts a first-order metric identity,
after normalizing by the largest of the four vanishing short weights.
An exact reference solution for every small `t` removes a possible
independent `O(t)` error.

This is an asymptotic research exclusion. It supplies no explicit height
threshold and is not by itself a fixed-height or Lean marking exclusion.

## 1. The complete triangle cover

The exact zero-cone calculation leaves four zero-weight patterns. The
indices here are cyclic edge indices in `A=(0,1,4,5)` and
`B=(2,3,6,7)`.

| Orientation | Zero A indices | Zero B indices |
|---|---|---|
| `+1` | `0,3` | `0,1` |
| `+1` | `1,2` | `2,3` |
| `−1` | `0,1` | `1,2` |
| `−1` | `2,3` | `0,3` |

There is exactly one positive base in each cap, and the separation gap
is zero. The physical horizontal perimeter is one, so each positive
base has length `1/2`. Undoing the temporary separate cap scalings used
in the cone proof leaves two nonzero normal heights. Normalize the A
height to one and denote their positive ratio by `λ`.

Checked marked phase permutations, a common horizontal reflection,
and a nonzero normal scaling take each entire pattern to

\[
\begin{aligned}
A&=((0,0),(0,-1),(1/2,-1),(0,0)),\\
B&=((0,0),(0,-\lambda),(0,-\lambda),(1/2,0)),
\qquad 0<\lambda<\infty.
\end{aligned}
\tag{1}
\]

Origins are chosen separately within the caps by a shear along the long
axis. The checker verifies these coordinate identities symbolically,
for the whole parameter interval; the transformed ratio is only `λ`
or `1/λ`. It also reruns the antecedent cover of 32 cones, 116 extreme
rays, 652 nonnegative ray products, and all 16 cross-cap zero supports.

The parameter is finite and positive because both caps are noncollinear
in this bounded blow-up. A zero or infinite height ratio belongs to a
limit with one collinear cap, covered separately.

## 2. The finite direction and bracket implication

In (1), the stretched edges 50 and 36 vanish. Retain each at its own
positive scale. The full necessary orientation/linking formula forces

\[
50\parallel-E,\qquad36\parallel+E,\qquad[1256]\geq0,
\tag{2}
\]

where `E` is the positive horizontal direction. The bracket inequality
is weak because the actual determinant may vanish even when its generic
completion has positive sign.

For the symbolic direction formula use formal points

\[
P_5=(-\epsilon a_x,-\epsilon a_y,0),\qquad
P_6=(\eta b_x,-\lambda+\eta b_y,1),
\]

and the other six points from (1) at their cap levels. Divide each
bracket containing 05 by `ε`, and each containing 36 by `η`; if both
pairs occur, divide by their product. Thus an arbitrarily small edge
keeps its own direction. No relative edge scale is imposed.

Every resulting nonzero expression is a signed determinant of retained
vectors or has a coefficient whose sign is checked for all `λ>0`.
The exact sign test checks the numerator and denominator polynomial
coefficients, not sampled parameter values. Rank-two determinant sign
relations and nonzero individual directions complete the necessary
formula. Zero leading determinants impose no sign constraint.

One exported CNF adds the negation of the combined conclusion (2) and
is independently checked `UNSAT`. As a supplementary check, there are
exactly four generic completions, differing only in the two cap signs:
all 68 other bracket signs are fixed. No previously excluded metric
chamber is needed for this proof.

Apply the checked phase relabeling

\[
p=(1,4,7,2,5,0,3,6).
\tag{3}
\]

It sends the bracket `[0347]` to `[1256]` with positive vertex parity.
It also gives physical horizontal corner coordinates

\[
(0,1/2,0,-1/2,0,0,-1/2,-1/2)
\]

and normal profile

\[
Z_4,Z_5\sim\delta,\qquad Z_6,Z_7\sim-\lambda\delta,
\qquad Z_1=o(\delta),
\tag{4}
\]

with `Z0=Z2=Z3=0` in the face-023 gauge. Set `δ=Z5>0`.
In these labels (2) forces the two missing bases 45 and 67 to have
negative and positive horizontal directions, respectively, and

\[
[0347]\geq0.
\tag{5}
\]

## 3. Four defects and an exact reference for all t

Use spatial coordinates

\[
r_i=(U_i,-y c_i/2+H_i/y,Z_i),\qquad t=y^{-2},
\]

with the actual face-023 isometry setting
`(U2,H2,Z2)=(x2,γ2,0)` and `(U3,H3,Z3)=(x3,γ3,0)`.
The four vanishing positive short weights are

\[
a=h_{45},\quad b=h_{50},\quad c=h_{67},\quad d=h_{36}.
\tag{6}
\]

Choose `a,b,c` as free parameters and keep `d` dependent. Replace those
four metric rows by the signed horizontal defects

\[
\begin{aligned}
\mu_a&=a+U_5-U_4,&
\mu_b&=b+U_5,\\
\mu_d&=d+U_6-U_3,&
\mu_c&=c-U_7+U_6.
\end{aligned}
\tag{7}
\]

The resulting 21 equations have 21 dependent intrinsic/extrinsic
variables. Their Jacobian determinant at the zero-weight corner is
exactly `2048`.

The corner is independently necessary: the affine cross-stress and
short-ring equations have constant rank 14 and force

\[
\begin{aligned}
x&=(0,-1/2,0,-1/2,-1/2,-1/2,0,0),\\
\gamma&=(0,1/4,-1/8,1/8,0,0,1/8,1/8).
\end{aligned}
\tag{8}
\]

The cross-distance equations have rank 5 and force the five free height
values `H1=−3/4`, `H4=H5=0`, `H6=H7=1/8` at `t=0`.

The constant corner itself has nonzero metric residuals when `t>0`.
Keeping (8) and the other spatial coordinates fixed, replace only

\[
U_1^0(t)=\frac{4-3t}{8+2t},\qquad
H_1^0(t)=\frac{t-12}{16+4t}.
\tag{9}
\]

This is an **exact planar solution of every metric equation** for all
small `t`. All four weights and all four defects are zero there.
The checker verifies (9) by rational identities, without discarding
any term in `t`.

## 4. Normalize by the largest small weight

Put

\[
M=\max\{a,b,c,d\}>0.
\tag{10}
\]

All four weights tend to zero. The established relative intrinsic axial
bounds imply that a short edge of weight `h` has physical length at
most `(1+Ct)h`. Therefore every defect in (7) is `O(M)`.
Also `Z5=δ` is a component of edge 05, while
`Z6=−λδ+o(δ)` is a component of edge 36. Thus

\[
\delta=O(b),\qquad\delta=O(d),\qquad
\|Z\|^2=O(\delta^2)=o(M).
\tag{11}
\]

The missing-base directions in (5), together with the relative axial
bounds, give

\[
\mu_a=o(a),\qquad\mu_c=o(c).
\tag{12}
\]

Indeed each normalized missing base has a nonzero horizontal component
and zero stretched normal component. Its physical normal increment
is `o(δh)`, and its axial increment is `O(h/y)`. Its horizontal
increment divided by `h` consequently tends to the forced sign.

Consider the functional

\[
F=b+d-U_5-(U_6-U_3).
\tag{13}
\]

It is identically zero on the exact reference (9). Differentiating the
regular system shows that its **seven total first derivatives** with
respect to `a,b,c,μa,μb,μd,μc` all vanish at the corner. These are
computed from the exact inverse Jacobian, not supplied as certificate
coefficients. Normal coordinates enter the metric system quadratically.

The uniform implicit function theorem around (9) now yields

\[
F=o(M).
\tag{14}
\]

More explicitly, if `θ` denotes the seven small free/defect parameters,
then `|θ|=O(M)`. The derivative of the composed functional with respect
to `θ` at the reference tends to zero as `t→0`, and its second
derivatives stay bounded. Consequently

\[
|F|\leq\varepsilon(t)|\theta|
       +C|\theta|^2+C\|Z\|^2=o(M),\qquad\varepsilon(t)\to0.
\]

The exact reference is essential: it eliminates a free term depending
only on `t`, which need not be small compared with `M`.

Define the two vertical-leg length deficits

\[
\nu_b=b-U_5,\qquad\nu_d=d-(U_6-U_3).
\]

The individual metric norm bounds give
`νb≥−Ct b` and `νd≥−Ct d`. Their sum is `F=o(M)`, so each is
`o(M)` separately. Equations (7), (12), and (14) therefore imply

\[
\begin{aligned}
U_5&=b+o(M),& U_6-U_3&=d+o(M),\\
U_4&=a+b+o(M),& U_7-U_3&=c+d+o(M).
\end{aligned}
\tag{15}
\]

No comparison between `t`, `δ`, or the individual short weights was
used.

## 5. The necessary bracket has the opposite sign

Use incidence coordinates `(U,Z,c−2tH)`, which differ from the physical
coordinates by a fixed positive determinant factor. The exact bracket
in (5) factors along the two actual short paths 04 and 37:

\[
\begin{aligned}
[0347]={}&(1-2t\gamma_3)
 \bigl(U_4Z_7-Z_4(U_7-x_3)\bigr)\\
&+2t x_3\bigl(H_4Z_7-Z_4(H_7-\gamma_3)\bigr).
\end{aligned}
\tag{16}
\]

The checker expands both sides and verifies equality. The relative
axial bounds on paths `05+54` and `36+67` give

\[
H_4=O(a+b),\qquad H_7-\gamma_3=O(c+d).
\]

Likewise their horizontal increments are `O(M)`. Divide (16) by the
positive quantity `(1−2tγ3)δ`. The normal-profile errors in (4)
multiply these small increments, so their contribution is `o(M)`;
the axial contribution is `O(tM)`. Using (5) gives

\[
\lambda U_4+(U_7-x_3)\leq o(M).
\]

Since `U3=x3`, substitute (15):

\[
\boxed{\lambda(a+b)+c+d\leq o(M).}
\tag{17}
\]

But the left side is at least `min(λ,1)M`, with `λ` finite and
strictly positive. This contradicts (17) and excludes the entire
triangle family.

## Reproduction

```sh
python3 research/type7_completion/remaining_two_triangles_blowup.py /tmp/type7-two-triangles
g++ -O3 -std=c++17 research/orientation_checkpoint/check_unsat.cpp -o /tmp/type7-sign-check
```

Independently replay both exported CNFs and require explicit
`UNSAT nodes ...` output. The implication CNF proves exactly the
missing-base directions and bracket sign used above. The completions
CNF is the same necessary formula with the four recorded primary models
blocked, independently binding that supplementary enumeration.

`two_triangles_certificate.json` records the four full-parameter shape
maps, relabeling, determinant counts, exact reference and metric
identities, and four generic completions. The metric helper can also
be run independently:

```sh
python3 research/type7_completion/remaining_two_triangles_metric.py
```
