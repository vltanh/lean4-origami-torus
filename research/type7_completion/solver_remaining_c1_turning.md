# Ray 1: regular C1 caps are impossible

The regular C1 limit cannot occur for marking 1. Here **regular** means
that both endpoint triangles 234 and 067 are noncollinear and that
`0<alpha,beta<1`. The proof uses the closed C1 metric identities and four
of the independently certified common bracket signs. It treats zero
individual deficits explicitly. It does not cover a collinear endpoint
cap or a height endpoint, and supplies no numerical height bound.

`solver_remaining_c1_turning.py` checks every polynomial identity and
factorization used below. Its input packages are the
[C1 circle identities](solver_remaining_c1_geometry.md) and the
[complete regular C1 topology cover](exhaustive_c1_angles.md). The latter's
six CNFs must have accepted independent RUP proofs.

## 1. Metric and orientation data

Write `delta_i=1/2-h_i`. Marking 1 gives

\[
\delta_i\ge0,\qquad\sum_{i=0}^7\delta_i=1/2.
\tag{1}
\]

The regular perimeter-one caps imply

\[
\delta_2,\delta_3,\delta_6,\delta_7>0,
\quad\delta_2+\delta_3<1/2,
\quad\delta_6+\delta_7<1/2.
\tag{2}
\]

Their orientations are positive. Use the circle-package vectors

\[
E_2=P_2-P_3,\quad E_3=P_4-P_3,\quad F=P_7-P_6,
\quad Y_0=\alpha P_2,\quad Y_5=\beta E_3-R_5.
\]

Thus `|E2|=h2`, `|E3|=h3`, `|P7|=h7`, `|F|=h6` are positive.
The certified signs `[0123]>=0`, `[0127]<=0`, `[3456]<=0`,
`[4567]<=0` give

\[
\operatorname{cross}(E_2,Y_0)\ge0,\quad
\operatorname{cross}(Y_0,P_7)\le0,\quad
\operatorname{cross}(E_3,Y_5)\le0,\quad
\operatorname{cross}(Y_5,F)\ge0.
\tag{3}
\]

Every inequality in (3) is weak; the argument does not assume these
limiting brackets remain nonzero.

## 2. The first pair gives an oriented angle

Put

\[
p=\delta_0,\quad q=\delta_1,\quad s=p+q,
\quad r=\delta_2,\quad a=\delta_3,
\quad\ell=\delta_6,\quad t=\delta_7,
\]

and `h=h2=1/2-r`, `k=h7=1/2-t`, `R=r+t`, `L=a+ell`.
Then `R,L>0` and `s+R+L<=1/2`, so `s<1/2`.
The first circle pair gives

\[
\begin{aligned}
\sigma&=\sigma_0=1/2+(1-\alpha)p-\alpha q,\\
n^2=|Y_0|^2&=\sigma^2-2(1-\alpha)p,\\
Y_0\cdot(E_2/h)&=1-\sigma-q/h,\\
Y_0\cdot(P_7/k)&=p/k-\sigma.
\end{aligned}
\tag{4}
\]

For example, the first dot formula follows from
`Y0=alpha*E2-R1`, the `R1·E2` identity, and
`rho1+sigma0=1-alpha*h2`.
The vector is nonzero, including when `p` or `q` is zero: with
`w=alpha*p+(1-alpha)*q`, exact expansion gives

\[
n^2-(1/2-s)^2
=w(1-2s)+[\alpha p-(1-\alpha)q]^2\ge0.
\tag{5}
\]

Let `psi` be the counterclockwise angle from `E2` to `Y0`, and `theta`
the clockwise angle from `Y0` to `P7`. Equation (3) places both in
`[0,pi]`. Equation (4) gives

\[
\cos\psi-\cos\theta
=\frac{1-q/h-p/k}{n}>0,
\tag{6}
\]

because

\[
hk-qk-ph
=\tfrac12(\tfrac12-s-r-t)+rt+pr+qt>0.
\tag{7}
\]

The first term is positive by (1)–(2). Hence `theta>psi`, and the
clockwise angle from `E2` to `P7` is

\[
\gamma=\theta-\psi\in(0,\pi].
\tag{8}
\]

## 3. An upper bound for cos(gamma)

Suppose first `p,q>0` and `gamma<pi`, and set `u=cos(gamma)`.
Eliminating `alpha` from (4) gives

\[
n^2=\sigma^2-\frac{2p}{s}\sigma+\frac{p(1-2q)}s.
\]

The Gram determinant of `Y0`, `E2/h`, `P7/k` vanishes. Therefore the
following quadratic has the real root `sigma`:

\[
n^2(1-u^2)-(1-q/h-\sigma)^2-(p/k-\sigma)^2
+2u(1-q/h-\sigma)(p/k-\sigma)=0.
\tag{9}
\]

Its leading coefficient is `-(1-u)^2`. The independently checked
discriminant is

\[
-\frac{4pq(u-1)^2(u+1)}{hk s^2}
\left(hk[(1-2s)u+1+2s]-2s(h+k-s)\right).
\tag{10}
\]

A real root requires a nonnegative discriminant. All factors outside
the leading minus sign are positive, so

\[
\cos\gamma\le U
:=\frac{2s(h+k-s)-hk(1+2s)}{hk(1-2s)}.
\tag{11}
\]

There is no lost zero-deficit case. If `p=0,q=s>0`, then `n=sigma<=1/2`,
`theta=pi`, and

\[
\cos\gamma\le-1+2s/h\le U,
\qquad
U-(-1+2s/h)
=\frac{2s(h-s)(1-2k)}{hk(1-2s)}\ge0.
\tag{12}
\]

Here `h>s` follows from `s+R+L<=1/2` and `L,t>0`.
If `q=0,p=s>0`, then `n=1-sigma<=1/2`, `psi=0`, and similarly

\[
\cos\gamma\le-1+2s/k\le U,
\qquad
U-(-1+2s/k)
=\frac{2s(k-s)(1-2h)}{hk(1-2s)}\ge0.
\tag{13}
\]

If `s=0`, equations (4) give `psi=0`, `theta=pi`, so `gamma=pi`.
A case with `gamma=pi` will be handled directly below.

## 4. Merging the two cap angles

For nonnegative `u,v` with `u+v<1`, define

\[
\Phi(u,v)=\arctan\sqrt{\frac{uv}{1-u-v}}.
\]

The elementary merging inequality is

\[
\Phi(u,v)+\Phi(x,y)\le\Phi(u+x,v+y)
\quad\text{when }u+v+x+y<1.
\tag{14}
\]

For completeness, put

\[
A_0=\sqrt{uv},\ B_0=\sqrt{xy},\quad
P=\sqrt{1-u-v},\ Q=\sqrt{1-x-y},\
Z=\sqrt{1-u-v-x-y}.
\]

Since `Q>=A0`, `P+Z<=2`, and `x+y>=2B0`,

\[
Q(P-Z)=\frac{Q(x+y)}{P+Z}\ge A_0B_0.
\]

The symmetric inequality gives
`PQ-A0*B0 >= Z*max(P,Q)>0`. Tangent addition is therefore on its
positive principal branch and yields

\[
\tan(\Phi(u,v)+\Phi(x,y))
=\frac{A_0Q+B_0P}{PQ-A_0B_0}
\le\frac{A_0+B_0}{Z}
\le\frac{\sqrt{(u+x)(v+y)}}{Z}.
\]

The last step is Cauchy's inequality, proving (14).

Let `A` be the clockwise angle from `E2` to `E3`, and `B` the
counterclockwise angle from `P7` to `F`. The positive cap orientations
make both angles lie in `(0,pi)`. The cosine rule for their perimeter-one
triangles gives

\[
A/2=\Phi(2r,2a),\qquad B/2=\Phi(2t,2\ell).
\tag{15}
\]

If `s>0`, (14) gives

\[
A+B\le2\arctan\sqrt{\frac{2RL}{1/2-R-L}}<\pi.
\tag{16}
\]

Also `A+B<pi` when `s=0`. Indeed the product of the two half-angle
tangents in (15) is strictly less than one: their squared denominator
is `(1-2r-2a)(1-2t-2ell)`, which is at least
`(2r+2a)(2t+2ell)` and strictly larger than `(2r)(2a)(2t)(2ell)`.
Thus their sum is less than `pi/2`.

## 5. The first pair forces cross(E3,F) negative

For `s>0`, put `Lmax=1/2-s-R>=L>0` and `H0=1/4-R/2>0`.
Since

\[
hk=H_0+rt\ge H_0,
\]

and the expression in (11) decreases as `hk` increases with `h+k=1-R`
fixed, `U<=U0`, where `U0` is (11) with `hk=H0`.
Equation (16) and `1/2-R-L>=s` give

\[
\cos(A+B)\ge C
:=\frac{s-2R L_{\max}}{s+2R L_{\max}}.
\]

The decisive exact factorization is

\[
C-U_0=\frac{4sL_{\max}}{(s+R)(1-2R)}>0.
\tag{17}
\]

Together with (11)–(13), it gives
`cos(gamma)<cos(A+B)`, hence `gamma>A+B`.
If `gamma=pi`, including `s=0`, the same conclusion follows directly
from `A+B<pi`.

Choose the direction of `E2` as angle zero. Then `P7` has angle
`-gamma`, `E3` angle `-A`, and `F` angle `-gamma+B`. Consequently

\[
\operatorname{cross}(E_3,F)
=h_3h_6\sin(A+B-\gamma)<0,
\tag{18}
\]

since `-pi<A+B-gamma<0`. Equivalently, the exact raw bracket identity
`2[3467]=cross(E3,F)` makes `[3467]` strictly negative.

## 6. The second pair forces the opposite sign

Apply the norm argument (5) to `Y5`, with

\[
p'=\delta_5,\quad q'=\delta_4,\quad
h'=h_3,\quad k'=h_6,\quad\alpha'=\beta.
\]

It gives `n5=|Y5|>0`. The second circle pair gives

\[
Y_5\cdot(E_3/h_3)=1-\sigma_5-\delta_4/h_3,
\qquad
Y_5\cdot(F/h_6)=\delta_5/h_6-\sigma_5.
\tag{19}
\]

Let `psi5` be clockwise from `E3` to `Y5`, and `theta5`
counterclockwise from `Y5` to `F`. Their directions follow from the last
two inequalities of (3), so both lie in `[0,pi]`. Now

\[
\cos\psi_5-\cos\theta_5
=\frac{1-\delta_4/h_3-\delta_5/h_6}{n_5}>0.
\]

This is the same positive factorization (7), whose remaining deficit sum
is now `delta0+delta1+delta2+delta7>0`. Thus `theta5>psi5` and the
counterclockwise angle from `E3` to `F` is in `(0,pi]`. Therefore

\[
\operatorname{cross}(E_3,F)\ge0,
\tag{20}
\]

contradicting (18). This excludes every regular C1 ray-1 limit covered by
the stated hypotheses.

## Replay and scope

```sh
python research/type7_completion/solver_remaining_c1_turning.py
```

The script replays the source circle and determinant identities, then
checks the norm lower bound, strict dot gap, full Gram discriminant,
both zero-deficit cases, cap half-angle formula, monotonicity identity,
strict gap (17), and the raw-bracket orientation in (18). The finite
topology proof remains independently replayable through
`exhaustive_c1_angles.py` and `solver_cnf_certificates.py`.

The proof is specific to the ray-1 deficit sum `1/2`. Ray 2 has deficit
sum `3/2`, so these positive gaps do not follow. A collinear cap or a
height endpoint also requires its own argument: their vanishing cap
brackets do not justify the regular-cap topology units. The separate
[one-collinear-cap extension](solver_remaining_c1_collinear_rank.md)
and [flat normal-stretch proof](solver_remaining_c1_flat_stretch.md)
now cover all collinear caps in the interior height rectangle.
