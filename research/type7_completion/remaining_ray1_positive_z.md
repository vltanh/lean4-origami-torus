# Excluding the positive-axial endpoint

The [nonedge15 cut](remaining_ray1_nonedge.md) and
[two-polarization contradiction](remaining_ray1_negative_x.md) leave
the endpoint regime `d0/h1 -> 1`. This note excludes that last regime
uniformly in every relative collapse rate. Thus all three canonical
endpoint regimes are now excluded. The earlier marked symmetries and
complete first-stretch cover close the entire ray-1 two-block limit;
the other ray-1 limit families and ray 2 still require proofs.

Use the published endpoint coordinates, put `h=h1`, and set

\[
S=h-d_0=d_2+d_3+d_4+d_5+d_6+d_7.
\]

Every finite deficit is positive. In this regime the earlier metric
estimates and exact virtual-direction consequences give

\[
b_1/h\to1,\quad P_{2x}/h\to0,\quad
Z_2/(\delta h)\to0,\quad (H_2-H_1)/h\to1/2.
\]

No comparison between `t`, `h`, and the first transverse width `delta`
is imposed.

## 1. A uniform factorization in the actual face027 plane

The actual face027 has consistent intrinsic lifts. Its spatial plane
can therefore be given orthonormal physical coordinates in which

\[
r_2=(x_2,yv_2),\quad r_7=(h_7,yv_7),\qquad
x_2=1/2-S,\quad h_7=1/2-d_7.
\]

Let the planar projection of vertex1 be
`(h0+u1, y(v1+t q1))`, and let `W1` be its signed perpendicular
distance to this plane. Here `h0=1/2-d0`. Polarizing the six K4 metrics
on vertices `0127` gives exactly

\[
x_2u_1+v_2q_1=-2d_0S,\qquad
h_7u_1+v_7q_1=-2d_0d_7.
\tag{1}
\]

The determinant `D=x2*v7-h7*v2` tends to `-1/4`. Since
`0<d7<=S`, both unknowns are `O(d0*S)` uniformly. The norm equation
then gives

\[
W_1^2=-2h_0u_1-2v_1q_1-u_1^2-tq_1^2.
\]

For a completely relative error estimate, put `rho=d7/S`, so
`0<=rho<=1`, and write

\[
u_1=d_0S U,\quad q_1=d_0S Q,\qquad
U=\frac{2(v_2\rho-v_7)}D,\quad
Q=\frac{2(h_7-x_2\rho)}D.
\]

Exact substitution yields

\[
W_1^2=d_0S\left\{
\frac{4h_0}{x_2}
-2\left(v_1-\frac{h_0v_2}{x_2}\right)Q
-d_0S(U^2+tQ^2)\right\}.
\tag{2}
\]

The expression in braces tends uniformly to four for `rho` in the
closed unit interval. Thus

\[
\boxed{W_1^2=(4+o(1))d_0S.}
\tag{3}
\]

The error is relative to the possibly arbitrarily small product
`d0*S`. There is no separate error involving only `t` or a phase.

To compare with the original face013 incidence frame, set

\[
a_X=P_{2x}/h,\quad a_Y=Z_2/(\delta h),\quad e=Z_7/\delta.
\]

The scalar triple product divided by the area of face027 gives

\[
\frac{W_1}{\delta h}\longrightarrow 2a_Xe-a_Y
\tag{4}
\]

along any subsequence where those quantities converge, after choosing
the normal orientation accordingly. The exact denominator tends to
`1/4`; no small area is divided. In the positive-axial case both
`aX,aY` tend to zero. Equations (3)–(4) and `d0/h->1` therefore imply

\[
\boxed{S=o(\delta^2h).}
\tag{5}
\]

For comparison, the previously excluded negative-X profile had
`(aX,aY,e)=(-1,0,1)`, which gives `d0/(delta^2*h)->1` by the same
identity. This comparison is not used to exclude the present case.

## 2. The metric and finite cones force one normal profile

The [profile lemma](remaining_ray1_positive_z_profile.md) uses the
actual face027 plane and (5). Its two exact vertex6 polarizations have
a coefficient determinant tending to `-1/4`. They show that its planar
coordinates satisfy `U6,lambda6=o(delta^2*h)`. The restored edge06 norm
then forces `W6=o(delta)`, and the explicitly controlled plane change
gives `Z6/delta->0` in the original axis frame.

All five surviving positive-axial cones have independently checked
rational row combinations proving `d=0 => c=e<=0`. First-width
normalization therefore gives

\[
(Z_5,Z_6,Z_7)/\delta\longrightarrow(-1,0,-1).
\tag{6}
\]

The source first-stretch cover also gives `Z4/delta->0`, and the gauge
has `Z3=0`. The fifteen new implication certificates retain every zero
bracket and cover all 172 surviving primary words. The profile lemma's
checker replays its original 426-certificate and 17-certificate sources
before accepting these implications.

## 3. A four-vertex metric stress gives a contradiction

The six edges of the clique `3456` have the consistent vertical lifts

\[
(v_3,v_4,v_5+1,v_6+1).
\]

Set

\[
A=v_4-v_6-1\to-1/2,\qquad
B=-(v_3-v_5-1)\to1/2,
\]

and use coefficients `(A,B,-A,-B)` on these four vertices. Their sum
and their weighted vertical lift both vanish. The elementary identity

\[
\sum_{i<j}c_ic_j|r_j-r_i|^2
=-\left|\sum_i c_i r_i\right|^2
\quad\text{when }\sum_i c_i=0
\]

therefore turns the **actual metric equations** into

\[
\left|A(r_3-r_5)+B(r_4-r_6)\right|^2=E,
\tag{7}
\]

with the exact horizontal energy

\[
\begin{aligned}
E={}&A^2(d_3+d_4)^2+B^2(d_4+d_5)^2\\
&-2AB\{d_4(1-d_3-d_4-d_5)-d_3d_5\}.
\end{aligned}
\]

The companion checks all six archived cocycles and this factorization.
There is no remainder in `t` or in any vertical phase. Since
`d3+d4+d5<=S`, eventually `|A|,|B|<=1` and `S<=1`, giving `E<=8S`.

On the other hand, the normal component of the vector on the left of
(7), divided by `delta`, tends by (6) to

\[
(-1/2)(0-(-1))+(1/2)(0-0)=-1/2.
\]

Its squared norm is consequently at least `delta^2/16` eventually.
Equation (7) implies

\[
\delta^2\le128S,
\tag{8}
\]

whereas (5) and `h->0` give `S/delta^2->0`. This contradiction excludes
the positive-axial endpoint. It uses an exact metric identity, not a
parametrization of nearby solutions or an assumed relation among small
scales.

## 4. Additional checked folded-phase estimate

The following estimates were useful during discovery but are not needed
for the contradiction above.

Put `B=v4-v2`, `z=ζ4-ζ2`, `eps=d2+d3`, and `lambda=H2-H1`.
The actual face214 has intrinsic vectors12 `(-h,b1)` and24
`(eps,B)`. Its exact metric polarization is

\[
b_1(z-B)+t\{P_2\cdot(P_4-P_2)+\lambda z+h\,\mathrm{eps}\}=0.
\tag{9}
\]

Here `P2/h->0`, `P4->0`, `lambda/h->1/2`, `z->0`, and `b1/h->1`.
Divide (9) by `h` to obtain `z-B=o(t)`. The folded axis definition also
gives exactly

\[
z+B=2b_2+t(H_4-H_2).
\]

The published endpoint constants are `b2/t->1/4`, `H4->-1/4`, and
`H2->1/4`. Consequently the right side is `o(t)`, proving

\[
\boxed{v_4-v_2=o(t),\qquad\zeta_4-\zeta_2=o(t).}
\tag{10}
\]

This controls a folded coordinate without replacing its axial baseline
by an unjustified bounded correction.

## 5. An exact finite-h reference

The planar reference in `remaining_ray1_endpoint.md` extends to this
deficit direction for every sufficiently small `h,t,u`: retain all
vertices except1, and replace

\[
x_1=h-1/2,\quad v_1=(1-2h)v_2,\quad r_1=(1-2h)r_2.
\]

Its horizontal weights are `h0=1/2-h`, `h1=h`, and all others `1/2`.
All 24 metric equations remain exact. The same normal extension with
parameter `p` still satisfies 22 equations; rows25 and45 have the
unchanged residual `-t*A*(1-p)/(A-t*p)`.

The companion checks these statements symbolically. The reference has
degenerate intrinsic faces and is not asserted to parametrize all
nearby solutions. The proof in Sections 1–3 avoids that additional
parametrization problem entirely.

```sh
python research/type7_completion/remaining_ray1_positive_z.py
```
