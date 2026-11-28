# Exact sections of the two C0 annuli

This package supplies exact section and length identities for a regular
ray-1 C0 limit on `0<u<v<1/2`. It does not itself exclude that region.
A perimeter argument still has to establish the required nesting and
convexity, including limiting contacts. The source checker calls the
existing full 29-row metric binding and expands every new identity
exactly.

Use the notation of the [C0 metric proof](remaining_c0_height_order.md):

\[
\begin{gathered}
\ell_u=1-2u,\quad\ell_v=1-2v,\quad K=v-u>0,\\
L=d_1+d_2=|P_3|,\quad M=d_6+d_7=|P_6|,\quad
D=d_0+L+M,\\
E=P_3-P_2,\quad F=P_7-P_6,\\
Q_4=P_4-2uP_3-\ell_uP_6,\quad
Q_5=P_5-2vP_3-\ell_vP_6,\\
r=h_3-\ell_uD,\quad s=h_5-2vD,\\
S=\ell_vQ_4-\ell_uQ_5,\quad W=vQ_4-uQ_5,\\
R_S=\ell_vr+\ell_us,\qquad R_W=vr+us.
\end{gathered}
\]

Here `P0=P1=0`, `h_i=1/2-d_i`, the deficits sum to `1/2`, and
regular caps give `d1,d2,d6,d7>0`. The circle and dot identities are

\[
\begin{gathered}
|Q_4|=r>0,\quad |Q_5|=s>0,\quad Q_4\cdot Q_5=-rs+d_4,\\
|E|=h_2,\quad |F|=h_6,\\
E\cdot S=h_2R_S-\ell_v(h_2-d_3),\quad
F\cdot W=h_6R_W-u(h_6-d_5).
\end{gathered}
\]

## 1. The direct annulus has sections of perimeter one

Cutting the triangulation along the two cap cycles `123` and `067`
leaves two annuli. The one containing neither intermediate vertex
has faces `013,023,027,127,167,016`. At height `t`, its section has
the cyclic vertex sequence

\[
0,\quad2tP_3,\quad2tP_2,\quad
2tP_2+(1-2t)P_7,\quad(1-2t)P_7,\quad(1-2t)P_6.
\tag{1}
\]

Its perimeter is exactly

\[
2t(L+h_2+h_1)+(1-2t)(h_7+h_6+M)=1.
\]

The certified cap, core and turning signs make five of its turns
weakly clockwise. Its remaining turn, at the origin, is
`2t(1-2t)cross(P3,P6)`. Consequently `cross(P3,P6)<=0` supplies
the remaining local convexity condition. This statement alone does
not determine which of the two section curves is contained in the
other.

## 2. The two critical sections of the other annulus

At height `u`, define

\[
\begin{aligned}
C_4&=2uP_3+\ell_uP_6,\\
D_{56}&=(u/v)P_5+(K/v)P_6,\\
D_{05}&=(u/v)P_5,\\
D_{57}&=(u/v)P_5+(K/v)P_7.
\end{aligned}
\]

The section is the five-gon

\[
P_4,C_4,D_{56},D_{05},D_{57}.
\tag{2}
\]

Its sides lie respectively in faces `346,356,056,057,457`.
Their vectors are

\[
-Q_4,\quad(u/v)Q_5,\quad-(K/v)P_6,\quad
(K/v)P_7,\quad(W-KF)/v.
\]

At height `v`, put

\[
\begin{gathered}
D_{24}=(\ell_v/\ell_u)P_4+(2K/\ell_u)P_2,\quad
D_{14}=(\ell_v/\ell_u)P_4,\\
D_{34}=(\ell_v/\ell_u)P_4+(2K/\ell_u)P_3,\quad
C_5=2vP_3+\ell_vP_6.
\end{gathered}
\]

The other critical section is

\[
P_5,D_{24},D_{14},D_{34},C_5,
\tag{3}
\]

with sides in faces `245,124,134,346,356`. Its side vectors are

\[
(S-2KE)/\ell_u,\quad-(2K/\ell_u)P_2,\quad
(2K/\ell_u)P_3,\quad-(\ell_v/\ell_u)Q_4,\quad Q_5.
\]

The apparently new side lengths are exact squares:

\[
\begin{aligned}
|W-KF|^2&=(u-R_W+Kh_6)^2,\\
|S-2KE|^2&=(\ell_v-R_S+2Kh_2)^2.
\end{aligned}
\tag{4}
\]

Their correct square roots are positive, because

\[
\begin{aligned}
u-R_W+Kh_6&=u h_4+K(1/2-d_4-d_5-d_6)>0,\\
\ell_v-R_S+2Kh_2&=\ell_vh_4+2K(1/2-d_2-d_3-d_4)>0.
\end{aligned}
\]

The remaining sums of deficits are nonnegative and `h4>0` follows
from regularity of the endpoint caps. Thus (2) has perimeter

\[
r+(u/v)s+(K/v)(M+h_7)+(u-R_W+Kh_6)/v=1,
\]

and (3) has perimeter

\[
(\ell_v-R_S+2Kh_2)/\ell_u
 +(2K/\ell_u)(h_1+L)+(\ell_v/\ell_u)r+s=1.
\]

All ten turns are expanded in the companion. For (2), sufficient
additional weak signs for clockwise turns are

\[
[0356]\ge0,\quad[0457]\le0,\quad
u[3456]-K[3467]\le0.
\]

For (3) they are

\[
[1245]\ge0,\quad[1346]\le0,\quad
\ell_v[3456]-2K[2356]\le0.
\]

The other turns follow from the cap signs and `[3456]<=0`. These
are statements about actual determinants; a generic completion can
be used only to infer the corresponding weak actual signs.

## 3. Strict shortening of the three middle projected edges

Use the Minkowski inner product
`<(t,x),(s,y)>=ts-x·y`. The
[strict core bound](exhaustive_c0_angles.md) says that

\[
T=(D,P_6-P_3)
\]

is future timelike. The vectors
`a=(r,Q4)` and `b=(s,-Q5)` are future null and satisfy
`<a,b>=d4`. Hence

\[
a+\ell_uT=(h_3,P_4-P_3),\qquad
b+2vT=(h_5,P_6-P_5)
\]

are future timelike. Also

\[
c=a+b+2KT=(1/2+d_4,P_4-P_5).
\]

Since `T` is future timelike and `a,b` are nonzero future null,

\[
\langle c,c\rangle
=2d_4+4K\langle T,a+b\rangle+4K^2\langle T,T\rangle>2d_4.
\]

The complement `(1,0)-c=(h4,P5-P4)` is therefore future timelike
as well. Consequently

\[
|P_4-P_3|<h_3,\quad |P_5-P_4|<h_4,\quad |P_6-P_5|<h_5.
\tag{5}
\]

The middle chain has length less than `h3+h4+h5=1+D`.
This is a metric consequence, not a claim that this chain encloses
either cap chain.

## 4. Actual zero mixed brackets

The exact dot discriminants give

\[
|S|^2-(E\cdot S/h_2)^2
=\frac{2\ell_v^2d_3}{h_2^2}
 \left(d_2(h_2-d_3)+\frac{\ell_u}{\ell_v}h_2(h_2-d_3-d_4)\right),
\]

and the reflected formula for `W,F,d5`. The parenthesis is strictly
positive for regular caps. Therefore `[2345]=0` forces `d3=0`,
and `[4567]=0` forces `d5=0`; the converses follow from the same
identities.

The parallel directions on these faces are determined as well. For
`d3=0`, the circle Gram inequality gives

\[
0\le2rs-d_4=2D(\ell_v/2-\ell_us).
\]

As `s=d4+lv*D>d4`, it follows that `(lu/lv)*d4<1/2` and

\[
S=\ell_v\left(-1/2+(\ell_u/\ell_v)d_4\right)E/h_2
\]

is a strictly negative multiple of `E`. Similarly, on `d5=0`,

\[
0\le2rs-d_4=4D(u/2-vr),
\]

so `(v/u)*d4<1/2` and `W` is a strictly negative multiple of `F`.
No generic sign is fixed by an actual zero bracket.

## Reproduction

```sh
python research/type7_completion/solver_remaining_c0_sections.py
```

This is an exact algebraic helper. A new embedding exclusion needs
an additional geometric argument; no SAT result or numerical sample
is used in this package.
