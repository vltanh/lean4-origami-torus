# Relative short-edge directions in interior C0

For either remaining marking, each endpoint-cap edge `12,23,67,07`
has a unit transverse limiting direction after division by its own
positive horizontal length. Both its intrinsic vertical displacement
and its normalized spatial axial displacement are `O(t*h)`, where
`t=1/y²` and `h` is that edge's horizontal length. This holds throughout
`0<u,v<1/2`, including arbitrarily fast shrinking edges.

These are relative estimates, not exclusions. The
[line-endpoint proof](remaining_c0_line_endpoints.md) uses the estimate
for edge 12 in a further normal stretch.

## 1. Edge 12

In the axis-01 chart write

\[
\ell=\zeta_1,\quad b=v_1,\quad h=h_1>0,\quad
r=(1/2-h_0)/h,\quad k=h_0+r-1,
\]
\[
w=P_2/h,\qquad
a=(\zeta_2-\zeta_1)/(th),\qquad
g=(v_2-v_1)/(th).
\]

The strict nearest lifts give `0<r<1`: indeed
`X02-1/2=(r-1)h<0` and `h0<1/2`. The three exact metric equations
on 01,02,12 give

\[
\ell^2=b^2+th_0^2,\qquad
\ell a-bg=k,\qquad |w|^2+ta^2=1+tg^2.
\tag{1}
\]

There is no boundedness assumption in the definitions of `w,a,g`.
Triangle 124 has zero cocycle period in both markings. Put
`theta=zeta4-ell`, and use its intrinsic edge components `X14,V14`.
Its exact polarization is

\[
w\cdot P_4+a\theta=-X_{14}+gV_{14}.
\]

Eliminating `a` gives

\[
\left(\frac{b\theta}{\ell}-V_{14}\right)g
=-X_{14}-w\cdot P_4-\frac{k\theta}{\ell}.
\tag{2}
\]

Here `ell,b -> 1/2`, `theta -> u-1/2`, and `V14 -> 1/2-u`.
The coefficient of `g` tends to `-(1-2u) != 0`. Since `k` and all
other coefficients are bounded, (2) gives `|g|<=C(1+|w|)`.

The exact polynomial consequence of (1) is

\[
\ell^2|w|^2
=\ell^2+t^2h_0^2g^2-2tbkg-tk^2.
\tag{3}
\]

It implies `|w|<=C1(1+t|g|)`. Substitute into the preceding bound
and absorb its multiple of `t|g|`. Then `g,w,a` are bounded, and
the last equation in (1) gives `|w| -> 1`. Thus

\[
v_2-v_1=O(th_1),\qquad \zeta_2-\zeta_1=O(th_1).
\tag{4}
\]

Every bound is relative to the actual edge length. No ratio of `h1`
and `t`, a cap area, or a transverse width has been restricted.

## 2. The other three cap edges

For edge 23, the exact finite equations are those of the
[C1 short-edge lemma](remaining_c1_short_edges.md). Its proof uses
only the positive axis limit and a nonzero polarization coefficient.
Substitute `alpha=1`, `beta=2v`: in C0 that coefficient is
`-(1-2v) != 0`. The same absorption gives the relative unit direction
and both `O(t*h2)` estimates. The checker replays its original finite
identities and both marked cocycles.

The checked reflection `p(i)=1-i mod 8` maps 12 to 07 and 23 to 67.
It sends `(u,v)` to `(1/2-v,1/2-u)`, still in the open height square.
Its axis is the reversed edge 01, so reanchoring preserves the relative
estimates. This covers all four cap edges for both markings.

## 3. Two finite identities at the h1=0 endpoint

For the line endpoint of ray 1, put `d_i=1/2-h_i` for `i!=1`.
The exact budget is `h=h1=sum_(i!=1)d_i`. Keep `w,a,g` from Section 1.
Let

\[
a_3=(\zeta_3-\zeta_1)/t,\qquad g_3=(v_3-v_1)/t.
\]

These are bounded by the already proved
[relative diagonal-13 estimate](exhaustive_c0_double_coincidence.md),
which also applies when its horizontal length tends to `1/2`.
Two further exact finite polarizations give

\[
\begin{aligned}
w\cdot P_7+\zeta_7a-v_7g&=d_0/h-h_7,\\
w\cdot P_3+t(aa_3-gg_3)&=d_2/h-1/2-d_2+h.
\end{aligned}
\tag{5}
\]

The first comes from the combination `E02-E01-E27+E17`; the
second from `E12+E13-E23`. All horizontal and vertical cocycles
are checked explicitly.

At this endpoint `P3,P7 -> e/2`, where `e` is the positive line
direction, and `zeta7,v7 -> 0`. After passing to a subsequence, (5)
therefore gives

\[
\frac{d_0}{h},\frac{d_2}{h}\longrightarrow\frac{1+w_x}{2}.
\]

Since `(d0+d2)/h<=1`, it follows that `w_x<=0`. This statement
does not assume that the unit vector `w` is already parallel to the
line. It will constrain the direction after the next normal stretch.

## Reproduction

```sh
python research/type7_completion/remaining_c0_short_edges.py OUTPUT
```

The exact replay checks both relative-edge sources, both markings,
the complete reflected edge cover, and the finite endpoint identities.
