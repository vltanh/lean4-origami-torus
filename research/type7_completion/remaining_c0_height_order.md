# Excluding the regular ray-1 C0 region with u >= v

No regular ray-1 C0 limit has `0<v<=u<1/2`. Both endpoint triangles
123 and 067 are assumed noncollinear. The proof includes the diagonal
and every zero individual deficit permitted by these assumptions.
It gives an asymptotic exclusion, without a numerical height bound.

The metric argument below proves the actual strict disjunction

\[
[2345]>0\quad\text{or}\quad[4567]>0.                    \tag{1}
\]

The separate [topological height-order implications](exhaustive_c0_height_order.md)
rule out both branches when `u>=v`. Their independent Boolean
certificates are a required premise. The off-diagonal half `v>u`,
collinear caps, and height endpoints remain outside this theorem.

## 1. The uniform metric identities

Use `d_i=1/2-h_i>=0`, with `sum(d_i)=1/2`. Regularity gives
`d1,d2,d6,d7>0`. In particular

\[
b_*=d_0+d_1+d_7>0,\qquad
D=\tfrac12-d_3-d_4-d_5=b_*+d_2+d_6>0.
\]

Let `lu=1-2u`, `lv=1-2v`, and define

\[
\begin{aligned}
Q_4&=P_4-2uP_3-l_uP_6,&r&=h_3-l_uD,\\
Q_5&=P_5-2vP_3-l_vP_6,&s&=h_5-2vD,\\
E&=P_3-P_2,&F&=P_7-P_6,\\
S&=l_vQ_4-l_uQ_5,&W&=vQ_4-uQ_5.
\end{aligned}
\]

The closed C0 metric system gives

\[
\begin{gathered}
|E|=h_2>0,\qquad |F|=h_6>0,\\
|Q_4|^2=r^2,\quad |Q_5|^2=s^2,\quad Q_4\cdot Q_5=-rs+d_4,\\
\frac{E\cdot S}{h_2}=l_vr+l_us-l_v(1-d_3/h_2),\\
\frac{F\cdot W}{h_6}=vr+us-u(1-d_5/h_6).
\end{gathered}                                                       \tag{2}
\]

The companion checks all five scalar identities by exact expansion.
It independently checks their seven source rows against the full
29-row auxiliary system, including the two required product-scale
syzygies. No product scale is set to zero.

The exact bracket formulas are

\[
2[2345]=-\operatorname{cross}(E,S),\qquad
[4567]=-\operatorname{cross}(W,F),\qquad
2[3456]=-\operatorname{cross}(Q_4,Q_5).
\tag{3}
\]

The common topological sign `[3456]<=0` therefore gives
`cross(Q4,Q5)>=0`. The [strict turn theorem](exhaustive_c0_turning.md)
gives a counterclockwise angle `gamma` from `E` to `F` with
`0<gamma<pi`.

## 2. Three middle angles

Since `u>=v`, the two ratios

\[
k=l_u/l_v,\qquad l=v/u
\]

belong to `[0,1]`. In the stated interior domain they are positive;
both equal one on the diagonal. Put

\[
S'=S/l_v=Q_4-kQ_5,\qquad W'=W/u=lQ_4-Q_5,
\qquad e=E/h_2,\quad f=F/h_6.
\]

For brevity set

\[
\begin{aligned}
\sigma&=\tfrac12-d_3+k(d_3+d_4),&
\tau&=\tfrac12-d_5+l(d_4+d_5),\\
n_S^2&=\sigma^2-2kd_4,&n_W^2&=\tau^2-2ld_4,\\
a&=1-\sigma-d_3/h_2,&b&=1-\tau-d_5/h_6,\\
c&=\sigma\tau-(1+kl)d_4.
\end{aligned}
\]

Equations (2) imply

\[
|S'|=n_S,\quad |W'|=n_W,\quad
(-e)\cdot S'=a,\quad W'\cdot(-f)=b,\quad S'\cdot W'=c.
\]

Define the unoriented angles in `[0,pi]`

\[
\eta_S=\arccos(a/n_S),\quad
\eta_W=\arccos(b/n_W),\quad
\theta=\arccos(c/(n_Sn_W)).
\]

We prove the strict bound

\[
\boxed{\eta_S+\theta+\eta_W<\pi.}                       \tag{4}
\]

## 3. Norms and cosine ranges, including zero deficits

The elementary norm identity used in the C1 proof gives

\[
n_S^2\ge(\tfrac12-d_3-d_4)^2>0,\qquad
n_W^2\ge(\tfrac12-d_4-d_5)^2>0.
\]

For example the first difference is

\[
[(1-k)d_4+kd_3][1-2(d_3+d_4)]
+[(1-k)d_4-kd_3]^2\ge0.
\]

The first cosine lies in `[-1,1]` because

\[
n_S^2-a^2=
\frac{2d_3}{h_2^2}
\left[d_2(h_2-d_3)+kh_2(h_2-d_3-d_4)\right]\ge0.
\]

The second follows from the identical formula with
`(d2,d3,h2,k)` replaced by `(d6,d5,h6,l)`. Every factor is
nonnegative by the deficit budget.

For the middle cosine,

\[
n_S^2n_W^2-c^2=(1-kl)^2d_4(2rs-d_4)\ge0.              \tag{5}
\]

To check the last inequality without assuming a realization, use
`u>=v` and set `w=2v`. Then

\[
r\ge r_0=d_4+d_5+wD,\qquad s=h_5-wD>0,
\]

and the exact factorization is

\[
r_0s-d_4/2
=(1-w)d_5(\tfrac12-d_4-d_5)
+wd_3(\tfrac12-d_3-d_4)+w(1-w)D^2\ge0.
\]

These identities also cover `d3=0`, `d4=0`, and `d5=0`.
On the diagonal `k=l=1`, equation (5) gives `theta=0`.

## 4. A strict Gram inequality with exact positive coefficients

Put

\[
x=a/n_S,\qquad y=b/n_W,\qquad z=c/(n_Sn_W),
\qquad G=x^2+y^2+z^2+2xyz-1.
\]

The companion proves the explicit lower bound

\[
\boxed{64h_2^2h_6^2n_S^2n_W^2G\ge(2b_*)^8>0.}        \tag{6}
\]

Here is the exact finite certificate behind (6). Clear the positive
denominators in `G` and use the six simplex coordinates

\[
(B,D_2,D_3,D_4,D_5,D_6)=2(b_*,d_2,d_3,d_4,d_5,d_6),
\qquad B+D_2+\cdots+D_6=1.
\]

The cleared polynomial has 530 terms, simplex degree at most eight,
and degree at most two in each of `k,l`. Homogenize it to simplex
degree eight by multiplying each monomial by the required power of
`B+D2+...+D6`. Then expand in the degree-two Bernstein bases of
`k` and `l`. The checker evaluates all **10,148 nonzero coefficients**
in the nine resulting homogeneous polynomials, using exact rational
arithmetic. Every coefficient is positive; every one of the nine
polynomials contains `B^8` with coefficient exactly one.

The Bernstein basis functions are nonnegative on `[0,1]` and sum to
one. Thus the nine coefficient checks prove (6). The checker verifies
the power-to-Bernstein conversion identities separately and generates
every simplex coefficient by the exact multinomial formula. No
floating-point approximation, sampling, or optimizer enters this
certificate.

## 5. Continuity fixes the angle branch

Any three angles in `[0,pi]` whose sum is `pi` have
`x²+y²+z²+2xyz=1` for their cosines. Equation (6) therefore forbids
`etaS+theta+etaW=pi`.

Keep `d2,d6,u,v` fixed and multiply `d3,d4,d5` by a parameter
`t` decreasing from one to zero. Add the freed deficit to `b_*`.
This path preserves the deficit simplex, all strict positive norm
bounds, and every cosine-range argument in Section 3. The three
angles are continuous along the entire path. At `t=0`, their cosines
are all one, so their sum is zero. Equation (6) prevents the sum from
crossing `pi`, proving (4). The parameter `t` here is only a path
parameter, not the inverse height used in the asymptotic chart.

## 6. The orientation contradiction

Suppose both actual mixed brackets in (1) are nonpositive. By (3),
`cross(e,S')>=0` and `cross(W',f)>=0`. Consequently there is a
clockwise turn from `-e` to `S'` of size `etaS`, and a clockwise
turn from `W'` to `-f` of size `etaW`.

Moreover

\[
\operatorname{cross}(S',W')=-(1-kl)
\operatorname{cross}(Q_4,Q_5)\le0,
\]

so the intermediate turn from `S'` to `W'` is clockwise of size
`theta`. The total clockwise path from `-e` to `-f` has length
less than `pi` by (4). This is impossible: their counterclockwise
angle is `gamma` in `(0,pi)`, so their clockwise angle is
`2pi-gamma>pi`.

All zero cross products are retained. An antiparallel pair would
contribute an angle `pi` and is already ruled out by (4); a parallel
pair contributes zero. Thus (1) holds throughout the whole stated
closed height order. Combined with the independently checked
topological height-order implications, this excludes that region.

## Reproduction

```sh
python research/type7_completion/remaining_c0_height_order.py
```

The C0 cap/orientation and strict-turn source certificates, plus the
[topological companion's two conditional CNFs](exhaustive_c0_height_order.md),
must also be independently replayed. The exact metric and polynomial
checker took 1.705 seconds in this shared workspace. This theorem is a research exclusion of
one entire regular C0 height-order region. It is not a finite-height
mask exclusion and has not yet been assembled in Lean.
