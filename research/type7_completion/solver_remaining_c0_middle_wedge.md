# The two-sided middle wedge in regular C0

This excludes sixteen of the forty-two regular ray-1 C0 completions left by
[the opposite-cone proof](solver_remaining_c0_opposite_cones.md), for the
entire height region `0<u<v<1/2`. It retains every actual zero bracket.
The companion checks the metric source, all new identities, and two finite
completeness obligations. The latter require independent RUP replay.

Use the existing notation

\[
\begin{gathered}
\ell_u=1-2u,\quad\ell_v=1-2v,\quad K=v-u>0,\qquad
h_i=\tfrac12-d_i,\quad\sum_i d_i=\tfrac12,\\
D=d_0+d_1+d_2+d_6+d_7,\quad
E=P_3-P_2,\quad F=P_7-P_6,\\
Q_4=P_4-2uP_3-\ell_uP_6,\quad
Q_5=P_5-2vP_3-\ell_vP_6,\\
r=|Q_4|=h_3-\ell_uD>0,\quad
s=|Q_5|=h_5-2vD>0,\\
S=\ell_vQ_4-\ell_uQ_5,\qquad W=vQ_4-uQ_5.
\end{gathered}
\]

Regular endpoint caps give `d1,d2,d6,d7>0`, and the previously proved
strict turning inequality gives `cross(E,F)>0`. The remaining source has
generic `2345−,3456−,4567−`. Thus the actual weak consequences are

\[
E\times S\ge0,\qquad Q_4\times Q_5\ge0,\qquad W\times F\ge0.
\tag{1}
\]

## 1. The two additional signs give a common wedge

Suppose the generic completion also has `2356−,3467−`. The exact raw
determinant identities are

\[
2[2356]=-E\times Q_5,\qquad2[3467]=Q_4\times F.
\]

Consequently `E×Q5>=0` and `F×Q4>=0`. The first and last inequalities in
(1), whose coefficients are positive, then imply

\[
E\times Q_4\ge0,\quad E\times Q_5\ge0,\quad
F\times Q_4\ge0,\quad F\times Q_5\ge0.
\tag{2}
\]

Write the direction of `E` as angle zero and that of `F` as
`gamma`, where `0<gamma<pi`. Each nonzero `Qj` lies in the closed
angular interval `[gamma,pi]`. Its width is strictly less than `pi`.
The middle inequality in (1) therefore orders their directions as

\[
\gamma\le\theta_4\le\theta_5\le\pi.
\tag{3}
\]

This argument includes parallel `Q4,Q5`. An antipodal pair cannot lie
in this wedge. No actual determinant is assumed strict beyond the
already proved `E×F>0`.

## 2. A zero-safe half-angle comparison

For `0<=x<=y<pi`, the function `tan(t/2)` is nonnegative and increasing.
Thus, for positive `A,B`,

\[
A\sin x\le B\sin y
\quad\Longrightarrow\quad
A(1-\cos x)\le B(1-\cos y).
\tag{4}
\]

The reversed inequalities hold when `x>=y`. Zero angles are allowed.
There is no division by a sine. Equivalently, one may use the finite
coordinate `t=tan(x/2)`, with

\[
(\cos x,\sin x)=\frac{(1-t^2,2t)}{1+t^2},\qquad
1-\cos x=t\sin x.
\]

For two such coordinates the cross product is
`2(t2−t1)(1+t1*t2)/((1+t1²)(1+t2²))`, so the same argument is algebraic.
The companion verifies these identities exactly.

Apply the reversed comparison to
`x=pi−theta4`, `y=pi−theta5`, `A=lv*r`, `B=lu*s`.
Both angles are less than `pi` by (3). The hypothesis is exactly
`E×S>=0`. With `e=E/h2`, this gives

\[
\ell_v(r+e\cdot Q_4)-\ell_u(s+e\cdot Q_5)\ge0.
\tag{5}
\]

Next use `x=theta4−gamma`, `y=theta5−gamma`, `A=v*r`, `B=u*s`.
Again both angles are less than `pi`; the hypothesis is `W×F>=0`.
With `f=F/h6`,

\[
v(r-f\cdot Q_4)-u(s-f\cdot Q_5)\le0.
\tag{6}
\]

## 3. The metric converts both comparisons into incompatible bounds

The exact C0 dot identities, already bound to the complete twenty-nine
source rows, are

\[
\begin{aligned}
E\cdot S&=h_2(\ell_vr+\ell_us)-\ell_v(h_2-d_3),\\
F\cdot W&=h_6(vr+us)-u(h_6-d_5).
\end{aligned}
\]

Substitution into (5) and (6) gives respectively

\[
\begin{aligned}
\ell_v(r+e\cdot Q_4)-\ell_u(s+e\cdot Q_5)
 &=2\ell_v\left(\frac{d_3d_2}{h_2}-\ell_uD\right),\\
v(r-f\cdot Q_4)-u(s-f\cdot Q_5)
 &=2u\left(2vD-\frac{d_5d_6}{h_6}\right).
\end{aligned}
\]

All divided factors are positive. Hence

\[
\ell_uD\le\frac{d_3d_2}{h_2},\qquad
2vD\le\frac{d_5d_6}{h_6}.
\tag{7}
\]

Their left sides sum to `(1+2K)D>D`. Their right sides sum to less
than `D`. For a denominator-free verification, put

\[
R_2=h_2-d_3-d_5=d_0+d_1+d_4+d_6+d_7>0,
\quad
R_6=h_6-d_3-d_5=d_0+d_1+d_2+d_4+d_7>0.
\]

Then

\[
\Delta=h_2h_6-d_3h_6-d_5h_2=d_3R_2+d_5R_6+R_2R_6>0.
\]

The two nonnegative expressions required by (7) satisfy

\[
\begin{aligned}
&h_6(d_3d_2-\ell_uDh_2)+h_2(d_5d_6-2vDh_6)\\
&\quad=-D\Delta-d_3(D-d_2)h_6-d_5(D-d_6)h_2-2KDh_2h_6<0.
\end{aligned}
\]

Here `D-d2=d0+d1+d6+d7>0` and `D-d6=d0+d1+d2+d7>0`.
This is the contradiction. It also handles `d3=0`, `d5=0`, and every
zero-angle or parallel-vector case within the wedge.

## 4. Finite coverage and remaining scope

Fresh enumeration of the exact previous forty-two-word source finds sixteen
words with both additional generic signs negative. The analytic argument
excludes them, giving the necessary generic clause `2356+ or3467+`.
The other twenty-six words are enumerated explicitly.

Two CNFs bind these lists to their complete sources: one blocks all sixteen
words under the two negative antecedents; the other blocks all twenty-six
words after adding the proved metric clause. Both require independent RUP
replay. The code never replaces a generic sign by an actual strict sign.

```sh
python research/type7_completion/solver_remaining_c0_middle_wedge.py OUTPUT
```

This is a uniform exclusion of these sixteen regular C0 completions.
It does not claim to exclude the remaining twenty-six, degenerate endpoint
caps, or finite-height Type 7 in its entirety.
