# Nonedge control of the remaining C0 vector pair

This package checks two necessary metric inequalities on the remaining
regular C0 height region `0<u<v<1/2`. It does **not** exclude that
region. It controls the same vectors whose orientations are supplied
by [the quantitative topological bounds](exhaustive_c0_height_order.md).
The two inequalities are also consequences of the existing circle
identities; these particular nonedge lifts do not strengthen the closed
metric system.

Write `d_i=1/2-h_i`, with `sum(d_i)=1/2`, and put

\[
\begin{gathered}
k=v-u>0,\quad l_u=1-2u>0,\quad l_v=1-2v>0,\\
L=d_1+d_2,\quad M=d_6+d_7,\quad
D=\tfrac12-d_3-d_4-d_5,\\
r=h_3-l_uD,\quad s=h_5-2vD,\quad
R_S=l_vr+l_us,\quad R_W=vr+us,\\
\Sigma=R_S+2kL,\qquad \mathcal T=R_W+kM,\\
S_0=l_vP_4-l_uP_5,\qquad W_0=vP_4-uP_5,\\
E=P_3-P_2,\qquad F=P_7-P_6.
\end{gathered}
\]

The new norm bounds and exact dot formulas are

\[
\begin{aligned}
|S_0|^2&\le\Sigma^2-2l_ul_vd_4,\\
|W_0|^2&\le\mathcal T^2-2uvd_4,\\
E\cdot S_0&=h_2\Sigma-l_v(h_2-d_3)-2kd_1,\\
F\cdot W_0&=h_6\mathcal T-u(h_6-d_5)-kd_7.
\end{aligned}
\tag{1}
\]

Together with the topology package, these vectors also satisfy

\[
\operatorname{cross}(E,S_0)\ge0,\qquad
\operatorname{cross}(W_0,F)\ge0.
\tag{2}
\]

The first two statements in (1) are separate upper bounds. They do not
specify `S0·W0` and must not be replaced by a joint Gram identity.

## 1. Two explicit lattice lifts

The metric realization is distance contracting from the flat torus:
the chord between two image vertices is at most the length of any
chosen intrinsic lift between them. Use lift `(1,-1)` for the missing
edge 04 and `(-1,1)` for the missing edge 15. Their horizontal
displacements are

\[
X_{04}=\tfrac32-(h_0+h_1+h_2+h_3),\qquad
X_{15}=2-(h_1+h_2+h_3+h_4).
\]

The companion reconstructs these displacements directly from the
marked cyclic cocycle. Set

\[
T_{04}=|P_4|^2-X_{04}^2,\qquad
T_{15}=|P_5|^2-X_{15}^2,
\]

and use the existing `Tij=|Pj-Pi|²-Xij²` on every edge.

The nonedge vertical products remain bounded in the compact axis chart.
To see their limits explicitly, use the generic variables

\[
a=v_1-v_3,\quad c=v_3-v_4,\quad d=v_3-v_5-1,\quad f=2v_3-1.
\]

The existing products are `P05=f(2d+1)` and `P14=-4ac`, while the
two nonedge products factor as

\[
P_{04}=f(2c+1),\qquad P_{15}=-4ad.
\]

At an interior C0 point, `2d+1=2v>0` and `c=-(1-2u)/2<0`.
Consequently, after division by the inverse-height parameter and
passage to the limit,

\[
q_{04}=(u/v)q_{05},\qquad q_{15}=(l_v/l_u)q_{14}.
\]

These relations retain the existing product scales. The bounded axial
corrections add `2u H4` and `-lv(H5-H1)`, respectively. The resulting
necessary nonedge inequalities are

\[
T_{04}+(u/v)q_{05}+2uH_4\le0,
\qquad
T_{15}+(l_v/l_u)q_{14}-l_v(H_5-H_1)\le0.
\]

## 2. Exact elimination and positive factors

Three edge equations eliminate each displayed auxiliary expression.
The companion checks the full 14 auxiliary coefficients directly
against the original 29-row system. Define

\[
\begin{aligned}
R_{04}&=T_{04}-(u/v)T_{05}+(2u/l_u)T_{34}-(2u/l_v)T_{35},\\
R_{15}&=T_{15}-(l_v/l_u)(T_{14}-T_{34})-T_{35}.
\end{aligned}
\]

Then `R04<=0` and `R15<=0`. Modulo the exact closed C0 stress rows
`U=V=J=0`, direct expansion gives

\[
\begin{aligned}
2kl_uR_{15}
 &=|S_0|^2-(\Sigma^2-2l_ul_vd_4),\\
kvR_{04}
 &=|W_0|^2-(\mathcal T^2-2uvd_4).
\end{aligned}
\]

Both multipliers are strictly positive on the stated height region,
proving the norm inequalities in (1). The checker verifies the exact
polynomial remainders before setting `U,V,J` to zero. It also binds
the `C,K` stress rows and the four cap metric rows used to obtain the
two dot identities. The source syzygies required by `C` and `K` are
included explicitly.

For later estimates the time scalars admit the positive representation

\[
\begin{aligned}
\widehat r&=d_4+d_5+M+2ud_0>0,\\
\widehat s&=L+d_3+d_4+l_vd_0>0,\\
\Sigma&=l_v\widehat r+l_u\widehat s,\qquad
\mathcal T=v\widehat r+u\widehat s.
\end{aligned}
\]

The strict positivity follows from regular endpoint caps, which give
`L,M>0`. This representation is a scalar identity and does not assert
that `P4,P5` lie on corresponding circles.

## 3. Relation to the existing circle bounds

With the earlier vectors `S=lv*Q4-lu*Q5` and
`W=v*Q4-u*Q5`, one has

\[
S_0=S-2kP_3,\qquad W_0=W+kP_6,
\]

and

\[
|S|^2=R_S^2-2l_ul_vd_4,\quad |W|^2=R_W^2-2uvd_4,
\qquad |P_3|=L,\quad |P_6|=M.
\]

Here `RS,RW>0`. Cauchy--Schwarz and `|S|<=RS`, `|W|<=RW`
give

\[
\begin{aligned}
|S_0|^2&\le |S|^2+4kL R_S+4k^2L^2
 =\Sigma^2-2l_ul_vd_4,\\
|W_0|^2&\le |W|^2+2kM R_W+k^2M^2
 =\mathcal T^2-2uvd_4.
\end{aligned}
\]

Thus the explicit nonedge calculation provides an independent source
check and useful vector formulas, but these norm bounds alone cannot
remove any additional point of the limiting metric locus.

## Reproduction and scope

```sh
python research/type7_completion/exhaustive_c0_nonedge_vectors.py
```

The replay checks the selected lattice lifts, four generic product
identities, two exact nonedge auxiliary combinations, nine metric
source bindings, and the norm and dot consequences. All arithmetic
is exact. The package supplies necessary inequalities for the remaining
height order; no metric or embedding exclusion is claimed.
