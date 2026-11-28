# Common-line reductions for the double-zero C1 orbits

For interior ray-2 C1, all transverse points lie on one common line
through zero in either of these situations:

* EF: `h2=h7=0`;
* EE at either endpoint: `h2=h6=0` and `h0=0` or `h0=1/2`.

The EF conclusion uses the preceding
[nonparallel-cap exclusion](remaining_c1_opposite_zero.md). Six further
strict-minor CNFs prove the reductions below. The resulting scalar
families are recorded explicitly and are not claimed to be excluded.

## 1. Parallel-cap EF

Put `U=P4-P3`, `V=P6`, and `W=alpha P3`. The
[closed C1 circle identities](solver_remaining_c1_geometry.md) and
the ray-2 budget give

\[
|U|=|V|=|W|=\tfrac12,\qquad
h_0=h_1=h_3=h_6=\tfrac12,\qquad h_4+h_5=\tfrac12,
\]

and the coordinates

\[
P_2=P_3=W/\alpha,\quad P_4=P_3+U,\quad P_6=V,
\quad P_0=P_1=P_7=0,
\quad P_5=\beta P_3+(1-\beta)V+2h_5U.              \tag{1}
\]

The preceding theorem makes U,V parallel, so `V=U` or `V=-U`.
The lower dot identity is
`(beta-2h5)(U dot V+1/4)=0`. Thus `V=U` forces `h5=beta/2`,
while `V=-U` leaves `0<=h5<=1/2` free.

Suppose W is independent of U. Choose the ambient orientation
and a positive-determinant transverse linear change of coordinates
so that `U=(1,0)` and `W=(xi,1)`. Formula (1) is preserved. All
original limiting determinants are independent of xi, and their
nonzero signs have the following finite certificate cover:

| Case | Strict minors retained | Variable-sign minors omitted |
|---|---:|---:|
| `V=U, h5=beta/2` | 24 | 0 |
| `V=-U, h5=0` | 23 | 0 |
| `V=-U, 0<h5<1/2` | 20 | 5 |
| `V=-U, h5=1/2` | 23 | 0 |

Every corresponding generic formula is UNSAT. Hence W is parallel
to U; (1) puts every transverse vertex on that common line.

## 2. The two EE endpoints

When `h2=h6=0`, nearest lifts and the total weight give

\[
h_1=h_3=h_5=h_7=\tfrac12,\qquad
h_0=r,\quad h_4=\tfrac12-r,\qquad 0\le r\le\tfrac12.
\]

Here `P2=P3`, `P6=P7=V`, and `|U|=|V|=1/2`, where
`U=P4-P3`. Write `W=alpha P3`. The two circle calculations give

\[
\begin{aligned}
|W|&=\alpha/2+(1-\alpha)r,
&W\cdot(2V)&=\alpha/2-(1+\alpha)r,\\
|R_5|&=\beta r+(1-\beta)/2,
&R_5\cdot(2U)&=2r-|R_5|.
\end{aligned}                                                     \tag{2}
\]

The squared perpendicular components are respectively
`4 alpha r(1/2-r)` and `4(1-beta)r(1/2-r)`. The companion checks
both identities and all four endpoint Cauchy equalities. They give:

| Endpoint | `P3` | `R5` | `P5` |
|---|---|---|---|
| `r=0` | `V` | `-(1-beta)U` | `V-(1-beta)U` |
| `r=1/2` | `-V/alpha` | `U` | `beta P3+(1-beta)V+U` |

If U,V are independent, orient and transform them to
`U=(1,0), V=(xi,1)`. Each endpoint has 33 uniform strict original
minor signs, independent of xi. Each produces an UNSAT generic
formula. Thus U,V are parallel at both endpoints, and the displayed
coordinates give the common-line conclusion.

## 3. The remaining exact scalar families

For EF orient the line so that `U=1/2`. There are two signs
`eta,epsilon in {−1,+1}` with `W=eta/2`, `V=epsilon/2`. Put `r=h5`.
Then

\[
\begin{aligned}
h&=(\tfrac12,\tfrac12,0,\tfrac12,\tfrac12-r,r,\tfrac12,0),\\
P_0=P_1=P_7&=0,\quad P_2=P_3=\eta/(2\alpha),\quad
P_4=P_3+\tfrac12,\\
P_6&=\epsilon/2,\qquad
P_5=\beta P_3+(1-\beta)\epsilon/2+r.
\end{aligned}
\]

For `epsilon=+1`, `r=beta/2`; for `epsilon=-1`, the entire closed
interval `0<=r<=1/2` is retained.

For either EE endpoint orient `V=1/2` and write `U=epsilon/2`.
Its weight vector is

\[
h=(r,\tfrac12,0,\tfrac12,\tfrac12-r,\tfrac12,0,\tfrac12),
\qquad r\in\{0,\tfrac12\}.
\]

Use the coordinate formulas in the endpoint table, with
`P0=P1=0`, `P2=P3`, `P4=P3+epsilon/2`, and `P6=P7=1/2`.

The companion reconstructs all eight scalar families—four EF and
four EE endpoint choices—and checks all twelve closed projected
stresses from the original 29-row system for each. All zero weights
and closed parameter endpoints are retained. These checks certify
the stated necessary families; they do not establish that the
families arise from embedded finite realizations.

## 4. Boolean source and replay

Each CNF retains the full necessary generic embedding/linking source,
removing only its freely chosen ambient-orientation unit. Every
strict original minor is expanded directly from the displayed
coordinates and multiplied by positive alpha. Its factors receive
exact uniform signs by multilinear corner interpolation on the
open parameter box. If a factor changes sign, that entire minor
is omitted. Original zero minors impose no generic sign.

```sh
python research/type7_completion/remaining_c1_zero_common.py /tmp/type7-c1-zero-common
python research/type7_completion/solver_cnf_certificates.py /tmp/type7-c1-zero-common-rup --checker /path/to/solver-check-rup-watched /tmp/type7-c1-zero-common
```

All six CNFs require independent replay. No rate comparison is
used. The interior EE range `0<h0<1/2`, the EB/ED orbits, the
remaining scalar common-line families, and all height endpoints
remain outside this package's exclusion claims.
