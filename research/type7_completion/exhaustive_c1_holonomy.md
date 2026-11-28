# A closed turning constraint for regular C1

Every regular C1 limit satisfies the two strict disjunctions

\[
\boxed{U<0\ \text{or}\ V>0},\qquad
\boxed{V<0\ \text{or}\ W<0},                         \tag{1}
\]

where

\[
\begin{aligned}
E_2&=P_2-P_3,&E_3&=P_4-P_3,&F&=P_7-P_6,\\
Y_0&=\alpha P_2,&Y_5&=\beta P_4+(1-\beta)P_6-P_5,\\
U&=\operatorname{cross}(P_2,E_3),&
V&=\operatorname{cross}(P_2,Y_5),&
W&=\operatorname{cross}(P_2,F).
\end{aligned}
\]

Here both projected caps 234 and 067 are noncollinear and
`0<alpha,beta<1`. The result is independent of the marking and of the
metric equations. It follows from the full generic-completion topology
cover, interpreted as **weak signs of the actual limiting minors**.
Thus (1) includes all cases in which one or more of `U,V,W` vanish.

With the closed C1 metric identities, (1) implies that the six natural
angles have total signed turn zero. It excludes their additional
`2*pi` turn, but does **not** exclude regular ray-2 C1.

## 1. A positive projective normalization

The spatial levels are

\[
(0,\alpha/2,1/2,1/2,1/2,\beta/2,0,0),\qquad P_0=P_1=0.
\]

For `0<alpha<1`, apply the projective map

\[
(P,z)\longmapsto
\left(\frac{P}{D(z)},\frac{(1-\alpha)z}{D(z)}\right),
\qquad D(z)=\alpha+(2-4\alpha)z.
\]

The denominator is positive on `[0,1/2]`: its endpoint values are
`alpha` and `1-alpha`. The homogeneous transformation has determinant
`alpha*(1-alpha)>0`, so every four-point minor retains its sign.
The new levels of vertices 0, 1, and 2 are respectively `0,1/4,1/2`.
The new parameter at vertex 5 is

\[
\widetilde\beta=
\frac{\beta(1-\alpha)}{\alpha+(1-2\alpha)\beta}\in(0,1).
\]

Both cap areas remain strictly positive after multiplying by positive
factors. Also

\[
\widetilde E_3=\frac{E_3}{1-\alpha},\qquad
\widetilde F=\frac F\alpha,\qquad
\widetilde P_2=\frac{P_2}{1-\alpha},\qquad
\widetilde Y_5=\frac{Y_5}{D(\beta/2)}.
\]

Consequently the signs of `U,V,W` are unchanged. The algebraic
certificate may therefore set `alpha=1/2`. In the next section `beta`
denotes the transformed parameter; no metric equation is transformed.

## 2. The exact polynomial certificates

Write `Cij=cross(Pi,Pj)` for `2<=i<j<=7`. There are fifteen such
coordinates. At the normalized levels, four times each of the seventy
spatial minors is a linear combination of the `Cij`, with coefficients
affine in `beta`. The checker derives these rows from the determinant
formula and independently verifies them in twelve planar coordinates.

Let

\[
A_u=C_{23}-C_{24}+C_{34},\qquad A_l=C_{67}.
\]

The three cap-orientation CNFs force the actual regular cap areas to
satisfy `Au>0` and `Al>0`. The fourth CNF proves that the 132 listed
primary words cover every generic completion with these cap signs.

For every listed word and each of the two additional **closed** branches

\[
\text{branch 0: }U\ge0,\ -V\ge0,
\qquad
\text{branch 1: }V\ge0,\ W\ge0,                       \tag{2}
\]

the frozen data provide an identity

\[
-\beta(1-\beta)A_uA_l
=\sum_j a_j Q_j+\sum_k b_k R_k,\qquad a_j\ge0.        \tag{3}
\]

Each `Qj` is one of the following nonnegative polynomials on that branch:

- A product of two signed weak minor rows, or of such rows with the
  additional weak forms in (2).
- A product of two signed anchor coordinates, multiplied by one of
  `1`, `beta`, `1-beta`, `beta^2`, `beta*(1-beta)`, `(1-beta)^2`.

Each `Rk` is a planar Plücker identity

\[
C_{ij}C_{kl}-C_{ik}C_{jl}+C_{il}C_{jk}=0,
\]

possibly multiplied by `beta` or `beta^2`. Its coefficient `bk` may have
either sign. Primitive normalization always divides by a positive
integer gcd. The left side of (3) is strictly negative, whereas the
right side is nonnegative. Thus both closed branches are impossible,
which proves (1).

Only **32 certificates and 2,687 sparse rational terms** are needed for
the 264 word/branch pairs. A certificate is reused only when every
signed product appearing in it retains its sign. The checker derives
these parity conditions from the terms themselves and checks that
every one of the 264 pairs is covered. It then adds the blocking clause
for every listed primary word to the original source formula; the
resulting UNSAT certificate binds this finite list to the full topology
source. No sampled geometry, LP status, or numerical coefficient enters
replay.

## 3. The two linked vectors are nonzero

The angular corollary uses the
[closed C1 circle identities](solver_remaining_c1_geometry.md), the
nearest-lift bounds `hi+h(i+1)>=1/2`, and the regular cap triangles.
Write `di=1/2-hi`. For either linked vector, its norm has the form

\[
\begin{aligned}
\sigma&=\tfrac12+(1-t)p-tq,\\
n^2&=\sigma^2-2(1-t)p,\qquad p,q\ge0,\quad p+q\le\tfrac12.
\end{aligned}
\]

The exact identity

\[
\begin{split}
n^2-(\tfrac12-p-q)^2
={}&[tp+(1-t)q](1-2p-2q)\\
&+[tp-(1-t)q]^2\ge0                              \tag{4}
\end{split}
\]

shows that `n=0` requires
`p=(1-t)/2`, `q=t/2`, and `sigma=1-t>0`.
For `Y0`, take `(p,q,t)=(d0,d1,alpha)`. Its dot identity would then give
`h7=1/2`. For `Y5`, take `(p,q,t)=(d5,d4,beta)`; its dot identity would
give `h6=1/2`. Either equality makes the perimeter-one lower cap
degenerate. Hence both vectors are nonzero. This argument includes
zero individual deficits and the endpoint `p+q=1/2`.

## 4. The total signed turn is zero

The positive cap orientations and four unanimous weak minor signs give
the following angles:

| Angle | Oriented pair | Range |
|---|---|---|
| `A` | clockwise from `E2` to `E3` | `(0,pi)` |
| `B` | counterclockwise from `P7` to `F` | `(0,pi)` |
| `psi` | counterclockwise from `E2` to `Y0` | `[0,pi]` |
| `theta` | clockwise from `Y0` to `P7` | `[0,pi]` |
| `psi5` | clockwise from `E3` to `Y5` | `[0,pi]` |
| `theta5` | counterclockwise from `Y5` to `F` | `[0,pi]` |

The four weak signs are `[0123]>=0`, `[0127]<=0`, `[3456]<=0`, and
`[4567]<=0`. The checker verifies that they hold in every covered word.
All angle definitions are valid by Section 3 and regularity of the caps.

Closing the sequence of directions shows that

\[
H=A+B+\psi-\theta+\psi_5-\theta_5\in2\pi\mathbb Z.
\]

The angle ranges give `-2*pi<H<4*pi`, so `H` is either zero or `2*pi`.
To exclude the latter without discarding parallel directions, set the
argument of `P2` to zero and choose the following real lifts:

\[
x=-\psi-A,\qquad y=x-\psi_5,\qquad z=y+\theta_5.
\]

Then `-2*pi<x<0`, `-3*pi<y<0`. If `H=2*pi`, the other lift of `F`
gives `z=-theta+B-2*pi`, hence `-3*pi<z<-pi`.
The signs of `U,V,W` are the signs of `sin(x),sin(y),sin(z)`.

If `V<=0`, the condition `z>=y` forces `y<=-2*pi`. Since
`x<=y+pi`, it follows that `-2*pi<x<=-pi`, so `U>=0`, contradicting
the first disjunction in (1).
If `V>=0`, then `-2*pi<=y<=-pi`; consequently
`-2*pi<=z<-pi` and `W>=0`, contradicting the second disjunction.
The two cases overlap when `V=0`, so the argument includes every zero
cross-product case. Therefore

\[
\boxed{A+B+\psi-\theta+\psi_5-\theta_5=0.}             \tag{5}
\]

## 5. Scope and retained diagnostics

Equation (5) is a necessary constraint. It does not yet contradict the
ray-2 weight budget. The separate
`exhaustive_c1_holonomy_diagnostics.json` retains two floating-point
metric examples to document failed relaxations:

| Diagnostic | Total turn | Anchor mismatches | Full-word mismatches |
|---|---:|---:|---:|
| Metric identities and four common signs | `0` | 2 | 18 |
| Metric identities and one complete anchor pattern | `0` | 0 | 9 |

Both have `sum(hi)=5/2`, regular caps, positive normalized face areas,
and positive checked nearest-lift/active-nonedge margins. Their
auxiliary reconstruction residuals were below `4e-15`. They are
numerical diagnostics, not proof certificates or actual realizations
of the full topology system. The second example fails height-sensitive
minors around vertex 5, including `[2356]` and `[2456]`. Thus neither
the four common signs nor the fourteen anchor patterns together with
zero total turn settle regular ray-2 C1. The full seventy-minor
constraints remain necessary.

## 6. Reproduction

```sh
python research/type7_completion/exhaustive_c1_holonomy.py /tmp/type7-c1-holonomy
python research/type7_completion/solver_cnf_certificates.py /tmp/type7-c1-holonomy-rup \
  --checker /path/to/solver-check-rup /tmp/type7-c1-holonomy
```

The exact algebraic replay took **1.06 seconds** in this workspace.
All four source CNFs then passed independent RUP replay in **0.60
seconds**, with four distinct proof hashes. The checker does not import
NumPy, SciPy, or an optimizer. The diagnostic JSON is not read by the
proof checker.
