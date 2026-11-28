# Excluding the remaining nonparallel double coincidence

There is no unbounded embedded ray-1 sequence with an interior C0 limit
satisfying
\[
P_1=P_3=0,\qquad P_0=P_6=0,\qquad C_{27}<0.
\]
The [positive-core companion](exhaustive_c0_double_coincidence.md)
excludes the other nonparallel orientation. Together these results
close every nonparallel double coincidence. The remaining nonparallel
both-flat order pairs are bd and da, which are exchanged by the
checked marked reflection.

One independently replayable CNF reduces the present case to four
alternatives. Two strict circle identities, elementary half-angle
comparisons, and an exact divided cap tilt exclude them. The proof
works for every \(0<u,v<1/2\), without ordering \(u,v\) or comparing
any collapse rates.

## 1. Strict circle identities at the double coincidence

Let \(d_i=1/2-h_i\). The two coincidences give
\[
d_1=d_2=d_6=d_7=0,\qquad
D=d_0,\quad p=d_3,\quad q=d_4,\quad g=d_5,\qquad
D+p+q+g=1/2.
\]
Write
\[
P_2=-e/2,\qquad P_7=f/2,\qquad |e|=|f|=1.
\]
The core identity gives
\[
D=(1-e\cdot f)/4.
\]
Since \(C_{27}<0\), the counterclockwise angle from \(e\) to \(f\)
is a number \(\theta\in(0,\pi)\). In particular,
\[
0<D<1/2,\qquad h_0=1/2-D>0.
\]

Set
\[
\ell_u=1-2u,\quad \ell_v=1-2v,\qquad
r=h_3-\ell_uD,\quad s=h_5-2vD.
\]
The closed C0 circle identities become
\[
|P_4|=r=q+g+2uD>0,\qquad
|P_5|=s=p+q+\ell_vD>0.                    \tag{1}
\]
For
\[
S=\ell_vP_4-\ell_uP_5,\qquad W=vP_4-uP_5,
\]
their dot equations give the two strictly positive differences
\[
\begin{aligned}
\ell_u(s+e\cdot P_5)-\ell_v(r+e\cdot P_4)
  &=2\ell_u\ell_vD>0,\\
v(r-f\cdot P_4)-u(s-f\cdot P_5)
  &=4uvD>0.                               \tag{2}
\end{aligned}
\]
The companion replays the full source bindings of the circle and core
identities, then checks these specializations algebraically. No
product scale or axial correction is set to zero prematurely.

The relevant actual determinant formulas are
\[
[2345]=-\tfrac14 e\times S,\qquad
[4567]=-\tfrac12 W\times f.                 \tag{3}
\]

## 2. Independently normalizing both shrinking diagonals

For each finite configuration put
\[
L=d_1+d_2=X_{13}>0,\qquad
M=d_6+d_7=-X_{06}>0,\qquad t=1/y^2.
\]
The positive-core companion proves, directly from the finite edge
equations,
\[
|P_3|/L\longrightarrow1,\qquad
\zeta_3-\zeta_1=O(tL).
\]
The same conclusion for 06 follows from the explicit identities below.

Write \(\ell=\zeta_1\), \(b=v_1\), and define
\[
a=\zeta_6/t,\qquad g_6=v_6/t.
\]
Here \(v_6\) is the actual intrinsic lift, including the bounded
axis-chart correction. The triangles 016 and 056 have zero cocycle
period. Their exact metric polarizations give
\[
\begin{aligned}
\ell^2&=b^2+th_0^2,\\
\ell a&=bg_6+h_0M,\\
\ell^2|P_6|^2&=(bM-th_0g_6)^2,\\
P_6\cdot P_5+a\zeta_5&=-MX_{05}+g_6v_5.
\end{aligned}                              \tag{4}
\]
After substituting the second equation into the fourth, the
coefficient of \(g_6\) is
\[
b\zeta_5/\ell-v_5\longrightarrow2v>0.
\]
Uniform boundedness of the other coefficients therefore gives
\[
|g_6|\le C(M+|P_6|).
\]
The third equation of (4) gives
\[
|P_6|\le C_1M+C_2t|g_6|.
\]
Absorbing the last term proves
\[
g_6=O(M),\qquad a=O(M),\qquad |P_6|/M\longrightarrow1. \tag{5}
\]

After taking a subsequence, let
\[
w=\lim P_3/L,\qquad z=\lim P_6/M.
\]
Both are unit transverse vectors. Their relative axial components
tend to zero by the preceding estimates. There is no comparison
between \(L\), \(M\), or \(t\).

## 3. A complete zero-safe four-cell cover

The Boolean source retains the full necessary generic topology and
linking formula, both strict height cuts, actual trits, affine
cocycles, weak Grassmann–Pluecker relations, all 49 uniform C0 height
identities, and the exact macro coincidences.

It additionally retains the two independent virtual directions \(w,z\).
Their cross products with the independent pair \(P_2,P_7\) cannot
both vanish. The six projected vectors
\[
P_2,\ P_4,\ P_5,\ P_7,\ w,\ z
\]
obey all rank-two three-term relations.

There are 29 four-point brackets containing pair 13 or pair 06.
Divide each by its positive diagonal length, and divide \([0136]\)
by \(LM\). The exact relative axial bounds justify all these limits.
The doubly divided bracket factors exactly through the two short
vectors; it does not introduce an error depending on \(L/M\).
The companion checks every polynomial factor and all coefficient
signs on the open height square.

A nonzero divided bracket fixes the finite generic sign. A zero
leaves that sign unrestricted. The metric nonzero radii in (1) are
included only through the necessary rank clauses saying that each
of \(P_4,P_5\) has a nonzero cross product with at least one of
\(P_2,P_7\).

The independently replayable CNF proves that at least one row of the
following table holds. All displayed \(C_{ij}\) are actual limiting
cross products; only the explicitly marked \(\chi\) is a generic
completion sign.

| Cell | Necessary signs |
|---|---|
| P | \(C_{47}=0,\ C_{24}\le0\) |
| F | \(C_{24},C_{25}\le0;\ C_{47},C_{57}\ge0;\ C_{45}\le0;\ [4567]\ge0\) |
| E | \(C_{24},C_{25},C_{47},C_{57}\ge0;\ C_{45}\le0;\ [2345],[4567]\ge0\) |
| T | \(C_{25}<0,\ P_2\times w=0,\ P_7\times w<0,\ \chi_{1235}=+1\) |

The cover preserves every zero sign. Its source and conclusion do not
depend on a strict height order.

## 4. Cell P: a vanishing circle defect

Since \(P_4\ne0\), \(C_{47}=0\) makes \(P_4\) parallel to \(f\).
The sign \(C_{24}\le0\) chooses the positive direction, because
\(e\times f>0\). Thus \(P_4=rf\).

Now \(r-f\cdot P_4=0\), while \(s-f\cdot P_5\ge0\) by Cauchy's
inequality. This contradicts the second strict identity in (2).

## 5. Cell F: comparison inside the cone of e and f

The first four signs place both nonzero vectors \(P_4,P_5\) in the
closed positive cone spanned by \(e,f\), whose angle is \(\theta<\pi\).
Let \(x,y\) be their clockwise angles from \(f\). Then
\[
0\le x,y\le\theta.
\]
The sign \(C_{45}\le0\) gives \(x\le y\). By (3), the last sign gives
\[
vr\sin x\le us\sin y.
\]
The function \(\tan(x/2)\) is increasing and finite on
\([0,\theta]\). Therefore
\[
\begin{aligned}
vr(1-\cos x)
&=vr\sin x\tan(x/2)\\
&\le us\sin y\tan(y/2)
 =us(1-\cos y).
\end{aligned}
\]
This contradicts the second identity in (2). The argument includes
zero angles, since no sine is divided by.

## 6. Cell E: comparison inside the cone of minus f and e

The first four signs put both vectors in the closed positive cone
spanned by \(-f,e\), of angle \(\pi-\theta<\pi\).
Write
\[
P_4=r(\cos a,-\sin a),\qquad
P_5=s(\cos b,-\sin b)
\]
in coordinates where \(e=(1,0)\). Then
\[
0\le a,b\le\pi-\theta,\qquad a\le b
\]
by \(C_{45}\le0\). The sign \([2345]\ge0\) gives
\[
\ell_us\sin b\le\ell_vr\sin a.              \tag{6}
\]

If \(a>0\), the decreasing function \(\cot(a/2)\), applied to (6),
gives
\[
\ell_us(1+\cos b)\le\ell_vr(1+\cos a),
\]
contradicting the first identity in (2).

If \(a=0\), (6) gives \(b=0\), because \(b<\pi\). Thus
\(P_4=re,\ P_5=se\). The second identity in (2) now says
\[
(vr-us)(1-e\cdot f)=4uvD>0,
\]
so \(vr-us>0\). But \([4567]\ge0\) says
\((vr-us)e\times f\le0\), a contradiction. This treats the shared
endpoint of the two angular comparisons explicitly.

## 7. Cell T: the opposite divided cap tilt

The two virtual signs choose \(w=e=-2P_2\). Use the finite quantities
from the positive-core companion:
\[
a_3=(\zeta_3-\zeta_1)/t,\quad
g_3=(v_3-v_1)/t,\quad
a_2=(\zeta_2-\zeta_1)/t,\quad
g_2=(v_2-v_1)/t.
\]
The relative bound gives finite subsequential limits
\(A=\lim a_3/L,\ G=\lim g_3/L\). The source polarizations become
\[
\begin{aligned}
A-G&=-2h_0,\\
e\cdot P_4-\tfrac12\ell_uA
  &=-h_3+\tfrac12\ell_uG,\\
a_2-g_2&=-h_0,\\
-\tfrac12e\cdot P_4-\tfrac12\ell_ua_2
  &=\tfrac12h_3+\tfrac12\ell_ug_2.
\end{aligned}
\]
Their exact linear combination gives
\[
\boxed{\tfrac12A+a_2=-h_0<0.}               \tag{7}
\]

Let \(B_n=P_{2,n}\times P_{3,n}\ge0\), using the usual generic
normalization \(\chi_{0123}=+1\). The finite identity
\[
[1235]_n
=(\zeta_{5,n}-\zeta_{1,n})B_n
+t_n(a_{2,n}C_{35,n}-a_{3,n}C_{25,n})        \tag{8}
\]
has first coefficient tending to \(v-1/2<0\). Its second coefficient,
divided by \(L_n\), tends by \(w=-2P_2\) and (7) to
\[
-(2a_2+A)C_{25}=2h_0C_{25}<0.
\]
Consequently \([1235]_n<0\) for all sufficiently far sequence terms,
contradicting \(\chi_{1235}=+1\). The two terms in (8) have the same
strictly adverse sign; no comparison of \(B_n\) and \(t_nL_n\) is needed.

## Reproduction and scope

    python research/type7_completion/exhaustive_c0_double_flat.py /tmp/c0-double-flat
    python research/type7_completion/solver_cnf_certificates.py /tmp/c0-double-flat-rup \
      --checker /tmp/type7-rup-check /tmp/c0-double-flat

The exact checker binds both relative diagonal estimates, the circle
identities, all 29 divided determinants, and the opposite divided tilt.
The four-cell cover additionally requires independent RUP replay.
The angular comparisons and finite determinant argument complete the
mathematical exclusion.

This theorem and the positive-core companion close the nonparallel dd
case. They do not exclude the common-line residual families, bd/da,
one-collinear-cap limits, or height boundaries outside their stated
scope.
