# Closing the asymmetric nonparallel flat-cap orders

There is no unbounded embedded ray-1 sequence with an interior C0
limit of nonparallel endpoint-cap order bd or da. Together with the
six-order exclusion and the two double-coincidence packets, this
closes every nonparallel both-flat interior C0 limit.

The proof keeps every \(0<u,v<1/2\), including equal heights. A
separately normalized diagonal gives a three-cell necessary sign
cover. Two strict circle identities and an exact cap tilt exclude
the cells. No collapse rates are compared.

## 1. The bd metric specialization

The order bd means that \(P_1=0\) lies strictly between \(P_2,P_3\),
while \(P_0=P_6=0\). Put
\[
L=d_1>0,\quad d_2=d_6=d_7=0,\quad
H=1/2-L=h_1>0.
\]
The positive-edge reduction in the common-line classification
already excludes \(L=1/2\) when the cap lines are nonparallel.
Choose unit vectors \(e,f\) so that
\[
P_2=-He,\qquad P_3=Le,\qquad P_7=f/2,
\qquad E=P_3-P_2=e/2,\quad F=P_7-P_6=f/2.
\]
The full source forces \(C_{27}<0\); this implication has its own
independently replayable CNF. Consequently \(e\times f>0\), with
angle \(\theta\in(0,\pi)\).

The core stress identity gives
\[
d_0=\frac H2(1-e\cdot f).
\]
Thus, for
\[
D=d_0+L,\quad p=d_3,\quad q=d_4,\quad g=d_5,
\]
we have
\[
D+p+q+g=1/2,\qquad
0<D<1/2,\qquad
1/2-D=\frac H2(1+e\cdot f)>0.                 \tag{1}
\]

Set
\[
\ell_u=1-2u,\quad\ell_v=1-2v,\qquad
Q_4=P_4-2uP_3,\quad Q_5=P_5-2vP_3.
\]
The closed C0 circle identities give
\[
\begin{aligned}
|Q_4|=r&=h_3-\ell_uD=q+g+2uD>0,\\
|Q_5|=s&=h_5-2vD=p+q+\ell_vD>0.
\end{aligned}                                \tag{2}
\]
Since \(h_2=h_6=1/2\), their two dot equations become
\[
\begin{aligned}
\ell_u(s+e\cdot Q_5)-\ell_v(r+e\cdot Q_4)
 &=2\ell_u\ell_vD>0,\\
v(r-f\cdot Q_4)-u(s-f\cdot Q_5)
 &=4uvD>0.                                    \tag{3}
\end{aligned}
\]
Write
\[
S=\ell_vQ_4-\ell_uQ_5,\qquad W=vQ_4-uQ_5.
\]
Then
\[
[2345]=-\tfrac14e\times S,\qquad
[4567]=-\tfrac12W\times f.                     \tag{4}
\]
All these equations are specializations of the full closed C0
stress system, with its auxiliary product scales retained. The
companion checks their source bindings.

## 2. The normalized lower diagonal and quotient coordinates

For every finite configuration let
\[
M=d_6+d_7=-X_{06}>0.
\]
The exact lower-diagonal estimate in the double-coincidence packet
uses only the interior C0 hypotheses, not the upper coincidence.
Its finite polarizations and absorption therefore apply here:
\[
|P_6|/M\longrightarrow1,\qquad
\zeta_6=O(tM),\qquad t=1/y^2.
\]
After a subsequence \(z=\lim P_6/M\) is a unit transverse vector.
The companion independently replays the finite identities used
for this estimate.

Use the four quotient vectors
\[
Q_2=-E=-e/2,\quad Q_4,\quad Q_5,\quad Q_7=F=f/2.
\]
The macro points can be written exactly as
\[
\begin{aligned}
P_2&=(1-2L)Q_2,& P_3&=-2LQ_2,\\
P_4&=Q_4-4uLQ_2,& P_5&=Q_5-4vLQ_2,& P_7&=Q_7.
\end{aligned}
\]
For \(i,j\in\{2,4,5,7\}\), the actual limiting determinant satisfies
\[
[36ij]=-\tfrac12(Q_i\times Q_j).               \tag{5}
\]
Thus the cross-product signs of these four vectors are existing
actual bracket trits, with the indicated orientation. Add only the
crosses with \(z\), their rank-two Grassmann--Pluecker identities,
and the necessary nonzero rank clauses. The latter are valid because
\(Q_2,Q_7\) are independent and \(Q_4,Q_5,z\) are nonzero.

The source retains all generic topology constraints, both strict
height cuts, actual trits, affine cocycles, weak Grassmann--Pluecker
relations, all 49 uniform height identities, and the bd
collinearity/coincidence relations.

The companion expands all 70 determinants in the displayed
coordinates. It adds 53 uniform macro relations and all 15
determinants containing 06 after division by \(M\). Their coefficients
are multiaffine in \(L,u,v\); checking their eight closed-cube
corners proves the required coefficient signs in the open cube.
Two extra macro relations have coefficients of sign \(v-u\) and are
omitted. No height order is assumed.

For a divided bracket, the relative bound
\(\zeta_6=O(tM)\) makes its axial error vanish after division by \(M\).
The other points merely converge; no rate comparison is required.
A nonzero divided bracket fixes the finite generic sign, while a
zero leaves the sign free.

## 3. The complete three-cell cover

Let
\[
K_{ij}=Q_i\times Q_j\qquad(i,j\in\{2,4,5,7\}).
\]
A second independently replayable CNF proves that at least one of
the following alternatives holds. Only \(\chi_{1235}\) is a generic
completion sign; every other sign is an actual limiting value.

| Cell | Necessary signs |
|---|---|
| T | \(K_{25}<0,\ \chi_{1235}=+1\) |
| F | \(K_{47},K_{57}\le0,\ K_{45}>0,\ [4567]\le0\) |
| E | \(K_{24},K_{25},K_{47},K_{57}\ge0,\ K_{45}\le0,\ [2345],[4567]\ge0\) |

The CNF negates these precise alternatives, including all their
zero boundaries. Neither this cover nor the core orientation
certificate uses a strict height order.

## 4. Cell F: the strict left-of-f turn

The two weak signs place \(Q_4,Q_5\) in the closed left half-plane
of \(f\). Let their counterclockwise angles from \(f\) be
\[
0\le a,b\le\pi.
\]
Since \(K_{45}>0\), we have \(a<b\) and \(b-a<\pi\).
By (4), the last sign gives
\[
vr\sin a\le us\sin b.                         \tag{6}
\]

If \(a=0\), the second left side in (3) is nonpositive, immediately
contradicting its strict positivity. If \(b=\pi\), (6) forces
\(\sin a=0\), and \(a<b\) again gives \(a=0\). Otherwise
\(0<a<b<\pi\), so
\[
\begin{aligned}
vr(1-\cos a)
&=vr\sin a\tan(a/2)\\
&\le us\sin b\tan(a/2)
 <us\sin b\tan(b/2)
 =us(1-\cos b).
\end{aligned}
\]
This contradicts the second identity in (3). The endpoint treatment
avoids division by a vanishing sine.

## 5. Cell E: the closed minus-f/e wedge

The four weak cross signs put \(Q_4,Q_5\) in the closed positive
cone spanned by \(-f,e\), whose angle is \(\pi-\theta<\pi\).
Write their clockwise angles from \(e\) as \(a,b\). Then
\[
0\le a\le b\le\pi-\theta
\]
by \(K_{45}\le0\). The sign \([2345]\ge0\) gives
\[
\ell_us\sin b\le\ell_vr\sin a.
\]
If \(a>0\), the decreasing half-angle cotangent gives
\[
\ell_us(1+\cos b)\le\ell_vr(1+\cos a),
\]
contradicting the first identity in (3).

If \(a=0\), the sine inequality forces \(b=0\). Thus
\(Q_4=re,Q_5=se\). The second identity in (3) gives \(vr-us>0\),
whereas \([4567]\ge0\) gives
\((vr-us)e\times f\le0\). This is the same zero-angle endpoint
argument as in the double-coincidence packet.

## 6. Cell T: the upper-b cap tilt

The bounded axis chart and the three exact finite product
factorizations bound all intrinsic rates
\((v_i-1/2)/t\), \(i=1,2,3\), on the open height square.
The spatial corrections are bounded too. Pass to limits of
\[
a_2=(\zeta_2-\zeta_1)/t,\qquad
a_3=(\zeta_3-\zeta_1)/t.
\]
The following exact combination of the full 29-row source system
gives
\[
\boxed{\Gamma=Ha_3+La_2=-L(1/2-D)<0.}         \tag{7}
\]
To make the source binding explicit, let \(\mathcal E_{ij}\) be the
original limit metric row, including all auxiliary terms. The
companion verifies polynomially
\[
\begin{aligned}
2\ell_u\bigl(\Gamma+L(1/2-D)\bigr)
={}&\ell_u\bigl(H\mathcal E_{03}
                +L\mathcal E_{02}
                -\tfrac12\mathcal E_{01}\bigr)\\
&-\tfrac12\mathcal E_{14}
  +L\mathcal E_{24}+H\mathcal E_{34}.
\end{aligned}                                \tag{8}
\]
In this identity the intrinsic contribution to \(\Gamma\) is
\((Lq_{24}-q_{14}/2)/(2\ell_u)\); none of these product variables
has been set to zero.

For the finite cap area \(B_n=P_{2,n}\times P_{3,n}\ge0\), the exact
determinant is
\[
[1235]_n
=(\zeta_{5,n}-\zeta_{1,n})B_n
 +t_n(a_{2,n}C_{35,n}-a_{3,n}C_{25,n}).        \tag{9}
\]
The first coefficient tends to \(v-1/2<0\). Also
\[
C_{25}=(1-2L)K_{25}<0,\qquad
C_{35}=-\frac LH C_{25}.
\]
The second coefficient in (9) therefore tends to
\[
-\frac{\Gamma}{H}C_{25}<0.
\]
Both terms in (9) have the adverse sign, and the second is strictly
negative. Hence \([1235]_n<0\) eventually, contradicting
\(\chi_{1235}=+1\). No comparison between \(B_n\) and \(t_n\) is used.

## Reproduction and scope

    python research/type7_completion/exhaustive_c0_flat_asymmetric.py /tmp/c0-flat-asymmetric
    python research/type7_completion/solver_cnf_certificates.py /tmp/c0-flat-asymmetric-rup \
      --checker /tmp/type7-rup-check /tmp/c0-flat-asymmetric

The producer checks all source, determinant, coefficient, and
reflection identities. The two CNFs additionally require independent
RUP replay. The checked marked reflection exchanges bd and da, so
the proof covers both.

Combining this result with the six-order nonparallel theorem and
both double-coincidence theorems excludes all nine nonparallel
both-flat interior C0 orders. Common-line residual families,
one-collinear-cap limits, and height boundaries require their own
arguments.
