# Common-line endpoint caps of ray-1 C0

For \(0<u,v<1/2\), suppose both endpoint triangles 123 and 067 lie
on the same transverse line. The necessary limit system reduces to
nine families: four endpoint-deficit families, four middle-deficit
families, and one circle with \(P_4=P_5\).
This is a classification, not an exclusion of these families as limits
of embedded sequences. Nonparallel endpoint-cap lines are outside its scope.

The companion checks the source metric identities, nine zero-safe
actual-trit implications, three additional positive coefficients in
the existing Gram certificate, and all twelve projected stresses on
every listed family. The nine CNFs require independent RUP replay.

Write
\[
d_i=\tfrac12-h_i\ge0,\quad \sum d_i=\tfrac12,\qquad
L=d_1+d_2,\quad M=d_6+d_7,\quad
D=d_0+L+M=\tfrac12-d_3-d_4-d_5.
\]
Here \(P_0=P_1=0\), and the heights are
\((0,\tfrac12,\tfrac12,\tfrac12,u,v,0,0)\). Put
\[
\ell_u=1-2u,\quad\ell_v=1-2v,\quad E=P_3-P_2,\quad F=P_7-P_6,
\]
\[
Q_4=P_4-2uP_3-\ell_uP_6,\qquad
Q_5=P_5-2vP_3-\ell_vP_6.
\]
With \(p=d_3,q=d_4,g=d_5\), the exact identities are
\[
\begin{gathered}
r=|Q_4|=\tfrac12-p-\ell_uD=q+g+2uD,\\
s=|Q_5|=\tfrac12-g-2vD=p+q+\ell_vD,\qquad
Q_4\cdot Q_5=-rs+q,\\
S=\ell_vQ_4-\ell_uQ_5,\qquad W=vQ_4-uQ_5,\\
E\cdot S=h_2(\ell_vr+\ell_us)-\ell_v(h_2-p),\\
F\cdot W=h_6(vr+us)-u(h_6-g).
\end{gathered} \tag{1}
\]
These are the closed source identities from
[the height-order proof](remaining_c0_height_order.md).

## 1. The two endpoint directions

First consider \(L=1/2\). The deficit budget gives
\(M=d_0=p=q=g=0\), so
\[
r=u,\qquad s=\ell_v/2,\qquad Q_5=-(s/r)Q_4.
\]
Whenever \(h_2,h_6>0\), the two dot identities force \(Q_4\)
opposite to both \(E\) and \(F\). If vertex 2 lies strictly between
1 and 3, then \(E\) points with \(P_2\), while the core identity
\[
d_0=h_1h_7+P_2\cdot P_7 \tag{2}
\]
makes \(P_2\) opposite to \(P_7=F\), a contradiction.
At \(h_1=0\) or \(h_2=0\), the remaining nonzero dot identity and
(2) instead place all points on one line and give the endpoint
families below at \(L=1/2\). The checked marked cap swap handles
\(M=1/2\), including both zero-edge endpoints. No zero edge is divided by.

For \(L,M<1/2\), all four endpoint sides \(h_1,h_2,h_6,h_7\)
are positive. Each cap has three possible orders:

| Label | Upper cap | Lower cap |
|---|---|---|
| a | 3 strictly between 1 and 2; \(d_1=0<d_2\) | 0 strictly between 6 and 7; \(d_6=0<d_7\) |
| b | 1 strictly between 2 and 3; \(d_2=0<d_1\) | 6 strictly between 0 and 7; \(d_7=0<d_6\) |
| d | \(P_1=P_3\); \(d_1=d_2=0\) | \(P_0=P_6\); \(d_6=d_7=0\) |

The other strict collinear order requires \(L=1/2\) or \(M=1/2\).
The common-line vectors \(P_2,P_7\) cannot point together. If they did,
(2) would give
\[
D=\tfrac12+d_2+d_6+2d_1d_7.
\]
The budget would force \(D=1/2,\ d_2=d_6=p=q=g=0\).
The two dot identities would again force \(E,F\) to point together,
although the cap orders make them opposite.

Consequently \(d_0=0\). Rotate the plane so
\[
E=h_2e,\quad F=h_6e,\quad e=(1,0),\qquad
P_2=-h_1e,\quad P_7=h_7e. \tag{3}
\]
For upper a,b,d, \(P_3/e\) is respectively \(-L,L,0\);
for lower a,b,d, \(P_6/e\) is \(-M,M,0\).

## 2. Nine actual-trit implications

The source retains the full topology/linking formula, both strict
height cuts, affine cocycles, weak Grassmann–Pluecker relations,
zero-safe actual trits, both cap collinearities, specified positive
interpolation or coincidence, and all 49 uniform C0 height relations.

Equation (3) adds exact cross-cap information. Every bracket containing
exactly one of 4,5 is a signed positive multiple of its transverse
coordinate, or zero. The companion expands these brackets in arbitrary
\(L,M,u,v\). Each nonzero coefficient is affine in \(L,M\), weakly signed
on their closed square and strictly signed for the open a/b parameters.
Coincident d parameters are substituted first. Brackets containing
neither 4 nor 5 vanish. No determinant or collapsing length is divided by.

For each order pair, one CNF proves the following disjunction:

1. \(P_{4y}=P_{5y}=0\);
2. \(P_{4y},P_{5y}>0\) and actual \([2345],[3456],[4567]\le0\);
3. \(P_{4y},P_{5y}<0\) and all three actual brackets are nonnegative.

Thus a nonflat case can be reflected transversely to give
\[
y_4,y_5>0,\qquad S_y\ge0,\quad W_y\le0,\quad
A:=Q_4\times Q_5\ge0. \tag{4}
\]
The circle centers lie on the line, so \(Q_{iy}=y_i\). Therefore
\[
\frac vu\le\frac{y_5}{y_4}\le\frac{\ell_v}{\ell_u},
\qquad u\ge v. \tag{5}
\]
Actual zero mixed brackets remain allowed.

## 3. No nonflat case with \(D>0\)

A nonflat case has \(r,s,q>0\): \(q=0\) would make \(Q_4,Q_5\)
opposite, contrary to (4).

Use the three middle angles from
[the height-order proof](remaining_c0_height_order.md), with
\(k=\ell_u/\ell_v,\ \ell=v/u\). They are the clockwise angles
\[
-e\longrightarrow S/\ell_v,\qquad
S/\ell_v\longrightarrow W/u,\qquad W/u\longrightarrow-e.
\]
The signs (4) and \(u\ge v\) place each in \([0,\pi]\).

The existing nonnegative Gram certificate is strict if
\(b_*=d_0+d_1+d_7>0\). It is also strict here when \(b_*=0\).
In normalized simplex variables
\(a=2d_2,b=2p,c=2q,d=2g,e=2d_6\), its Bernstein block \((2,2)\) has
\[
[a^4c^4]=1,\qquad[c^4e^4]=1. \tag{6}
\]
Its weight \(k^2\ell^2\) is positive. Since \(D=d_2+d_6>0\)
and \(q>0\), one of the monomials in (6) is positive.
The companion checks these coefficients from the same Gram polynomial
and replays the complete nonnegative certificate.

The original continuity proof now gives a sum strictly below \(\pi\).
Its path scales \(p,q,g\) to zero and adds their removed mass to \(b_*\).
Every intermediate point has positive \(b_*\); (6) handles the initial
point. No realization of intermediate scalar data is assumed.

For \(u>v\), the clockwise path returns from \(-e\) to \(-e\).
A nonnegative angle sum below \(\pi\) must be zero. Thus
\(S_y=W_y=0\); the invertible coefficient matrix gives
\(y_4=y_5=0\), a contradiction.

For \(u=v\), (4) already gives \(y_4=y_5>0\). The same strict angle
bound puts \(Q_4-Q_5\) on the negative \(e\) ray, so
\(A=y_4(Q_{4x}-Q_{5x})<0\), again contradicting (4).
Every \(D>0\) common-line case therefore has all points on that line.

## 4. The \(D=0\) case

Here \(d_0=d_1=d_2=d_6=d_7=0\), \(p+q+g=1/2\), and \(P_3=P_6=0\).
In a nonflat case, (4)--(5) still hold.

If \(u>v\) and \(pg>0\), the Gram certificate is strict because
its block \((0,0)\) has coefficient \([b^4d^4]=6\) and weight
\((1-k)^2(1-\ell)^2>0\). The preceding clockwise-return argument
is impossible. If \(u=v\), the mixed signs give \(y_4=y_5\), whereas
\[
|Q_4-Q_5|^2=(p+g)^2,\quad
e\cdot(Q_4-Q_5)=p-g,\quad
(y_4-y_5)^2=4pg.
\]
Thus in either case \(pg=0\).

It follows that \(q=2rs\), so \(Q_4,Q_5\) have the same unit direction
\(n\). Write \(c=e\cdot n\). Their dot equations are
\[
(c+1)(\ell_vr-\ell_us)=0,\qquad
(c-1)(vr-us)=0. \tag{7}
\]
For nonflat \(n\), \(|c|<1\); both linear factors vanish. This forces
\(u=v,\ r=s\), hence \(p=g=0\). The resulting family is
\[
d_4=\tfrac12,\quad P_4=P_5=\tfrac12n,\quad |n|=1,\quad u=v. \tag{8}
\]
Both line directions and every nonparallel direction are retained.

## 5. All line families

Write \(Q_4=\epsilon r e,\ Q_5=\eta s e\).
A zero radius for \(D=0\) contradicts the two dot equations;
for \(D>0\) both radii are positive.

For \((\epsilon,\eta)=(+,-)\), the dot identities give
\(p=h_2,\ g=h_6\), violating the deficit budget.
For \((\epsilon,\eta)=(-,+)\), \(q=0\), and the equations factor as
\[
p(4(v-u)+\ell_v/h_2)=0,\qquad
g(2(v-u)+u/h_6)=0.
\]
The coefficients are at least \(2\ell_u>0\) and \(2v>0\).
Thus \(p=q=g=0,\ D=1/2\).

The same-positive case is impossible for \(D>0\). Its equations give
\[
g\,d_6=2vDh_6,\qquad
(v-u)D=(p+\ell_uD)(g+2vD).
\]
Hence \(d_6,g>0\), followed by
\[
(v-u)d_6=v(p+\ell_uD),\qquad p=0.
\]
But \(v-u<v\ell_u\) and \(d_6\le D\), contradicting
\((v-u)d_6=v\ell_uD>0\).
The checked cap swap sends the same-negative case to this one.

There are four closed endpoint families. Choose upper and lower
labels independently in \(\{a,b\}\), take \(0\le L\le1/2\), and
set \(M=1/2-L\). The only deficits are
\[
d_2=L\ (a),\quad d_1=L\ (b);\qquad
d_7=M\ (a),\quad d_6=M\ (b).
\]
Put \(x_3=-L\) or \(L\), and \(x_6=-M\) or \(M\), for a or b.
Their coordinates are
\[
\begin{aligned}
&P_0=P_1=0,\quad P_2=-h_1e,\quad P_3=x_3e,\quad
P_6=x_6e,\quad P_7=h_7e,\\
&P_4=(2ux_3+\ell_ux_6-u)e,\qquad
P_5=(2vx_3+\ell_vx_6+\tfrac12-v)e.
\end{aligned} \tag{9}
\]
The closed endpoints cover all four zero outer-edge cases.

For \(D=0,\ u\ne v\), equation (7) gives four further line families.
Unlisted deficits vanish, \(d_4=1/2-d_j\), and
\(P_0=P_1=P_3=P_6=0,\ P_2=-e/2,\ P_7=e/2\).

| Height order | Nonzero deficit besides \(d_4\) | \(P_4/e\) | \(P_5/e\) |
|---|---|---|---|
| \(u<v\) | \(d_5=(v-u)/\ell_u\) | \(1/2\) | \(1/2-d_5\) |
| \(u<v\) | \(d_3=(v-u)/(2v)\) | \(-1/2+d_3\) | \(-1/2\) |
| \(u>v\) | \(d_3=(u-v)/\ell_v\) | \(1/2-d_3\) | \(1/2\) |
| \(u>v\) | \(d_5=(u-v)/(2u)\) | \(-1/2\) | \(-1/2+d_5\) |

All four displayed deficits lie strictly between 0 and \(1/2\).
At \(u=v\), the circle (8) is the remaining family.

The checker verifies all twelve closed projected stresses on every
family. This does not establish every additional inequality or the
existence of any embedded sequence. Their normal deformations must
still be excluded.

## Reproduction

    python research/type7_completion/exhaustive_c0_flat_common.py /tmp/c0-flat-common
    python research/type7_completion/solver_cnf_certificates.py /tmp/c0-flat-common-rup \
      --checker /tmp/type7-rup-check /tmp/c0-flat-common
