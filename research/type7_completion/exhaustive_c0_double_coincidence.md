# The positive-core double coincidence is impossible

Consider an interior ray-1 C0 limit with
\[
P_1=P_3=0,\qquad P_0=P_6=0,\qquad
C_{27}=P_2\times P_7>0.
\]
Both endpoint triangles are collinear. This package excludes this
orientation of the double coincidence. Together with the
[nonparallel cap reduction](exhaustive_c0_flat_nonparallel.md), the
remaining nonparallel cases are bd/da and dd with \(C_{27}<0\).

The argument uses one independently replayable CNF and an exact
relative estimate for the shrinking diagonal 13. It does not
compare the rates of its length, the other shrinking diagonal, the
upper cap area, or \(t=1/y^2\).

## 1. An exact relative estimate for diagonal 13

Use the bounded axis chart with \(P_0=P_1=0\), and write
\[
\ell=\zeta_1,\quad b=v_1,\quad h_0=-X_{01},\quad
L=X_{13}=1-h_1-h_2=d_1+d_2>0.
\]
Here \(\zeta\) denotes the actual normalized spatial axial coordinate,
while \(v\) denotes the intrinsic vertical coordinate. Both
\(\ell,b\) tend to \(1/2\). Define the finite quantities
\[
g=(v_3-v_1)/t,\qquad a=(\zeta_3-\zeta_1)/t.
\]
Their definitions alone impose no bound.

The exact metric equations on 01,13,03 give
\[
\ell^2=b^2+th_0^2,\qquad
\ell a=bg-h_0L,\qquad
\ell^2|P_3|^2=(bL+th_0g)^2.                 \tag{1}
\]
The last identity is a polynomial consequence of the first two
equations and the edge-13 equation; the companion supplies its
exact source combination.

The face 134 has zero cocycle period. Polarizing its three edge
equations gives
\[
P_3\cdot P_4+a(\zeta_4-\ell)
   =LX_{14}+gV_{14}.                       \tag{2}
\]
Substitute the middle identity of (1). The coefficient of \(g\) is
\[
c=\frac{b(\zeta_4-\ell)}{\ell}-V_{14}
  \longrightarrow u-\tfrac12-(\tfrac12-u)
  =-(1-2u)\ne0.
\]
All other coefficients and \(P_4\) remain bounded. Consequently
\[
|g|\le C(L+|P_3|).
\]
The final identity of (1) gives
\[
|P_3|\le C_1L+C_2t|g|.
\]
Absorbing the last term for sufficiently small \(t\) proves
\[
g=O(L),\qquad a=O(L),\qquad
\frac{|P_3|}{L}\longrightarrow1.            \tag{3}
\]
Thus, after taking a subsequence,
\[
w=P_3/L\longrightarrow w_\infty,\quad |w_\infty|=1,
\qquad
(\zeta_3-\zeta_1)/L=O(t).
\]
Every finite \(L\) is positive by the strict horizontal edge bound.
No limiting positive lower bound for \(L\) is used.

## 2. The complete virtual-direction implication

The source retains the full necessary generic topology/linking
formula, actual trits, both strict height cuts, affine cocycles,
weak Grassmann–Pluecker relations, all 49 uniform C0 height
relations, and the exact coincidences \(P_1=P_3\), \(P_0=P_6\).

Introduce the direction \(w_\infty\) independently. Since \(P_2,P_7\)
are independent and \(w_\infty\ne0\), their two cross products with
\(w_\infty\) cannot both vanish. The five projected vectors
\(P_2,P_4,P_5,P_7,w_\infty\) obey all rank-two three-term relations.

For each of the fifteen brackets containing vertices 1 and 3,
divide the actual determinant by the positive number \(L\).
Its limit is the determinant obtained by replacing the vector
from 1 to 3 by \((w_\infty,0)\). The exact relative axial estimate
(3) justifies this replacement, including brackets whose other
vertices coincide in the limit. A nonzero normalized determinant
fixes the generic sign; a zero leaves that sign free.

The companion expands all fifteen forms and certifies every
coefficient sign on the open height square. One CNF proves
\[
P_2\times w_\infty=0,\qquad
P_7\times w_\infty<0,\qquad
\chi_{1237}=+1.                             \tag{4}
\]
The metric gives \(|P_2|=1/2\). Since \(C_{27}>0\), the first two
relations in (4) choose the positive multiple of \(P_2\). Hence
\[
w_\infty=2P_2.                              \tag{5}
\]
This is an actual directional conclusion, not an assumption that
the shrinking triangle has a fixed collinear order before taking
limits.

## 3. The divided cap tilt is strictly positive

Set \(P_2=-e/2\), with \(e\) a unit vector, and let
\[
A=\lim a/L,\qquad G=\lim g/L,\qquad
\ell_u=1-2u>0.
\]
The quantities are bounded by (3). For vertex 2 put
\[
a_2=(\zeta_2-\zeta_1)/t,\qquad
g_2=(v_2-v_1)/t.
\]
These are bounded in the open C0 component. Alternatively, the
same pair of polarization equations used below bounds them
directly, because its limiting coefficient is \(-\ell_u\).

The source equations on 01,03,13,14,34, divided as above, and the
equations on 01,02,12,14,24 give
\[
\begin{aligned}
A-G&=-2h_0,\\
-e\cdot P_4-\tfrac12\ell_u A
  &=-h_3+\tfrac12\ell_u G,\\
a_2-g_2&=-h_0,\\
-\tfrac12e\cdot P_4-\tfrac12\ell_u a_2
  &=\tfrac12h_3+\tfrac12\ell_u g_2.
\end{aligned}                              \tag{6}
\]
The horizontal period of triangle 012 is \(-1\); the third
equation in (6) includes this period. The companion checks all
cocycle and horizontal-lift bindings explicitly.

Eliminating the two intrinsic rates and \(e\cdot P_4\) gives
\[
\boxed{\displaystyle
\tfrac12A-a_2=\frac{h_3}{1-2u}>0.}           \tag{7}
\]
Strictness follows from the deficit budget:
\[
h_3=d_0+d_4+d_5>0.
\]
Indeed the core identity and nonparallel \(P_2,P_7\) imply
\(d_0=h_1h_7+P_2\cdot P_7>0\).

## 4. A uniform finite determinant contradiction

Let \(B_n=P_{2,n}\times P_{3,n}\). Generic normalization
\(\chi_{0123}=+1\) and the positive axis height give \(B_n\ge0\).
The exact finite determinant identity is
\[
[1237]_n
=(\zeta_{7,n}-\zeta_{1,n})B_n
+t_n\left(a_{2,n}C_{37,n}-a_nC_{27,n}\right). \tag{8}
\]
By (5),
\[
C_{37,n}/L_n\longrightarrow2C_{27}.
\]
By (7), the second coefficient in (8), divided by \(L_n\), tends to
\[
(2a_2-A)C_{27}
=-\frac{2h_3C_{27}}{1-2u}<0.
\]
The first coefficient tends to \(-1/2\). Therefore both terms in
(8) are eventually nonpositive, and the second is strictly
negative. This contradicts \(\chi_{1237}=+1\) from (4).

The argument permits \(B_n\), \(L_n\), and \(t_n\) to approach zero
at arbitrary relative rates.

## Reproduction

    python research/type7_completion/exhaustive_c0_double_coincidence.py /tmp/c0-double-coincidence
    python research/type7_completion/solver_cnf_certificates.py /tmp/c0-double-coincidence-rup \
      --checker /tmp/type7-rup-check /tmp/c0-double-coincidence

The CNF requires independent RUP replay. The package excludes the
stated orientation only; it does not claim a complete C0 exclusion.
