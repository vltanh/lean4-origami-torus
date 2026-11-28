# Nonparallel collinear caps: a uniform first-order sign

For an interior ray-1 C0 limit whose endpoint triangles are both
collinear but lie on distinct transverse lines, six of the nine
positive-edge order pairs are impossible. The only remaining pairs
are bd, da, and dd; bd and da are exchanged by the checked marked
cap swap. Thus there are two canonical remaining families, each with
at least one endpoint-cap coincidence.

This reduction uses four actual-trit certificates and an exact
first-order metric sign. The sign proof makes no assumption about
the ratio between the planar cap area and \(t=1/y^2\).

## 1. Complete endpoint order cover

Use the order labels from
[the common-line classification](exhaustive_c0_flat_common.md):

| Label | Upper 123 | Lower 067 |
|---|---|---|
| a | 3 between 1 and 2; \(d_1=0<d_2\) | 0 between 6 and 7; \(d_6=0<d_7\) |
| b | 1 between 2 and 3; \(d_2=0<d_1\) | 6 between 0 and 7; \(d_7=0<d_6\) |
| d | \(P_1=P_3\) | \(P_0=P_6\) |

The metric argument in Section 1 of that classification handles
\(L=d_1+d_2=1/2\) or \(M=d_6+d_7=1/2\) before assuming a common
line: its strict-between case is impossible, and each zero-edge
endpoint forces the two cap lines to agree. Thus every nonparallel
case here has \(L,M<1/2\) and positive
\(h_1,h_2,h_6,h_7\), and belongs to the nine table pairs.

In the full zero-safe source, a single clause asserts that actual
\(C_{27}=P_2\times P_7\) is nonzero. This is equivalent to
nonparallelism because both cap lines pass through the projected
origin and \(P_2,P_7\ne0\). The source includes cap interpolation,
both strict height cuts, actual trits, all affine cocycles, weak
Grassmann–Pluecker relations, 49 uniform height identities, and the
necessary generic topology/linking formula.

Two CNFs exclude ab and ba outright. One CNF for each of aa and ad
proves the joint consequence
\[
C_{27}>0,\qquad \chi_{1237}=+1, \tag{1}
\]
where the second sign belongs to the fixed generic completion.
Its actual limiting bracket is zero, so it is essential to retain
the distinction between these two assertions.

## 2. Bounded vertical rates in the open height square

Suppose the upper order is a. Write
\[
L=d_2>0,\quad H=\tfrac12-L=h_2,\quad p=d_3,\quad
\ell_u=1-2u>0.
\]
The limits are \(h_1=1/2\) and \(P_3=2LP_2\).

The bounded axis chart retains product scales \(q_{05},q_{14},q_{24}\).
On the interior C0 component, their nonzero complementary factors give
\[
v_i=\tfrac12+t\gamma_i,\qquad i=1,2,3,
\]
with all three \(\gamma_i\) bounded. After taking a subsequence,
\[
q_{05}=4v\gamma_3,\qquad
q_{14}=2\ell_u(\gamma_1-\gamma_3),\qquad
q_{24}=2\ell_u(\gamma_2-\gamma_3). \tag{2}
\]
Here the intermediate heights may vary along the sequence; their
limits remain strictly inside the square. The companion checks the
exact finite polynomial expansions, including the terms of order \(t\)
discarded in (2). No factor tending to zero is divided by.

For these three vertices the actual normalized axial coordinates are
\[
\zeta_i=v_i+tH_i.
\]
The \(H_i\) are the bounded axis corrections, not new free normal
scales. Let
\[
a_2=\gamma_2-\gamma_1+H_2-H_1,\qquad
a_3=\gamma_3-\gamma_1+H_3-H_1.
\]
Thus \(\zeta_2-\zeta_1=ta_2\) and
\(\zeta_3-\zeta_1=ta_3\) exactly before taking limits.

## 3. The actual cap tilt has a strict sign

The three source equations on edges 01,02,03 give
\[
K:=\tfrac12H_3-LH_2-HH_1=0. \tag{3}
\]
This identity uses the collinear limiting positions
\(P_2=-e/2,\ P_3=-Le\) and the exact horizontal lifts. It is a
source equation, not a choice of axial gauge.

Define the actual first-order tilt
\[
\Gamma=\tfrac12a_3-La_2
       =-\frac{Hq_{14}+Lq_{24}}{2\ell_u}+K.
\]
The source equations on 14,24,34, combined with (3), give
\[
\boxed{\displaystyle
\Gamma=\frac{L(H-p)}{\ell_u}>0.} \tag{4}
\]
The strictness follows from
\[
H-p=d_0+d_4+d_5+d_6+d_7>0.
\]
Indeed nonparallel \(P_2,P_7\) and the core identity
\(d_0=h_1h_7+P_2\cdot P_7\) give \(d_0>0\).

For an explicit check, write \(E_{ij}\) for the full limiting metric
equation, including its retained product scale and axial correction.
The companion verifies the polynomial identity
\[
\begin{aligned}
2\ell_u\Gamma-2L(H-p)
={}&\ell_u\left(\tfrac12E_{03}-LE_{02}-HE_{01}\right)\\
 &-HE_{14}-LE_{24}+\tfrac12E_{34}.
\end{aligned} \tag{5}
\]
All dependence on the free coordinates of vertex 4 cancels. No
product variable is set to zero.

## 4. The finite determinant contradicts the generic completion

Let \(A_n=P_{2,n}\times P_{3,n}\) be the actual planar cap area.
The usual generic normalization \(\chi_{0123}=+1\) gives \(A_n\ge0\):
the axis height \(\zeta_{1,n}\) is positive and
\([0123]_n=\zeta_{1,n}A_n\). The argument does not require a positive
lower bound or even strict positivity for \(A_n\).

The exact determinant expansion is
\[
[1237]_n=(\zeta_{7,n}-\zeta_{1,n})A_n
+t_n\left(a_{2,n}C_{37,n}-a_{3,n}C_{27,n}\right). \tag{6}
\]
Since \(P_3=2LP_2\) in the limit, the second coefficient converges to
\[
(2La_2-a_3)C_{27}=-2\Gamma C_{27}<0
\]
by (1) and (4). Also
\(\zeta_{7,n}-\zeta_{1,n}\to-1/2\). Both terms in (6) are therefore
nonpositive for all sufficiently late terms, and the second is
strictly negative. Consequently
\[
[1237]_n<0
\]
eventually, contradicting the fixed generic sign in (1).

This proof covers \(A_n\ll t_n\), comparable scales, and
\(t_n\ll A_n\) in one estimate. It uses bounded rates and determinant
continuity, not a Taylor expansion with an assumed relative rate.

## 5. Remaining orders and scope

The marked cap swap \(i\mapsto1-i\pmod8\) sends
\((u,v)\) to \((1/2-v,1/2-u)\) and
\(d_i\) to \(d_{-i}\). It exchanges aa with bb and ad with db.
After reanchoring the reverse long edge 01, choose the generic spatial
orientation again. The source and argument above cover both signs
of \(C_{27}\), so this normalization loses no case.

Combining the two direct CNF exclusions, the first-order sign proof,
and this exact marked symmetry leaves
\[
\boxed{\text{bd, da, dd}},
\]
with bd and da reflected copies. Every remaining nonparallel case
therefore has an endpoint coincidence. Their further degenerations,
and the nine common-line families, still need separate exclusions.

## Reproduction

    python research/type7_completion/exhaustive_c0_flat_nonparallel.py /tmp/c0-flat-nonparallel
    python research/type7_completion/solver_cnf_certificates.py /tmp/c0-flat-nonparallel-rup \
      --checker /tmp/type7-rup-check /tmp/c0-flat-nonparallel

The producer checks (2), the full source identity (5), the exact
finite determinant (6), and the marked order-pair map. All four
CNFs require independent RUP acceptance.
