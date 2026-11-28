# The nonflat coincident-vertex circle is impossible

The [common-line cap classification](exhaustive_c0_flat_common.md) leaves
one circle that is not itself confined to the common cap line. Its interior
ray-1 C0 coordinates are

\[
\begin{gathered}
d_4=\tfrac12,\qquad d_i=0\ (i\ne4),\qquad 0<u=v<\tfrac12,\\
P_0=P_1=P_3=P_6=0,\quad
P_2=P,\quad P_7=-P,\quad P_4=P_5=N,\quad |P|=|N|=\tfrac12.
\end{gathered}
\]

This package excludes every nonflat member, `cross(P,N) != 0`.
The two line directions `N=P` and `N=-P` remain separate cases.
Two finite sign implications have independent RUP certificates. The
analytic contradiction below allows every relative rate of the shrinking
diagonal, cap area, and `t=1/y²`.

## 1. The relative diagonal and its divided tilt

Use the bounded axis chart with `P0=P1=0`. Put

\[
\ell=\zeta_1,\qquad b=v_1,\qquad
L=1-h_1-h_2=d_1+d_2>0,\qquad
a=\frac{\zeta_3-\zeta_1}{t},\qquad
g=\frac{v_3-v_1}{t}.
\]

The [relative diagonal proof](exhaustive_c0_double_coincidence.md)
uses exact finite polarizations to prove

\[
a=O(L),\qquad g=O(L),\qquad |P_3|/L\longrightarrow1.
\tag{1}
\]

Its absorption uses only the nonzero limiting coefficient `-(1-2u)`;
it does not use `cross(P2,P7)>0`. Thus it applies here even though the
two limiting cap lines agree. After taking a subsequence write

\[
w=\lim P_3/L,\quad |w|=1,\qquad
A=\lim a/L,\qquad G=\lim g/L.
\]

Also put

\[
a_2=(\zeta_2-\zeta_1)/t,\qquad
g_2=(v_2-v_1)/t.
\]

These rates remain bounded in the open C0 component. The same
polarizations at 02,12,14,24 give a direct bound with limiting
coefficient `-(1-2u)`. Subsequences may therefore be chosen so all
displayed rates converge.

If `w=2P2`, write `P2=-e/2` for a unit vector `e`. The four checked
source equations are

\[
\begin{aligned}
A-G&=-2h_0,\\
-e\cdot P_4-\tfrac12(1-2u)A
  &=-h_3+\tfrac12(1-2u)G,\\
a_2-g_2&=-h_0,\\
-\tfrac12e\cdot P_4-\tfrac12(1-2u)a_2
  &=\tfrac12h_3+\tfrac12(1-2u)g_2.
\end{aligned}
\]

They give

\[
\frac A2-a_2=\frac{h_3}{1-2u}
             =\frac{1}{2(1-2u)}.
\tag{2}
\]

The companion replays the original finite metric identities and their
cocycle bindings before using (2).

## 2. Exact virtual-direction implications

Write `C24=cross(P,N)`. The sign source retains the full necessary
generic topology and linking formula, actual zero brackets, affine
cocycles, weak Grassmann–Pluecker relations, strict height cuts, and
all uniform C0 height relations. The exact circle supplies

\[
r_4=r_5,\qquad r_2+r_7=r_0+r_1,
\]

where `r_i=(P_i,z_i)` and
`z=(0,1/2,1/2,1/2,u,u,0,0)`.

The unit direction `w` is independent of the unscaled coincidence.
Because `P,N` are independent, `cross(P,w)` and `cross(N,w)` cannot
both vanish. All five projected vectors `P2,P4,P5,P7,w` obey the
rank-two three-term relations. Each determinant containing vertices
1 and 3 may be divided by the positive finite `L`; (1) makes its
limiting short column `(w,0)`. All fifteen forms are expanded exactly,
including their specialized circle coefficients. Nonzero normalized
limits fix the same generic completion signs as the original
determinants; zero limits leave those signs free.

One CNF proves the implication

\[
C_{24}<0\quad\Longrightarrow\quad
P_2\times w=0,\quad P_4\times w>0,\quad
\chi_{1234}=-1,\quad\chi_{1237}=+1.
\tag{3}
\]

Since `|P2|=1/2` and `|w|=1`, the first two conclusions choose
`w=2P2`. The other CNF proves

\[
C_{24}>0\quad\Longrightarrow\quad\chi_{0167}=-1.
\tag{4}
\]

No actual zero determinant is replaced by a strict determinant.
The strict hypothesis on `C24` is precisely the nonflat case under
consideration.

## 3. One bracket forces a lower bound for the cap area

First suppose `C24<0`. Let

\[
B_n=P_{2,n}\times P_{3,n}\ge0.
\]

The weak inequality follows from the normalized generic sign
`chi0123=+` and the positive axis height. For any vertex `j`, the
following identity holds exactly at every finite stage:

\[
[123j]_n=(\zeta_{j,n}-\ell_n)B_n
       +t_n\bigl(a_{2,n}C_{3j,n}-a_nC_{2j,n}\bigr).
\tag{5}
\]

For `j=4`, equations (2) and (3) give

\[
\frac{a_{2,n}C_{34,n}-a_nC_{24,n}}{L_n}
\longrightarrow (2a_2-A)C_{24}
=-\frac{C_{24}}{1-2u}>0.
\tag{6}
\]

Meanwhile `zeta4-ell -> -(1-2u)/2<0`. The required sign
`chi1234=-` says that the actual determinant in (5) is nonpositive.
Consequently there is a constant `c0>0` such that eventually

\[
B_n\ge c_0t_nL_n.
\tag{7}
\]

Only a lower bound is needed. In particular `B_n/(t_n L_n)` is
allowed to diverge.

## 4. The other bracket contradicts that lower bound

For vertex 7, the limiting circle has

\[
C_{27}=0,\qquad C_{37,n}/L_n\longrightarrow w\times P_7
      =2P\times(-P)=0.
\]

The rates in (1) and the boundedness of `a2` therefore give

\[
t_n\bigl(a_{2,n}C_{37,n}-a_nC_{27,n}\bigr)=o(t_nL_n).
\]

Since `zeta7-ell -> -1/2`, equation (5) implies

\[
[1237]_n\le-\tfrac14B_n+o(t_nL_n)<0
\]

for all sufficiently large `n`, by (7). This contradicts
`chi1237=+` in (3). The argument has made no comparison of the
rates of `B_n`, `L_n`, and `t_n`.

## 5. The opposite circle orientation

If `C24>0`, use the checked marked reflection `p(i)=1-i mod 8`,
followed by translation to old vertex 1 and spatial inversion.
Its limiting coordinates are

\[
P'_i=-P_{p(i)},\qquad z'_i=\tfrac12-z_{p(i)}.
\]

It preserves the unique deficit `d4=1/2`, sends the common height
to `u'=1/2-u`, keeps `P2'=P` and `P7'=-P`, and sends `N` to `-N`.
Thus `C24'=-C24<0`. The permutation of the bracket `0123` is
`1076`, with even sorting parity; spatial inversion has determinant
`-1`. By (4),

\[
\chi'_{0123}=-\chi_{0167}=+1.
\]

The transformed sequence therefore satisfies the normalization
needed in the first case. This excludes the other nonflat orientation.
The companion checks both marked cocycles, the permutation parity,
the height transformation, and the full circle coordinates.

## Reproduction and scope

```sh
python research/type7_completion/exhaustive_c0_circle.py /tmp/c0-circle
python research/type7_completion/solver_cnf_certificates.py /tmp/c0-circle-rup \
  --checker /tmp/type7-rup-check /tmp/c0-circle
```

Both CNFs require independent RUP replay. The package excludes the
nonflat coincident-vertex circle throughout the open height interval.
It leaves its two line directions, the other surviving common-line
families, and height endpoints open.
