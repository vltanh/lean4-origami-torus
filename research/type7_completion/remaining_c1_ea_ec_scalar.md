# Excluding the complete interior EA and EC orbits

The [flat-cap reduction](remaining_c1_flat_reduction.md#4-two-zero-edge-order-orbits)
and [short-edge order cover](remaining_c1_short_edges.md#4-complete-remaining-zero-edge-order-cover)
put every EA or EC limit on a common transverse line. This package
excludes all their scalar families, including every relative rate of
normal collapse and cap-edge collapse. Its only geometric normalization
beyond the earlier normal stretch is the already proved relative lemma
for edge 23.

The new algebraic ingredient is an exact positive linear combination
of original determinant forms. Such identities preserve their actual
coefficients; the earlier sign-only linear relations lost this
information. Three displayed identities, together with 28 independently
replayable CNFs, close both entire order orbits.

## 1. Complete scalar source

Write `a=alpha`, `b=beta`, with `0<a,b<1`. Orient the lower common
line positively and put `k=h7`. For EA, `0<k<1/2`; for EC, `k=1/2`.
The preceding reduction gives

\[
\begin{aligned}
h&=(\tfrac12-k,\tfrac12,0,\tfrac12,\tfrac12-r,r,\tfrac12,k),\\
p&=\frac{1/2-(1-a)k}{a}>0,\\
P_0=P_1&=0,\qquad P_2=P_3=p,\qquad
P_4=p+\epsilon/2,\\
P_6&=k-\tfrac12,\qquad P_7=k,\\
P_5&=bp+(1-b)(k-\tfrac12)+\epsilon r.
\end{aligned}                                                    \tag{1}
\]

Here `epsilon=+1` or `-1` is the upper direction relative to the lower
line. The second circle identity gives `R5=r epsilon`. Its remaining
lower dot equation is

\[
\left(\frac b2-r\right)(\epsilon-1)=0.              \tag{2}
\]

Consequently `epsilon=-1` forces `r=b/2`, while `epsilon=+1` permits
the whole closed interval `0<=r<=1/2`. Splitting that interval into
its two endpoints and open interior leaves four families for EA and
four for EC, with no omitted parameter value. The companion checks
(1), (2), the total weight, and all twelve closed projected stresses
from the original 29-row metric system for each of these eight families.

The other endpoints of k belong to other members of the established
six-orbit order cover. No additional EA or EC endpoint is discarded.

## 2. Macro normal stretch and its forced zeros

Since p is nonzero, use P3 to fix the finite transverse scalar axis.
Divide its normal coordinate by the positive maximum normal width
delta, as in the [EB/ED scalar proof](remaining_c1_single_zero_scalar.md).
After a subsequence,

\[
N_0=N_1=N_3=0,\qquad
\max_{i\in\{2,4,5,6,7\}}|N_i|=1.
\]

The positive-determinant shear used there gives scalar coordinates

\[
x=(0,2k-1,2k,2k,2k+\epsilon,
       2k-1+b+2\epsilon r,2k-1,2k),                 \tag{3}
\]

and height coordinates `z=(0,a,1,1,1,b,0,0)`. The checker obtains (3)
from (1) through the same exact transformation, of determinant four.
The seventy determinant forms in the five normals and the 560
projected identities are inherited from their original expansions.
Both strict axial cuts and the full generic embedding/linking source
are retained. Actual zero determinants leave their generic signs free.

The following macro conclusions each have an exported UNSAT formula:

| Scalar family | Macro conclusion |
|---|---|
| EA, `epsilon=-1` | Excluded directly |
| EA, `epsilon=+1, r=0` | Excluded directly |
| EA, `epsilon=+1, 0<r<=1/2` | `N2=0` |
| Every EC family | `N2=N6=0` |

For a forced-zero conclusion the exported formula adds the disjunction
that one of its indicated normal coordinates is nonzero. Its UNSAT
certificate therefore proves all the stated zeros at once. At least
one of the other macro normals remains nonzero.

## 3. All scales at the shrinking edge 23

Once `N2=0`, vertices 2 and 3 coincide in the macro stretched limit.
The [relative short-edge theorem](remaining_c1_short_edges.md) gives
unit physical transverse length after dividing by h2, and normalized
axial difference `O(t h2)`, where `t=1/y^2`.

Exactly as in the EB/ED proof, normalize edge 32 independently of
delta. Every sequence has a subsequence with virtual direction

\[
(H,Y,0),\qquad
H\in\{-1,0,1\},\quad Y\ne0\text{ if }H=0.         \tag{4}
\]

For completeness, put `rho=max(2h2,|Y2|/delta)` in the stretched
chart. If `rho/h2` is unbounded, division by rho gives H=0 and a
nonzero normal component. Otherwise divide by `2h2`; the physical
normal component divided by h2 tends to zero, so unit physical length
forces H to be +1 or -1. In both alternatives the axial component
vanishes by the relative estimate. No comparison between t, h2, and
delta is imposed.

Let `D_ijkl` denote a macro determinant of `(x_i,N_i,z_i)` and let
`E_ijkl` denote the independently divided determinant at (4), defined
when its indices include 2 and 3. The producer inserts

\[
r_2=r_3+e(H,Y,tq),
\]

with independent positive e, factors e exactly from all fifteen such
determinants, and verifies that the discarded axial term carries t.
It then sets t to zero. The resulting forms are linear in the macro
normals and Y. A nonzero E binds to the same original generic sign
as its unscaled determinant. Affine identities are not mixed between
these differently normalized forms.

For every family except the two direct macro exclusions, the
companion covers all three H values. The residual H is `-epsilon`;
the other two possibilities are excluded directly by their necessary
sign constraints. The following exact linear identities close that
residual possibility.

## 4. Positive identities with all coefficients retained

Suppose a generic determinant has sign chi. Its corresponding actual
limiting form F satisfies `chi F>=0`, including when F=0. Thus an
identity

\[
\sum_j w_j\chi_j F_j=-N_4,\qquad w_j>0             \tag{5}
\]

rules out that collection of generic signs together with `N4>0`.
This produces a necessary Boolean clause. The companion verifies
(5) coefficient by coefficient, checks each rational weight's strict
sign on the complete parameter domain, and constructs the clause
from the referenced original generic literals and the actual N4 trit.

For `epsilon=+1`, `H=-1`, define

\[
\begin{aligned}
w_1&=\frac{1-a}{1-2(1-a)k},&
w_2&=\frac{1-a}{1-b},\\
w_3&=\frac1{1-b},&
w_4&=\frac{a(1-b)+2r(1-a)}{(1-b)^2}.
\end{aligned}
\]

Every weight is strictly positive for all the relevant a,b,k,r,
including r=0 and r=1/2. Direct determinant expansion gives

\[
-w_1D_{0127}+w_2D_{2457}+w_3E_{1235}+w_4E_{2345}
=-N_4.                                             \tag{6}
\]

For EA, the one clause from (6) closes every residual family with
`0<r<=1/2`. EC also uses the independent identity

\[
-\frac{1-a}{a}D_{0127}
+\frac1{1-b}E_{1235}+E_{2347}
+\frac{1-a}{1-b}E_{2357}=-N_4.                     \tag{7}
\]

All its weights are strictly positive. With (6) at k=1/2, it closes
both positive-r EC families. EC at r=0 closes directly in the virtual
sign system.

For EC with `epsilon=-1`, `H=+1`, use the exhaustive height cover
`a<b`, `a=b`, `a>b`. The latter two cells close directly after their
coefficient signs are specialized. In the first cell,

\[
-\frac{1-a}{a}D_{0257}
+\frac{b(1-a)}{a(1-b)}D_{2457}
+\frac1{a(1-b)}E_{1235}
+\frac{b-a}{a(1-b)^2}E_{2345}=-N_4.                \tag{8}
\]

Its four weights are strictly positive because a<b. The exact
parameterizations are `a=bu`, `a=b`, and `a=b+(1-b)u`, with
`0<u<1`; these cover every interior a,b. In the checker u reuses
the formal alpha variable only after simultaneous substitution.
Equation (8) supplies the one additional clause needed in the first
cell. There is no sample-point or numerical assumption.

The three identities themselves are exact algebra, not SAT conclusions.
Their Boolean clauses are combined with the original necessary source.
All resulting contradictions require independent RUP replay. Positive
weights are verified by exact factorization and multilinear corner
interpolation; a coefficient whose sign is not certified is omitted
from the auxiliary sign relaxation. No such omission is made in the
identities (6)–(8), whose complete coefficients are checked directly.

## 5. Replay and scope

The producer exports two direct macro exclusions, six simultaneous
forced-zero implications, and twenty virtual-direction/cell exclusions:
28 CNFs in total. These exclude all eight scalar families and hence
the complete EA and EC order orbits under the already checked marked
symmetries. Other zero-edge orbits and height boundaries have their
own proofs; no claim about them is needed here.

```sh
python research/type7_completion/remaining_c1_ea_ec_scalar.py /tmp/type7-c1-eaec-scalar
python research/type7_completion/solver_cnf_certificates.py /tmp/type7-c1-eaec-scalar-rup \
  --checker /tmp/type7-rup-check /tmp/type7-c1-eaec-scalar
```

The producer uses exact SymPy arithmetic and Boolean SAT only. It does
not invoke linear programming, numerical optimization, or SMT arithmetic.
Its certificate packet records every referenced determinant coefficient,
positive weight, generated clause, and parameter-cell substitution.
