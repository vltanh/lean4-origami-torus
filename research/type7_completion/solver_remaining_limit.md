# Exact projected metric identities on the six limit components

## Result

`solver_remaining_limit.py` eliminates the axial corrections from the
bounded-axis limit system by exact rational linear algebra. It retains
**all six product scales** until the five proved universal relations
justify their elimination. The source is the complete **29-by-14** system:

- 24 limit edge equations;
- five universal linear relations among the six product scales;
- auxiliaries `H1,...,H7,w,q05,q14,q24,q25,q47,q57`.

Each of the six generic components has auxiliary rank 14 and **12
independent projected metric identities**. The output covers **54
parameter strata**, including every polygon edge and vertex and the
interior exceptional line `B=0` in component 3. It exports **642
polynomial row-combination certificates**, all valid for both markings.

The auxiliary matrix has rank 14 throughout this cover. At two geometric
corners, the product-relation matrix drops from rank two to rank one, so
there are **11 projected identities** there. Those corners appear in six
component records because the component planes overlap. They are reduced
directly; generic product vanishings are not imposed on them.

The full generation took **7.47 seconds**. The independent checker passed
the original-system reconstruction, every finite-parameter cancellation,
all 642 row identities, all rank certificates, and the complete feasible
pivot-zero cover. This is an exact dimension reduction for the limit
problem, not a marking exclusion or a finite-height certificate.

## 1. The system being eliminated

Use the notation and uniform bounds of `exhaustive_remaining_axis.md`.
Let `v6=v3-1/2` denote the baseline, while the actual intrinsic coordinate
is `v6+t*w`. The spatial baseline is

\[
z_i=v_i\quad(i\ne4,5),\qquad
z_4=2v_3-v_4,\qquad z_5=2v_3-v_5-1.
\]

The actual normalized axial coordinate is `z_i+t*H_i`, with `H0=0`.
For an edge, define

\[
T_{ij}=|P_j-P_i|^2-X_{ij}^2,
\qquad V^0_{ij}=v_j-v_i+n_{ij},
\qquad \Delta w_{ij}=w(\mathbf1_{j=6}-\mathbf1_{i=6}).
\]

The exact compact metric equation is

\[
T_{ij}+q_{ij}+2(z_j-z_i)(H_j-H_i)
-2V^0_{ij}\Delta w_{ij}
+t\bigl((H_j-H_i)^2-(\Delta w_{ij})^2\bigr)=0,                 \tag{1}
\]

where `q_ij=0` on the other eighteen edges. All correction variables are
uniformly bounded, so the last term vanishes in a limit. The two markings
have identical vertical cocycles; their horizontal displacements differ.
The certificate therefore records the common matrix and the exact
constant terms `T_ij` for **each** marking.

In the independent affine coordinates

\[
f=2v_3-1,\quad a=v_1-v_3,\quad c=v_2-v_3,\quad d=v_3-v_4,
\quad b=2v_3-2v_5-1,\quad e=2v_3-2v_7-1,
\]

the five additional rows are

\[
\begin{aligned}
L_1&=a q_{24}-c q_{14},\\
L_2&=(1-b)q_{24}+2d q_{25},\\
L_3&=f q_{57}-e q_{05},\\
L_4&=2c(q_{47}-q_{57})+e(q_{24}-q_{25}),\\
L_5&=(2d+1)q_{57}-bq_{47}.
\end{aligned}                                                    \tag{2}
\]

All five vanish exactly before taking the limit. Their derivation and the
complete six-component cover are checked separately in
`exhaustive_remaining_locus.py`. The reducer never substitutes a generic
consequence such as `q24=0` directly into the original system.

On each component, two vertical parameters remain. Eliminating the
fourteen linear auxiliaries leaves seven horizontal coordinates and
eleven transverse coordinates, in addition to those two parameters:
**20 projected variables**. The residual identities are quadratic in the
horizontal and transverse coordinates, with polynomial coefficients in
the component parameters.

## 2. Denominator and boundary handling

Write the 29 equations as

\[
M(A,B)u+(T_{01},T_{02},\ldots,T_{67},0,0,0,0,0)^T=0.
\]

The producer finds left null vectors over the rational function field,
clears every denominator, divides common polynomial factors, and checks
the resulting identities directly over the polynomial ring. Each stored
29-entry vector `c` satisfies

\[
cM=0
\]

as an exact polynomial identity. Therefore its projected equation
`sum c_ij*T_ij=0` remains necessary even when a parameter or a former
denominator vanishes.

Completeness of the reduced **linear equation system** needs more than
these necessary identities. The output records nonzero minors proving
the matrix ranks, right-nullspace witnesses proving the matching upper
bounds, and a nonzero minor of the projected stress rows. These witnesses
prove that the stored projected identities span every compatibility
condition wherever their listed factors are nonzero. This equivalence
concerns the linear equations only; bounds on the auxiliaries remain
additional necessary conditions.

Every feasible zero locus of a witness factor is reduced separately. The
checker intersects that affine line with the closed component polygon
using exact rational arithmetic and verifies that the linked child covers
the entire intersection. Each step lowers the parameter dimension, so
the cover terminates at points. In particular, component 3's initial
minor contains `B`; `B=0` crosses its interior and is not silently omitted.

The two exceptional physical corner baselines are the component-0 points

\[
(A,B)=(1/2,-1/2),\qquad (A,B)=(1,0).
\]

At each, the five product rows have rank one rather than two. Their
independently reduced eleven-identity systems are in the output JSON.

## 3. A uniform sparse identity set for component 0

Here

\[
(v_1,v_2,v_3,v_4,v_5,v_7)=(1/2,1/2,1/2,A,B,0),
\quad 1/2\le A\le1,\quad -1/2\le B\le0.
\]

Put `u=1-A`, `v=-B`, `lambda_u=1-2u`, and `lambda_v=1-2v`.
Thus both `u` and `v` range over `[0,1/2]`. The following twelve
expressions vanish throughout the closed component:

\[
\begin{gathered}
T_{06}=T_{07}=T_{12}=T_{13}=T_{23}=T_{67}=0,\\
T_{01}-T_{02}-T_{17}+T_{27}=0,\\
2uT_{34}+\lambda_uT_{46}-2u\lambda_uT_{36}=0,\\
2vT_{35}+\lambda_vT_{56}-2v\lambda_vT_{36}=0,\\
T_{45}-2uT_{35}-\lambda_uT_{56}-2vT_{34}-\lambda_vT_{46}
+(2u\lambda_v+2v\lambda_u)T_{36}=0,\\
\lambda_v(T_{24}-T_{34})-\lambda_u(T_{25}-T_{35})=0,\\
v(T_{47}-T_{46})-u(T_{57}-T_{56})=0.
\end{gathered}                                                     \tag{3}
\]

These sparse rows were supplied by the projected-geometry analysis and
are used as the reducer's preferred component-0 basis. The three middle
rows annihilate the 24 metric rows directly; the penultimate row subtracts
`L2`, and the last adds `L5/2`. Their exact 29-row coefficient checks pass.
The rank witnesses on all nine component-0 strata confirm that they span
the projected compatibility conditions throughout the closed rectangle.
At `u=v=0` or `u=v=1/2`, one projected row vanishes and the other eleven
give the exceptional corner system.

The first six give the two unit-perimeter endpoint triangles 067 and
123. The four-term identity gives the previously useful exact relation

\[
h_0=\tfrac12-h_1h_7-P_2\mathbin{\cdot}P_7,
\]

after writing the cyclic horizontal step displacements as `-h_i`.
The other identities retain both middle projected vertices and all
product-scale effects.

## 4. A uniform sparse identity set for component 1

Here

\[
(v_1,v_2,v_3,v_4,v_5,v_7)=(A,1/2,1/2,1/2,B,0),
\quad 1/8\le A\le1/2,\quad -1/2\le B\le0.
\]

Put `v=2B+1`. The following twelve identities hold on the closed component:

\[
\begin{gathered}
T_{06}=T_{07}=T_{23}=T_{34}=T_{67}=0,\\
(2A-1)(T_{01}-2AT_{02})-2AT_{12}=0,\\
(2A-1)(T_{01}-2AT_{03})-2AT_{13}=0,\\
T_{01}-2AT_{02}-T_{17}+2AT_{27}=0,\\
T_{35}-vT_{36}-T_{45}+vT_{46}=0,\\
2BT_{35}-2BvT_{36}-vT_{56}=0,\\
(1-A+B)T_{24}=0,\\
T_{57}-T_{56}+2B(T_{47}-T_{46})=0.
\end{gathered}                                                     \tag{4}
\]

The coefficient `1-A+B` is positive throughout this closed polygon except
at `(A,B)=(1/2,-1/2)`. Its certificate uses the full metric row for edge
24 together with `L1-L2/2`. It therefore proves `T24=0` everywhere except
that one exceptional corner, without dividing by a factor that vanishes
along an entire boundary edge.

The final identity is certified directly by
`E57-E56+2B*(E47-E46)-L5=0`, where `Eij` is the complete limit edge
equation. It remains informative at `B=-1/2`. The rank witnesses on all
nine component-1 strata verify that these twelve sparse rows span the
projected compatibility conditions everywhere, with eleven independent
rows at the exceptional corner.

## 5. Independent replay and reproduction

The standalone verifier reconstructs every coefficient of the original
matrix without calling the producer's matrix or nullspace routines. It
checks the exact finite-`t` cancellation behind (1), each universal
relation (2), every exported row combination, every determinant witness,
both nullspace upper-rank bounds, and every child covering a feasible
pivot-zero locus. Its polynomial reader accepts only arithmetic, named
symbols and integer powers; it does not execute proof-file expressions.

```sh
python3 research/type7_completion/exhaustive_remaining_locus.py
python3 research/type7_completion/solver_remaining_limit.py \
  /tmp/type7-remaining-limit.json
python3 research/type7_completion/solver_remaining_limit_verify.py \
  /tmp/type7-remaining-limit.json
```

The JSON contains the full original matrix, both marking-dependent
constant vectors, component parameterizations and facets, all 54 strata,
the exact certificates and their rank conditions. It is reproducible
from the repository data and requires only SymPy and the Python standard
library. No floating-point LP, SAT search, or NRA search is involved.

These projected equations are intended for the remaining geometric
analysis. They do not establish feasibility, infeasibility, a uniform
finite-height threshold, or a Lean theorem.
