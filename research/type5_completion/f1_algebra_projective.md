# Type 5: complete projective metric elimination

This is the primary algebraic implementation for the F1 attack. It replaces the
23-variable signed-Gram system by **two charts, each with 15 real variables and
seven metric equations**. The charts have a bounded ratio parameter and retain
all nongeneric simplex-intersection tests. The F1 option takes the disjunction
of all five finite cells at the same metric `tau = 1/2 + 10^6 i`.

No cell is excluded by constructing these formulas. Lower variable count comes
with higher polynomial degrees and is not itself a performance result. The
single completion ledger remains `ROADMAP.md`.

## 1. Fixed signed pivot

Use the signed matrix `H` from
[`cubic_metric.md`](../type5_focus/fixed_elongated/cubic_metric.md), with pivot
`I = (2,5,7,4)` and remaining indices `J = (0,3,6,8,9)`. Indices 8 and 9 are
the two fixed negative directions, of Gram matrix `diag(-1,-1/w)`.

Write `A=S27`, `B=S24`, `C=S54`, and `a=A*C>0`. If `M=H[I,I]`, then

```
M = [0 0 A B]       N = [0  0  C 0]
    [0 0 0 C]           [0  0 -B A]
    [A 0 0 0]           [C -B  0 0]
    [B C 0 0]           [0  A  0 0]
```

`M*N=a*Id`, and `M` has inertia `(2,2)`. Define the scaled residual

```
L_ij = a*H_ij - H[i,I]*N*H[I,j].
```

An embedded realization has `L=u*u^T` of rank one, with `u8` and `u9` not both
zero. Otherwise both negative directions would lie in the four-dimensional
pivot span; its positive part would have dimension two, placing vertices
`1,2,5,7,4` in a plane and contradicting their strict K4 condition.

Choose `k` in `{8,9}` with maximal `|u_k|`, put `l=17-k`, and set
`t=u_l/u_k`. Thus `r=L_kk>0`, `-1<=t<=1`, and

```
L_kl = t*r,     L_ll = t^2*r.                           (1)
```

Every actual realization belongs to at least one of these two charts. Ties
belong to both; no lower bound on `r` is inserted.

## 2. Eliminate all four missing slacks

For `i=0,3,6`, the pivot column `H[I,i]` has precisely one unknown entry,
respectively `S07`, `S34`, `S67`. Write it as `v_i + m_i*e_i`, where the missing
entry of `v_i` is zero. For `j=8,9`, put

```
c_ij = a*H_ij - v_i^T*N*H[I,j],
alpha_ij = -e_i^T*N*H[I,j].
```

Then `L_ij=c_ij+alpha_ij*m_i`. Equation `L_il=t*L_ik` gives

```
D_i = alpha_il - t*alpha_ik,
n_i = t*c_ik - c_il,
m_i = n_i/D_i.                                         (2)
```

These denominators cannot vanish in an embedded realization. Here is a
division-free way to identify the needed premise. With
`theta=M^-1*(H[I,l]-t*H[I,k])`, one has `D_i=-a*theta_m`, where `m` is the
missing pivot position. The kernel of `H[I+{k,l},I+{k,l}]` is
`(-theta,-t,1)`. Its adjugate is `a*r` times the outer product of that vector,
so a cofactor and the Schur complement against the negative block give

```
det G[I\{m}, I\{m}] = w*r*D_i^2/a.                     (3)
```

The left side is strictly positive by K4 `1257` for vertex 3, and K4 `1254`
for vertices 0 and 6. All factors `w,r,a` are positive. In particular the
assertions `D_i!=0` lose no actual embedding, including configurations with
vanishing nonclique brackets. Vertices 0 and 6 have the same missing pivot
position; **`D_0=D_6`**, reused explicitly by the generator.

Set `P_i=D_i*v_i+n_i*e_i` and

```
vhat_i = D_i*a*H_ik - P_i^T*N*H[I,k] = D_i*L_ik.
```

The implementation cancels the projective terms before emitting this value:
`vhat_i=alpha_il*c_ik-alpha_ik*c_il`. It is independent of `t` and has degree
at most five; leaving the uncancelled expression would obscure this useful
structure.

The remaining missing slack is determined by

```
S06 = (r*P_0^T*N*P_6 + vhat_0*vhat_6)/(D_0^2*a*r).     (4)
```

Its denominator is positive, so it is retained directly instead of being
squared a second time when clearing inequalities.

## 3. Exactly seven remaining metric equations

In addition to the two equations (1), require

```
r*(-P_i^T*N*P_i) = vhat_i^2               (i=0,3,6),
r*(D_i*D_j*a*H_ij-P_i^T*N*P_j)
    = vhat_i*vhat_j                       ((i,j)=(0,3),(3,6)).
```

These are five further equations. All entries of the residual are now
`L_ij=L_ik*L_jk/r`: the omitted mixed entries follow from (2), and entry 06
follows from (4). Conversely one can set `u_k=sqrt(r)`, `u_l=t*sqrt(r)`, and
`u_i=L_ik/sqrt(r)`. Thus `L=u*u^T`; the signed matrix has inertia `(3,2)`,
and its Schur complement against the negative block is a positive
semidefinite Euclidean Gram matrix of rank three.

The fourteen intrinsic variables and `t` are the only declared variables.
The four missing slacks and all five previous residual factors are eliminated.
The reconstructed metric is exact on the stated charts, under the K4 premise.

## 4. Complete intersection tests with signed homogeneous coordinates

The actual incidence coordinates are just

```
C_i = (G_2i, G_5i, G_4i),
G_ji = S_ji + x_j*x_i + w*b_j*b_i.
```

The rays `r2,r5,r4` are independent by strict K4 `1245`, so
`r -> (<r2,r>,<r5,r>,<r4,r>)` is an invertible linear map on spatial `R^3`.
Consequently these three coordinates preserve every affine dependence and
intersection. Vertices 2 and 5 are universal, and vertex 4 is adjacent to
every vertex except 3; **only the coordinate `G43` has a variable denominator**.
For vertex 3 the generator uses the signed homogeneous multiple
`(D3*C3,D3)`, clearing the single fraction by (2). Its weight is nonzero;
the other seven points have weight one. Thus the raw row is

```
(D3*G23, D3*G53, n3+D3*(x4*x3+w*b4*b3), D3).
```

Zero determinants and ranks are unchanged. If `c_i` are cofactors giving a
dependence among the raw homogeneous rows, the coefficients for the actual
affine points are `c_i*w_i`, where only `w3=D3` can differ from one. Therefore
only the coefficient indexed by vertex 3 needs its sign corrected. A Boolean
test on `D3>0` selects the raw cofactor sign or its reverse, and both overall
signs of a circuit remain allowed. No extra algebraic chart is introduced.
The verifier exhausts both denominator signs, every cofactor sign pattern,
and zero strata for supports two through five.

This avoids multiplying an extra degree-three factor into every determinant
containing vertex 3. Such multiplication would preserve correctness but
needlessly raise the degree of the polynomial atoms before the solver starts.

This also makes the embedding tests substantially smaller: they use three
coordinate axes instead of five. The old five-coordinate signed projection
is emitted only for the independent exact check of the reconstructed Gram
matrix; its auxiliary homogeneous weights remain positive.

All 23 clique tetrahedra are made nondegenerate by their `3 by 3` Gram
determinants, directly from their six known edge lengths. These tests have
degree at most six in intrinsic coordinates and avoid disjunctions of ten
high-degree projective minors. The following lower-support circuits are
then already impossible:

- All pairs are distinct: every graph edge occurs in a strict-area face,
  and every missing pair has an explicitly positive squared distance.
- The 55-triple theorem makes every triple with an edge noncollinear. The
  only untreated triple, `067`, contains no edge, so it has no partition
  into two disjoint simplices of sizes one and two.
- Every four-clique is affine independent by its strict Gram determinant.

The finite verifier checks these coverage facts. The default full system
therefore needs only the remaining four-point circuits and all relevant
five-point circuits. It tests all required rank minors and all cofactor
axes; rank deficiency for support five is automatic in spatial dimension
three. Thus all degeneracies remain covered. When the 55-triple
strengthening is disabled programmatically, the generator restores the
lower-support circuit tests.

The proved strict support at every vertex supplies another **233 necessary
circuit exclusions**. A finite star admits a strict supporting linear
functional exactly when its center is outside the convex hull of its
neighbors. If it were inside, a minimal representation would use at most
four neighbors, with positive coefficients. One- and two-neighbor supports
are already excluded by pair distinctness and the 55-triple theorem.
For each four- or five-point set with a vertex adjacent to every other
vertex, the generator therefore forbids the singleton-center partition
against the other three or four vertices, even when that opposite set is
not a face. There are 83 relevant nonclique four-point partitions and 150
five-point partitions; their complete finite enumeration is checked.

Canonicalizing the positive part to contain the smallest vertex is harmless,
but for a five-point support it can make the positive part have size four.
The implementation explicitly retains those parts. The same rank and cofactor
tests handle all lower-rank degeneracies. These strict-support constraints
are included even in `--relax`; that flag omits only the actual
simplex-intersection exclusions.

Rational comparisons are polynomialized with positive denominators. A general
fraction `n/D` is represented as `(n*D)/D^2`; formula (4) uses its separately
proved positive denominator. Every resulting SMT division is by a numerical
constant. The verifier checks this and checks both signs of the general
divisor transformation.

Products of denominators are tracked as products of **positive atoms**: a
whole squared nonzero divisor is one atom, and a denominator supplied by
`positive_div` is another opaque positive atom. Mixed sums and comparisons
use the least common product of these atoms, avoiding repeated powers shared
by different aliases. They never factor an atom into signed subfactors.
This distinction is necessary: `x*y` and `x*z` can both be positive while the
ordinary monomial LCM `x*y*z` is negative. The verifier includes that negative
example and repeated-alias checks. Every common product used to multiply a
comparison is positive, so inequality directions remain unchanged.

## 5. Additional whole-domain inequalities

The generator retains every baseline nearest-lift, face, contraction, cyclic
quadratic, and selected-cell condition. It also adds the 21 nonclique-triple
strictness tests and 144 strict lift-uniqueness sums from
[`coverage.md`](coverage.md). No positive numerical margin is imposed.

There is a further cyclic inequality missing from the older quadratic system.
For a universal vertex, index its link by `0,...,6` cyclically and write
`a_i=S(i,i+2)` and `b_i=S(i,i+3)`. The principal determinant on indices
`(0,1,2,3,5)` is

```
2*a0*a1*(b0*b2*b5-a0*a3*b5-a1*a5*b2).
```

The signed deficit matrix has at most two negative eigenvalues and at most
three positive ones, so this determinant is nonnegative. If `a0,a1>0`, divide
to obtain the cubic inequality. If `a0=0`, strict support and the isometry of
the three consecutive rays express ray 1 as `alpha*ray0+beta*ray2`, with
`alpha,beta>0`. Then `a1=alpha*b0`, `b5=alpha*a5+beta*b2`, and the expression
in parentheses is `beta*b0*b2^2>0`. If `a1=0`, use ray
`2=alpha*ray1+beta*ray3`; the expression becomes `alpha*b0*b5^2>0`.
Consecutive `a` values cannot both vanish. Thus all seven rotations of

```
b_i*b_(i+2)*b_(i+5)
  >= a_i*a_(i+3)*b_(i+5) + a_(i+1)*a_(i+5)*b_(i+2)
```

hold in each of the three universal-vertex gauges, including zero-slack
boundaries. All 21 are added. These reject some stored quadratic-relaxation
witnesses, but the stored F1 quadratic witness satisfies them; they alone
are not an obstruction.

Finally the exact cap Gram/SOS bounds of
[`f1_geometry.md`](f1_geometry.md) are added for cycles `014` and `356`. The
three horizontal margins are strictly positive, while the SOS remainder is
allowed to vanish. The two determinant lower bounds therefore remain weak.

## 6. One complete F1 union

`--cell F1` uses common normalized vertical variables with `b_i=z_i`. It
generates the exact metric and embedding model once at `w=10^12`, then adds
the disjunction of the five cells' phase and cap-center inequalities. The
old cell-specific physical correction is replaced by
`10^6*(b_i-offset_i)` before forming this disjunction. The metric equations
are identical in all five cells, so no copies of their variables are needed.
The common-coordinate conversion is checked against all five stored exact
phase witnesses. It does not import the hexagonal metric or its bounds.

The union is complete when **both** ratio charts have been discharged. One
chart exclusion alone does not close a cell or F1.

## 7. Reproduction and observed limits

```sh
python research/type5_completion/f1_algebra_verify.py
python research/type5_completion/f1_algebra_projective.py /tmp/type5-f1-projective --cell F1 --solver nlsat-no-factor --statistics
python research/type5_focus/solve.py 60000 /tmp/type5-f1-projective/F1-chart8.smt2 /tmp/type5-f1-projective/F1-chart9.smt2
```

The `--solver` flag selects the default solver, explicit `qfnra-nlsat`, or
`qfnra-nlsat` with its factoring preprocessor disabled. It changes only the
query command, not any mathematical constraint. `--statistics` appends the
solver statistics query so preprocessing and actual nonlinear-search work
can be distinguished in recorded experiments.

The exact verifier checks the sparse inverse, denominator cofactor identity,
elimination identities, both
zero-slack cases of the new cubic inequality, both projective charts on
constructed rational rank-three metrics, the `w=10^12` scale, recovery of all
four missing slacks, every reconstructed Gram entry using both coordinate
representations, positive homogeneous scaling for all relevant affine minors,
the signed-row correction in 50,112 sign/zero cases, the positive-atom LCM
rule including its negative-factor counterexample, finite coverage of the
omitted circuit tests, the five-cell coordinate conversion, all 233 support
tests on the exact square witness, and final SMT symbol/denominator integrity.
The constructed rational metrics
test the algebra; they are not claimed to be tori.

Initial 10-second probes of the maximal-cell necessary systems, before adding
the new inequalities and whole-F1 union, returned `UNKNOWN (timeout)` in both
charts. Those probes establish no exclusion. Record final strengthened-union
outcomes in the primary roadmap; do not interpret a timeout or generation
success as a proof certificate.

The final full-union queries each have 15 declared reals, seven metric
equations, 1,027 assertions, and 432,623 bytes. Native Z3 4.13.3.0, using
`qfnra-nlsat` with factoring disabled and a 60,000 ms timeout, returned
`UNKNOWN` with reason `canceled` for both charts. Reported times were 60.00
and 60.02 seconds; no `nlsat` search counters appeared in either result.
The available statistics are consistent with a preprocessing bottleneck;
they do not establish infeasibility or predict the time needed to decide
either chart. Exact source/query hashes, raw solver output, and all final
verification output are recorded in [`verification.json`](verification.json).
