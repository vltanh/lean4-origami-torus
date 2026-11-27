# Exact quadratic raw-bracket certificates

For every `y>=8`, nine stored exact certificates, reused under the
verified phase symmetries, exclude seventeen complete weak chambers:

`9,10,28,30,31,32,34,36,37,38,40,41,50,62,70,116,117`.

They are disjoint from the thirteen earlier final-polynomial and linear
metric exclusions. Those modules together exclude **30 of 132 phase
chambers**. The later [quotient certificates](solver_metric_quotient.md)
increase the compiler's verified union to 78, leaving 54. The separate product certificates also
prove chambers 28 and 36; the compiler retains both proofs without
counting those chambers twice. No full marking is excluded.

## 1. A stronger finite cone

Let `B_q=|[q]|>=0` be the seventy raw affine four-bracket magnitudes in
one common frame. The exact inequalities established in
`solver_metric_differences.md` are homogeneous linear expressions
`L(B)<=0`. They retain both sides of each absolute difference, including
cases where the two relevant weak signs agree.

For any bracket `r`, multiplication by `B_r>=0` gives the necessary
quadratic inequality

`L(B)*B_r <= 0`.

The fifty-six affine cocycle identities can likewise be multiplied by
any magnitude. The rank-four Grassmann--Pluecker identities supply
additional quadratic equalities. For common vertices `a,b` and four
other vertices `c,d,e,f`, the ordered identity is

`[abcd]*[abef]-[abce]*[abdf]+[abcf]*[abde]=0`.

Relabeling parity and the chamber signs express every factor as a
signed nonnegative magnitude. All identities remain valid when some
nonclique magnitudes vanish.

Treating the `70*71/2=2485` quadratic monomials as independent
nonnegative unknowns produces a necessary linear cone. There are 3920
affine cocycle products and 420 GP equalities. This relaxation omits
many relations among the monomials, so a feasible cone does not provide
an actual geometric realization. An exact infeasibility certificate,
however, excludes the entire original weak chamber.

## 2. What the stored certificate proves

Each JSON certificate contains positive integer weights for selected
metric products, and signed integer weights for selected exact
identities. Adding those expressions gives

`sum_{q<=r} c_{q,r}*B_q*B_r <= 0`.

The checker recomputes every rational coefficient and verifies
`c_{q,r}>=0` for every monomial. At least one positive coefficient
multiplies two K4 brackets. Both bracket magnitudes are strictly
positive, so the displayed sum is positive, a contradiction.

There is no lower bound for a K4 volume. In particular, the proof does
not infer a geometric margin from a numerical LP tolerance. Every
nonclique magnitude may be zero. Positive multipliers may also vanish;
multiplying by them remains valid. Only the final recorded K4 product
is required to be nonzero.

| Reference certificate | Covered chambers | Metric products | Cocycle products | GP identities |
|---|---|---:|---:|---:|
| 30 | 30 | 5 | 134 | 57 |
| 31 | 31 | 5 | 142 | 80 |
| 37 | 28, 32, 34, 36, 37, 38 | 4 | 12 | 5 |
| 40 | 40 | 5 | 180 | 91 |
| 41 | 41 | 5 | 92 | 50 |
| 50 | 50 | 5 | 92 | 48 |
| 62 | 9, 10, 62, 70 | 5 | 12 | 2 |
| 116 | 116 | 7 | 40 | 15 |
| 117 | 117 | 8 | 37 | 14 |

The integer weights use at most nineteen bits. The larger certificates
are still finite sums of explicit identities; they require no
nonlinear solver at replay time.

## 3. Exact reuse and symmetry

Each coverage entry records the full seventy-sign model, a verified
phase-preserving permutation, and a reference certificate. The checker
transforms the signs with the permutation parity and normalizes one
common orientation sign. It reconstructs the selected metric and
identity expressions for those signs, then checks the complete residual
again. A reference certificate may therefore cover another sign model
even when the models are not in the same full sign orbit.

This reuse is an exact coefficient check, not a new assumption about
the chamber. The two factors of the final positive product are relabeled
back into the original graph and checked to be actual K4s. No extra
edge-length normalization or independent symmetry reduction is added.

All products use **raw affine brackets in a common frame**. Individually
rescaled sign-only incidence definitions from an SMT query are not
valid substitutes for these magnitudes.

## 4. Replay and scope

```sh
python3 research/type7_completion/solver_metric_quadratics.py
```

The standalone verifier symbolically expands the underlying determinant
comparison, the generic affine cocycle, and the generic GP identity.
It checks the uniform rational constants, reconstructs every selected
source expression, validates the phase permutations, and adds the
integer-weighted expressions using exact `Fraction` arithmetic. It
imports no LP solver and uses no floating-point tolerance.

The discovery screen considered 119 chambers after the earlier thirteen
exclusions. Some floating solver results could not be turned into exact
certificates; those results are not included in this proof. The supplied
data records only the independently replayed exact certificates and
their exact reuse coverage. At `1/8`, every metric comparison is valid
for the full range `y>=8`.

The chamber compiler retains all 132 representatives and the unchanged
1888-model Boolean coverage. It omits a metric query only when one of
the exact exclusion checkers succeeds. These seventeen exclusions are
additional progress inside the ray-3 phase system, not a complete
marking exclusion or a Type-7 closure.
