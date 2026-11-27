# Faster certificate discovery with independent coordinate replay

The certificates in `solver_metric_quotient.json` exclude **72 complete
weak phase chambers for every `y>=8`**. Twenty-four overlap the other
proof modules, so this adds forty-eight exclusions. The verified union is now
**78 of 132 phase chambers**, leaving 54. The original marking systems
are not yet excluded in full.

The discovery calculation uses a smaller exact polynomial quotient.
The standalone verifier deliberately uses a different method: it expands
the stored identities in twenty-one formal spatial coordinates and checks
exact zero. Replay trusts no quotient construction, rank computation,
floating LP result, or numerical tolerance.

## 1. Reduce the discovery system before solving

The quadratic cone of `solver_metric_quadratics.md` has 2485 raw bracket
products and 4340 explicit affine-cocycle and GP identity rows. Translate
vertex 0 to the origin. Every raw bracket is then an alternating linear
combination of the 35 brackets containing 0:

`[abcd]=[0bcd]-[0acd]+[0abd]-[0abc]`.

There are only 630 quadratic products of these anchored brackets.
The exact Pluecker relations leave 490 free coordinates. Grouping the
relations by their seven-column multidegree makes the elimination small:
each block has at most ten columns. The resulting substitution for all
2485 raw products has 19,411 nonzero integer entries, each of magnitude
at most two. Its construction took 0.13 seconds in the recorded run.

The 420 original GP rows have rank 140 after the affine substitution,
so this representation enforces the same quadratic identities as the
earlier cone. It introduces no new geometric assumption. The discovery
LP then has 490 equality coordinates instead of 2485 raw coordinates
and thousands of redundant identity rows.

In matched recorded searches, the exact case-41 certificate producer
dropped from 22.01 seconds to 1.34 seconds. Case 55, whose separate
dual optimization had timed out after 45 seconds, produced a candidate
in 2.48 seconds. Exact active-basis reconstruction then took 0.40 seconds.
These are concrete certificate-discovery timings, not claims about
general NLSAT performance or completion of the full metric systems.

## 2. Reconstruct the rational weights exactly

An LP selects metric-product inequalities and nonnegative bracket
products. Its floating output is only a proposed support. If direct
rational reconstruction does not satisfy the identity exactly, solve
the selected active linear system over the rationals, including its
normalization. Check every recovered weight is nonnegative and every
identity coefficient is exactly zero.

For example, case 55 has 225 active variables. Its exact reconstructed
weights use 74 bits before clearing the source coefficient's denominator.
Large integer weights are acceptable: a residual of `10^-15` is not
accepted as zero, while an exact rational identity is decisive.

Some additional certificates need only two metric products. Allowing
the positive residual to occur at any proved-strict product exposes
these cases; fixing only the `0123` square had missed them. Every
certificate retained here ultimately has a positive K4-by-K4 residual,
so its final proof needs only clique nondegeneracy.

## 3. Store a universal raw identity

Each metric inequality has the form `L(B)<=0`, where `B_q=|[q]|` is a
nonnegative raw bracket magnitude. Multiplying it by another magnitude
preserves the inequality. Let `G(B)` be a positive integer-weighted sum
of these quadratic metric products.

The data stores a polynomial `I(X)` in the **raw signed brackets** that
is identically zero for all eight points in three-dimensional space.
For a chamber with signs `s_q`, replace `X_q` by `s_q*B_q` and form

`C(B)=G(B)-I(s*B)`.

The checker verifies every coefficient of `C` is nonnegative, and one
positive coefficient multiplies two nonzero K4 brackets. Consequently
`C(B)>0`, whereas `I=0` and the source metric inequalities imply
`C(B)=G(B)<=0`. This is the contradiction.

All nonclique brackets and all inequality multipliers may be zero.
No uniform lower bound on a volume or a cap edge is imposed. All
magnitudes refer to a single common raw affine frame; individually
rescaled SMT incidence definitions cannot replace them.

## 4. Independent replay in ordinary coordinates

`solver_metric_quotient.py` puts `r_0=0` and treats the other seven
points' three coordinates as twenty-one independent formal variables.
It performs three exact checks:

1. For each of the seventy raw brackets, expand
   `det(r_b-r_a,r_c-r_a,r_d-r_a)` directly and check its alternating
   expression in the anchored determinants.
2. Substitute those anchored expressions in every stored `I(X)`, then
   expand each ordinary three-by-three determinant with its six signed
   terms. All resulting integer coordinate coefficients must be zero.
3. Reconstruct each metric-product source from its verified phase
   symmetry, ordered cap pair, inequality direction, and multiplier;
   check the complete residual coefficient sum and the final K4 product.

There are at most 630 anchored quadratic products, each with at most
36 coordinate terms before cancellation. This direct universal check is
small. The standalone run checked all twenty-five stored identities, all
seventy substitutions, and all seventy-two covered chambers in 0.49 seconds
after imports in the recorded run.

```sh
python3 research/type7_completion/solver_metric_quotient.py
```

## 5. Exact reuse coverage

A reference identity may apply to more than its discovery sign model.
For every claimed reuse, the verifier applies the stored phase symmetry,
normalizes one common orientation sign, and recomputes all residual
coefficients. It relabels the positive product back to the original graph
and verifies both factors are K4s. The coverage is therefore a new exact
check for each weak chamber.

| Reference | Covered chambers | Metric products |
|---|---|---:|
| 48 | 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 48, 49, 50 | 2 |
| 55 | 55 | 32 |
| 65 | 65, 93 | 5 |
| 69 | 61, 69 | 14 |
| 71 | 71, 96 | 6 |
| 72 | 3, 4, 5, 56, 66, 72 | 14 |
| 73 | 73 | 14 |
| 76 | 76, 78, 79, 80, 81, 83, 98, 99, 100 | 8 |
| 84 | 9, 10, 11, 62, 70, 74, 84, 85 | 3 |
| 87 | 87, 88, 90, 91 | 14 |
| 89 | 89 | 15 |
| 92 | 92 | 13 |
| 94 | 94 | 15 |
| 110 | 110, 111, 116, 117 | 8 |
| 113 | 113 | 3 |
| 114 | 114 | 3 |
| 115 | 115 | 5 |
| 118 | 118 | 8 |
| 121 | 121 | 3 |
| 122 | 122 | 5 |
| 123 | 123 | 8 |
| 124 | 124 | 5 |
| 125 | 125 | 11 |
| 126 | 126 | 7 |
| 127 | 127 | 3 |

The compiler retains all earlier certificates, including independent
proofs of overlapping cases, and counts their union. Boolean model
enumeration and its independently checked coverage remain unchanged.
