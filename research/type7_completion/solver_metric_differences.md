# Nine further exact metric exclusions

For every `y>=8`, the exact certificates in
`solver_metric_differences.json` exclude the complete weak phase chambers
**88, 91, 93, 95, 96, 97, 98, 99, and 100**. They retain zero values for
all nonclique brackets. Together with the two final-polynomial exclusions
and the earlier five-sign metric obstruction, thirteen of the 132 phase
chambers are excluded and 119 remain. No full marking is excluded.

## The additional inequality

The raw determinant identity established in
`solver_metric_certificates.md` gives, before imposing signs,

`|[0ij2]-[0ij3]| <= 8/y^2*(|[023i]|+|[023j]|)`

for each pair `i,j` from `{1,4,5}`. The same coordinate bounds and
positive anchor-factor cancellation prove this comparison. It applies
to all sixteen verified phase-preserving marked metric symmetries.
At `y>=8`, its coefficient is at most `1/8`.

When the two left brackets have opposite weak signs, their difference
has magnitude equal to their magnitude sum. That was the earlier
five-sign obstruction. When their signs agree, the comparison instead
bounds the difference of two nonnegative magnitudes. Those additional
relations control their relative scales and yield the new certificates.

All quantities are **raw affine brackets in the same coordinate frame**.
The separately rescaled sign-only minors in a generated SMT query must
not be substituted as magnitudes into these inequalities or cocycles.

## The finite exact certificate

Write `B_q=|[q]|>=0` for every sorted four-tuple `q`. Each allowed source
permutation and pair gives two linear inequalities in these seventy
magnitudes, one for each side of the absolute-value comparison:

`+([0ij2]-[0ij3])-(B023i+B023j)/8 <= 0`,

`-([0ij2]-[0ij3])-(B023i+B023j)/8 <= 0`.

The chamber sign and relabeling parity express each signed ordered
bracket as `+B_q` or `-B_q`. The fifty-six five-point affine cocycles
provide exact linear equalities in the same magnitudes. Each stored
certificate supplies positive integer weights for some metric
inequalities and signed integer weights for some affine identities.
Their sum is

`sum_q c_q*B_q <= 0`,

where every rational coefficient `c_q` is nonnegative. A recorded K4
bracket has a strictly positive coefficient. Its actual magnitude is
strictly positive, so the sum cannot be nonpositive.

| Chambers | Metric comparisons | Affine identities |
|---|---:|---:|
| 88, 91, 93, 95 | 6 | 11 |
| 96, 97 | 7 | 12 |
| 98, 100 | 6 | 16 |
| 99 | 6 | 13 |

All weights are integers of at most sixteen bits. Their values, source
permutations, ordered cap pairs, chosen inequality directions, and
cocycle supports are included in the JSON certificate file. No bound
away from zero for an unknown edge length or a nonclique bracket is
used. The only strictness premise is the nondegeneracy of one recorded
K4 in each certificate.

## Reproduction

```sh
python3 research/type7_completion/solver_metric_differences.py
```

The standalone verifier checks the underlying determinant identities
and rational constants, reconstructs each inequality from its ordered
source vertices, verifies every source symmetry, recomputes the affine
cocycles, and adds all coefficients with exact `Fraction` arithmetic.
It checks both coefficientwise nonnegativity and the actual graph edges
of the strict K4. It imports no linear-programming solver and accepts no
floating tolerance. The LP was used only to discover the weights.

The chamber compiler records the verified certificate and omits the
corresponding nonlinear query. Manifest replay checks the same exact
certificate against the primary model and the verified metric symmetry
group. All 132 representatives remain in the manifest so that the
independently checked enumeration coverage is unchanged.
