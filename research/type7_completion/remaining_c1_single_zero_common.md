# Completing the common-line reduction for ray-2 C1

In the EB and ED zero-edge orbits, every interior ray-2 C1 limit
whose cap directions are parallel has **all eight transverse vertices
on one common line through zero**. Combined with the
[nonparallel exclusion](remaining_c1_single_zero_nonparallel.md), this
removes the parallel-lines-with-different-offsets possibility as well.

The twenty source CNFs below retain every actual zero minor and impose
no comparison between collapse rates. They reduce the configuration
to scalar families; they do not exclude those families.

## 1. An off-line vector would make finite nesting impossible

Use the preceding notation

\[
P=P_2=P_3,\quad U=P_4-P_3,\quad
P_5=bP+(1-b)P_6+R.
\]

The two cap vectors have norm `1/2`; parallelism therefore says
`U=epsilon V` with `epsilon in {-1,+1}`. Both P6 and P7 lie on
the V-line, and are distinct and nonzero in EB and ED. Suppose
that at least one of P,R is off that line.

If A is inside B, the upper-cap triangle-plus-backtracked-segment
argument of the preceding proof applies. Besides forcing R parallel
to U, it forces

\[
aP+(1-a)P_6\quad\text{parallel to }U.
\tag{1}
\]

For completeness, its outer segment has endpoints
`H=((s-a)/(1-a))P` and `J=((s-a)/(1-a))(P+U)`.
The inner point `Y=(1-s)P6+s(P+U)` tends to `P+U` and hence is
outside the shrinking outer triangle for s sufficiently close to one.
Winding stability puts Y on that segment. The exact identity

\[
Y-J=\frac{1-s}{1-a}\,[aP+(1-a)P_6+aU]
\]

gives (1). Since P6 and U already lie on the V-line, it makes P
lie there too. This contradicts the assumed off-line vector.

If B is inside A and P is off the V-line, its critical triangle
is nondegenerate. The complete unequal-height tracking and nine
equal-height matching arguments from the preceding proof apply
without change: they use only that U is nonzero and P6,P7 are
distinct and nonzero, not independence of U,V. They exclude nesting.

If P is on the V-line, its critical triangle is a segment of
perimeter one. Convex perimeter equality forces the entire outer A
section at that height onto the same segment. At least one of its
vertices contains P5 with a strictly positive coefficient; all its
other terms lie on the V-line. This makes R lie on that line too,
again contradicting the assumption. The coefficient is `a/b` below
b, one at b, or `(1-a)/(1-b)` above b, all positive.

Thus no off-line configuration permits finite nesting. The relative
unit edge direction from the
[short-edge theorem](remaining_c1_short_edges.md) consequently satisfies

\[
w=\lim(P_3-P_2)/h_2=2\eta U,\qquad \eta\in\{-1,+1\}.
\tag{2}
\]

Otherwise the finite plane 234 has an `O(1/y²)` height gradient,
can be flattened by a vanishing shear, and forces precisely the
finite nesting just excluded. This repeats the verified relative-scale
argument of the preceding two zero-edge packages.

## 2. P cannot be off the common cap direction

Assume first that P and V are independent and orient the plane so
that `P cross V>0`. The seventy normalized determinants are the
same source-bound forms as in the preceding package: divide by h2
exactly when the determinant contains the pair 23.

The actual cross products satisfy

\[
U\times V=0,\quad P\times U=\epsilon(P\times V),
\quad U\times R=\epsilon(V\times R).
\tag{3}
\]

The first eight CNFs cover the two orders, two choices of epsilon,
and two choices of eta. Each retains the full generic source,
rank-two relations, and the normalized determinant trits. The
nonparallel orientation unit of the preceding algebra model is
explicitly replaced by (3) and the positive `P cross V` normalization;
no embedding/linking clause is removed. Uniform coefficient signs
omit the same one variable-sign relation in EB and none in ED.

All eight formulas are UNSAT. Therefore P lies on the V-line.

## 3. Exactly three possible scalar anchor formulas

The first closed circle now gives its Cauchy equality cases.

For EB put `r=h0`. The ray-2 weight budget and nearest lifts give
`r+ell<=1/2`. Its strict-circle identity is

\[
\rho^2-[a/2-(1+a)r]^2=4ar(1/2-r),
\qquad \rho=a/2+(1-a)r.
\]

Since P,V are parallel, the left side is zero. The value `r=1/2`
is impossible because `ell>0`, so `r=0` and **P=V**.

For ED put `p=1/2-h0`, where `0<=p<=k`. Its Gram difference is
equation (4) of the preceding proof. Since
`1-2(1-a)k>0`, parallelism gives `p=0` or `p=k`. Therefore

\[
P=\chi V,\qquad
\chi=\begin{cases}
1,&\text{EB},\\
[1-2(1-a)k]/a,&\text{ED with }h_0=1/2-k,\\
-1/a,&\text{ED with }h_0=1/2.
\end{cases}
\tag{4}
\]

The positive ED coefficient is `(1-2k)/a+2k>0`. Both original
circle identities and all displayed endpoint coefficients are
checked exactly.

## 4. R cannot be off the common cap direction

If R is off that line, the finite-nesting obstruction in Section 1
again supplies (2). Orient the transverse plane so that
`V cross R>0`, and divide all cross products by this positive number.
Equations `P=chi V`, `U=epsilon V` then give the exact six-vector
cross data

\[
(P\times U,P\times V,P\times R,
 U\times V,U\times R,V\times R)
=(0,0,\chi,0,\epsilon,1).
\]

The remaining twelve CNFs cover the three values in (4), the two
cap directions, and the two virtual directions. For each case the
checker substitutes the displayed crosses into all seventy normalized
determinants, multiplies by the positive a to remove its denominator,
and verifies the exact factorization and uniform sign of every factor.
**No variable-sign determinant is omitted.** Zero determinants impose
no generic sign. Each resulting strict-minor formula is UNSAT.

Thus R is on the same line. The coordinate formula for P5 and all
the other vertex formulas now put every transverse point on that
line through the origin.

## 5. Combined reduction and remaining gate

The complete six-orbit cover for an interior ray-2 C1 limit with a
zero cap edge is now:

| Orbit | Completed necessary conclusion |
|---|---|
| EA, EC | Common line, from the original zero-edge reduction |
| EB, ED | Common line, from this proof and the nonparallel exclusion |
| EF | Common line, from the opposite-zero and scalar reduction |
| EE, FF interior parameter | Excluded by the same-zero proof |
| EE, FF parameter endpoints | Common line, from the scalar reduction |

Thus **every surviving interior ray-2 C1 limit lies on a single
common transverse line**. Positive cap edges were already excluded.
The remaining task within this component is to classify and exclude
the scalar zero-edge families and their possible normal deformations.
No height endpoint or ray-2 C0 case is included in this conclusion.

```sh
python research/type7_completion/remaining_c1_single_zero_common.py /tmp/type7-c1-single-common
python research/type7_completion/solver_cnf_certificates.py /tmp/type7-c1-single-common-rup \
  --checker /tmp/type7-rup-check /tmp/type7-c1-single-common
```

All twenty CNFs require independent replay. The source checker reuses
the exact original section, circle, independent short-edge, and
normalized determinant bindings from the preceding packages.
