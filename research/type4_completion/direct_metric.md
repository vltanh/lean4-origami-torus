# A complete quartic formulation with cubic intersection tests

**Status: the full `ray2_2` domain remains open.** The new formulation has
26 real variables, every polynomial has degree at most four, and every
intersection/support test uses cubic affine brackets. It includes all
weak boundary strata. Its bounded exact-solver attempt returned
`UNKNOWN (timeout)`; no case exclusion is claimed.

This is an equivalent formulation of the complete continuous problem.
It retains the baseline marking and cell conditions, with the complete
geometric coverage implication in
[ray2_attack_coverage.md](ray2_attack_coverage.md). The strict-support/K4
premises now have the direct Type 4 hand proof in
[global_attack_support.md](global_attack_support.md); they are not newly
formalized in Lean by this implementation.

## 1. Affine coordinates preserve every realization

Use the strict anchor `(4,5,1,6)` and set

    z4=0, z5=(1,0,0), z1=(0,1,0), z6=(0,0,1).

There are fourteen intrinsic coordinates `p_i=(x_i,b_i)`, with `p4=0`,
and three affine coordinates for each of `0,2,3,7`: 26 unknowns in total.
The physical intrinsic norm is `x^2+W*b^2`, with `W=10^12`.

The six intrinsic anchor edge lengths determine the three-by-three Gram
matrix `G` of the spatial basis `(r5,r1,r6)`. Require `G` positive definite.
Then the spatial metric is exactly

    D_ij=(z_j-z_i)^T G (z_j-z_i).

Every embedded realization admits these coordinates because its anchor is
strict. Conversely, a positive-definite `G` can be realized by a Euclidean
basis, and these coordinates determine actual spatial vertices. Neither
direction assumes a quantitative lower bound on the anchor volume.

The six anchor edge equalities are identities. Four radial equations
at vertices `0,2,3,7` impose `z_i^T G z_i=d_4i`. Polarizing the other
fourteen edge equations gives

    z_i^T G z_j=(d_4i+d_4j-d_ij)/2.

Ten of these are cubic because one endpoint is a fixed anchor; four
are quartic. Together with the four radial equations there are
**ten cubic and eight quartic metric equations**. Their equivalence to
the original distance equations follows from the exact residual identity

    (D_ij-d_ij)=(D_4i-d_4i)+(D_4j-d_4j)
                  -2*(z_i^T G z_j-(d_4i+d_4j-d_ij)/2).

All four nonedge chords and their slacks are derived quantities. Thus
the four old free nonedge slacks and five signed-Gram auxiliary variables
are absent.

## 2. The anchor positivity test is also quartic

Let the physical marking shift on edge `15` be `(k,n*y)`. It is `(1/2,y)`
in marking 1 and `(1,0)` in marking 2. In both cases the shift on `56`
is its negative and the shift on `16` is zero. Define

    C=k*x5+W*n*b5+(k^2+W*n^2)/2,
    Delta=x1*b6-x6*b1,
    E=(x5+k)*(b6-b1)+(b5+n)*(x1-x6),
    F=(x1-x6)^2+W*(b6-b1)^2,
    Q=-2W*Delta^2+2W*Delta*E-C*F.

The exact polynomial identity is

    det(G)=C*Q.

To derive it, view the intrinsic vectors `p1,p6` in their two-dimensional
metric and write `u=p5+(k,n)`. The two mixed spatial Gram entries are
`p1.u-C` and `p6.u-C`. Their two-by-two intrinsic Gram determinant is
`W*Delta^2`. Expanding the three-by-three determinant gives the displayed
factorization. The expansion is a polynomial identity, so it remains true
when `Delta=0`; no division by `Delta` is needed.

Moreover `2C=|p5+(k,n)|^2-|p5|^2>0`: the radial edge `45` has its
strictly shortest lift. Hence `det(G)>0` is equivalent to `Q>0` under
the existing nearest-lift condition. The generator records `C>0`
explicitly and uses the first two Sylvester minors together with `Q>0`.
These tests have degrees at most four. Small `C` and arbitrarily small
positive anchor determinants remain allowed.

The original determinant has actual total degree five after cancellation;
the naive expansion of its quadratic entries has degree-six terms which
cancel. Removing the known positive factor lowers the actual degree by one.

The checker proves the factorization symbolically for both markings,
with all six intrinsic anchor coordinates and `W` indeterminate. It also
checks that **every polynomial in the fully expanded generated domain
has degree at most four**.

## 3. Cubic circuits include all degeneracies

For four labels, the affine bracket of their `z` coordinates is cubic.
For any five labels, its five alternating four-brackets form an affine
dependence. If its nonzero coefficients have sign parts `A,B`, their
convex hulls intersect. To exclude an intersection of disjoint simplices,
forbid both sign orientations with strict signs on `A,B` and exact zeros
on all remaining labels.

This test is complete even for intersections with support smaller than
five. Any prohibited intersection has a sign-compatible minimal affine
circuit on `k<=5` vertices. Its homogeneous affine rank is `k-1`.
The fixed anchor spans homogeneous rank four, so append `5-k` vertices
from that anchor to obtain five distinct labels of rank four. The unique
dependence then has exactly zero coefficients at the appended vertices.
Its other coefficients are the original circuit. One of the generated
five-point tests therefore detects it.

Consequently the extra zero-coefficient labels need only come from the
fixed anchor. This reduces the embedding clauses from 5,810 for arbitrary
extensions to **1,666** without changing their content. Coincident points,
collinear triples, coplanar quadruples and simultaneous nonclique zeros
are retained in the formula until an actual forbidden intersection
excludes them. No general-position hypothesis is added.

The 23 clique tetrahedra are required to have nonzero affine brackets.
Because `G` is positive definite, their augmented Gram determinants equal
`det(G)` times the squares of those brackets, so this is equivalent to the
baseline strict clique determinant test.

## 4. Proven geometric cuts

The direct Type 4 strict-support theorem excludes a vertex from the
convex hull of its neighbors. Apply the same complete circuit test to a
singleton on one side and up to four neighbors on the other. After
omitting clauses already supplied by simplex nonintersection, this adds
**824 cubic support clauses**. They require no auxiliary normals and no
genericity assumption.

The optional `--mixed-faces` flag adds **eight finite disjunctions**:
at each vertex, some incident face must have other neighbors on both
strict sides of its plane. Here is the geometric justification. Strict
support puts the spherical link in an open hemisphere. Central projection
onto the supporting affine plane takes its shorter great-circle arcs to
line segments and gives a simple closed polygon; overlapping arcs would
contradict local embeddedness of the spatial star. If every polygon edge
has all other vertices weakly on one side, this polygon is convex, allowing
collinear subdivisions. It cannot be entirely collinear because it is a
simple closed polygon. Its spherical counterpart is a convex curve in an
open hemisphere and has length strictly less than `2*pi`, by the spherical
Crofton formula. This contradicts the flat vertex's link length `2*pi`.
Thus one incident face has neighbors on both strict sides. This proof
uses the new direct strict-support result and does not delete a vertex
or retriangulate its star.

All face-side tests use cubic brackets with checked permutation parity.
The parent inequalities and cuts remain valid throughout the finite cell,
including every cap-collapse and strip-endpoint regime.

## 5. Exact verification and reproduction

    python3 research/type4_completion/direct_metric_check.py
    python3 research/type4_completion/direct_metric.py /tmp/type4-ray2-direct-pruned.smt2 --case ray2_2 --mixed-faces --solve-ms 10000

The committed checker verifies the symbolic physical metric identity;
the actual emitted rational anchor, chord and bracket expressions; all
eighteen emitted polarized edge equations against nontrivial rational
intrinsic/spatial data; both determinant factorizations; the degree bound;
and preservation of every baseline prefix assertion. In the polarized
equation check, a rational spatial anchor realizes the six anchor edges
exactly, while arbitrary outside coordinates leave generally nonzero
residuals. Thus the test checks the residual identity, not just a solution
where both sides happen to vanish.

It also compares the five-point encoding with an independent rational
nullspace oracle operating directly on minimal supports of sizes two
through five. The fixtures include coincident, collinear, coplanar and
simultaneously degenerate positions. Both embedding and support circuit
sets agree. A separate independent audit checked 25 rational configurations
and reviewed the full-domain correspondence and mixed-face argument.

For the final `ray2_2` input:

| Quantity | Value |
|---|---:|
| Real variables | 26 |
| Assertions | 2,845 |
| Metric equations | 18: ten cubic, eight quartic |
| Complete embedding clauses | 1,666 |
| Additional strict-support clauses | 824 |
| Mixed-face disjunctions | 8 |
| Maximum polynomial degree | 4 |
| Formula bytes, excluding `(check-sat)` | 275,993 |
| Input file bytes, including `(check-sat)` | 276,005 |

The exact input SHA-256 is

    464b0993c5e882a076d87895cb9a95aaf5045e96a1245d6a6b92e822b7e5ea31

Solver: `libz3.so.4`, full version **4.13.3.0**, logic `QF_NRA`, configured
limit **10,000 ms**. The result was **`UNKNOWN`**, with reason **`timeout`**.
No further solver escalation was attempted after this pruned query.

Two developmental forms were also queried at the same limit and returned
`UNKNOWN (timeout)`: direct distance equations without the support cuts
(input SHA-256 `9725d2762d83ce3b5621c3a840f726b728580441fd187e86d8a049a44282b89e`),
and polarized equations before the determinant factorization and cuts
(`3bf73181b59871730909df22024eb56e38a50a1f6ae524a95fe1b60c2fe88b66`).
These are recorded attempts, not certificates. The current generator
produces the final quartic version above.

The previous full signed-Gram formula used 23 variables, 890 assertions
and 406,079 formula bytes, with higher-degree incidence determinants.
The new input has more variables and Boolean clauses, lower polynomial
degree and fewer bytes. **No runtime improvement or feasibility conclusion
has been established.** The remaining task is an exact contradiction on
the entire full domain, or a certified embedded full torus.
