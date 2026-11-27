# Finite chamber compilation for the full ray-3 search

The full ray-3 search now has **119 remaining metric chambers**. Exact
Boolean enumeration covers 1,888 generic sign completions, and verified
phase symmetries reduce them to 132 representatives. Two complete weak
chambers are excluded by Grassmann–Plücker final polynomials; two more
are excluded by a metric volume comparison and an affine identity. Nine
further chambers are excluded by exact weighted sums of raw-volume
difference bounds and affine identities. The exclusions retain actual
zero nonclique minors.

The compiler removes all Boolean variables and almost all actual circuit
tests. Its optional face chart uses **29 real variables and 21 quadratic
metric equations**, instead of the direct chart's 27 variables and
19 equations of degree at most four. The direct compiled queries have
297–311 assertions and 92–108 kB, compared with 9,140 assertions and about
820 kB in the uncompiled direct query. The face-chart queries have **310–324 assertions and 80,808–95,178
bytes**, after positive factor cancellation and linear area alternatives.

Enumeration is approximately four times faster and its complete model
set is unchanged. Representative nonlinear trials still returned
`UNKNOWN (timeout)` at 3,000 ms. The thirteen exclusions below have exact
certificates independent of those trials. **The full ray-3 marking
remains open.**

## 1. Compile the topology once

[`solver_chambers.py`](solver_chambers.py) enumerates the necessary
orientation formula with both horizontal unlinkings and
`|lk(0246,1357)|=2`. There are exactly **1,888 normalized 70-sign models**.
The producer now blocks an entire verified 16-symmetry phase orbit per
SAT result. This reduces the enumeration from 1,889 SAT checks to **133**;
the measured enumeration time fell from **7.61 seconds to 1.83 seconds**.
The sorted 1,888-model set and exported coverage CNF were checked to be
byte-for-byte identical. Enumeration need not be repeated for each
metric query or domain cell.

The generator appends one blocking clause per model and exports a CNF
and an RUP trace. The independent C++ checker
[`solver_check_rup.cpp`](solver_check_rup.cpp) uses no solver library and
accepted:

```text
PASS UNSAT: 10267 original clauses, 12565 checked input lines,
67473 RUP additions, 65982 deletions
```

The checker verifies every logged input clause against the original
formula or by reverse unit propagation. The solver is only a producer
of the trace. A separate exact Python replay evaluates every primary
orientation model, mixed-face witness, and linking number directly.

## 2. Use the correct marked symmetry group

The graph and marked metric have 32 symmetries. For each, the generator
checks the entire edge-cocycle identity

\[
K_{p(i)p(j)}=A K_{ij}+g_j-g_i.
\]

The four possible matrices `A` are exact lattice isometries for every
`1/2+i*y`. The verifier checks both coefficients of the identity
`Aᵀ Q(y) A = Q(y)`, so this is not a numerical test at one height.

Only **16 symmetries preserve the canonical cap partition**
`{0145,2367}`. They reduce the 1,888 models to **132 chambers**. Using all
32 would produce 66 orbits but would also identify the two phase
endpoints; imposing canonical phase 0 on those 66 representatives alone
is not a valid cover. The generator retains the correct 132.

The same 16 symmetries act transitively on the eight undirected short
edges. Thus a separate search can normalize `01` to a longest short
edge, obtaining `h01>=1/4` and `px1>3/16`. This normalization is **not**
imposed on the 132 sign representatives: choosing a sign representative
and choosing a longest edge independently would reuse the same
relabeling freedom and could discard solutions.

## 3. Prove more brackets nonzero, then remove redundant circuit tests

Every chamber starts with the 16 nonzero K4 brackets. Two sound rules
increase the strict set to **64–69 brackets** while retaining weak signs
on the others.

**Cofactor rule.** Suppose a candidate four-bracket vanishes. Add a fifth
vertex for which another cofactor is already nonzero. The five affine
columns have rank four. Their alternating cofactor relation has zero
coefficient at the added vertex and the prescribed weak signs at the
remaining four. If the positive and negative parts are disjoint
simplices, their convex hulls intersect. If one part is a vertex and
the other consists of its neighbors, strict neighbor support is
contradicted. If one part is empty, the affine coefficients cannot sum
to zero. In each situation the candidate bracket must be nonzero.

**Grassmann–Plücker rule.** The prescribed signs turn each three-term
identity into `A+B=C` with nonnegative products of bracket magnitudes.
If both factors of either summand are already nonzero, `C>0`, so both
factors of `C` become nonzero. This rule does not assume all brackets
are generic.

Each new strict bracket has an explicit witness. The independent
[`solver_verify.py`](solver_verify.py) replay checked **6,608 such
witnesses** across the 132 representatives.

The original 524 minimal-circuit tests divide into 144 three-point,
236 four-point, and 144 five-point partitions. Their reduction is exact
for actual placements in the chamber:

- All three-point supports lie in a proved nonzero four-bracket, so
  they cannot be collinear minimal circuits.
- A four-point support with a proved nonzero bracket cannot be a
  coplanar minimal circuit.
- A minimal five-point circuit has all five cofactor brackets nonzero.
  Their weak chamber signs then become the prescribed strict signs,
  which already forbid every disjoint-simplex partition in the generic
  orientation formula.

Only **2–16 four-point circuit partitions per chamber** remain. Those
tests are emitted in full, including every zero-bracket boundary and
each two-dimensional cofactor projection. Positive pair distances are
also retained. The verifier checked all 67,736 omitted circuit tests
across the 132 chambers. It does not simply replace nongeneric
intersection tests by a generic sign assumption.

## 4. Remove redundant metric work

The four cap diagonals previously had 63 lattice-image contraction
inequalities each. Only these two images per diagonal are necessary:

| Diagonal | First lattice shift | Second lattice shift |
|---|---|---|
| `04` | `(0,0)` | `(1,0)` |
| `15` | `(-1,0)` | `(0,0)` |
| `26` | `(0,-1)` | `(1,-1)` |
| `37` | `(-1,0)` | `(0,0)` |

To see that the other 244 inequalities are redundant, let `H` be the
horizontal displacement along the directed two-edge cap path. The
relative bounds and the cap period give `-1<H<0`. The two listed images
have horizontal displacements `H` and `H+1`; one has magnitude at most
`1/2`, and every other horizontal image is farther. The gamma displacement
`g` along the same diagonal satisfies

\[
|g|<\tfrac12(\tfrac12+y^{-2}).
\]

For a nonzero vertical integer `k`, the change in squared vertical
distance is `y^2*k^2+2*k*g`, which is at least `y^2-2|g|`. For `y>=8`
this exceeds `1/4`, so even a zero horizontal displacement in the other
image cannot beat the nearer listed image. Equality in the retained
contraction inequalities is permitted.

The generator also proves symbolically that the total oriented double
face area for this fixed cocycle is identically **−2**. It therefore
replaces the two orientation branches and redundant sum equations by
the sixteen individual negative-area inequalities. Duplicate K4
nonzero tests are absorbed into the corresponding strict chamber signs.

## 5. Thirteen complete weak chambers are excluded

[`solver_final_polynomials.py`](solver_final_polynomials.py) excludes
chambers **23 and 131**. Each proof uses six signed Grassmann–Plücker
relations. Already verified nonvanishing makes every compared factor
positive; four of the six comparisons are strict. Multiplying them
cancels the same twelve bracket magnitudes on both sides, yielding a
strict contradiction. The two remaining comparisons allow equality,
so a zero cap minor is not silently discarded.

[`solver_metric_certificates.py`](solver_metric_certificates.py) excludes
chambers **129 and 130** at every `y>=8`, and gives a second proof for 131.
The needed signs are

`0123:+, 0127:-, 0137:+, 0237:+, 1237:-`.

Write `Bijkl` for the absolute value of the **raw** affine bracket in one
common coordinate frame. The five-point affine identity gives

`B0237+B1237 = B0123+B0137+B0127`.

A phase-symmetry image of the uniform metric comparison gives

`B0237+B1237 <= (8/y^2)*(B0123+B0137)`.

The first sum on the right is positive because `0123` is a nonzero K4
bracket, while `8/y^2<=1/8<1`. This is a contradiction. The checker
verifies the determinant identities, constants, symmetry, and five
signs exactly. A numerical linear program helped discover the proof;
its output is not trusted by the replay.

The magnitude inequality applies to raw brackets before the query's
individual positive rescalings. Those rescalings preserve signs and
zeros, but not affine identities between magnitudes. The certificate
checker keeps these two uses separate.

The [general difference certificates](solver_metric_differences.md) add
chambers **88, 91, 93, 95, 96, 97, 98, 99, and 100**. They use the same
absolute raw-bracket difference bound when the two left signs agree as
well as when they oppose. Each exact certificate adds 6–7 metric
inequalities and 11–16 affine identities with integer weights. The
result has nonnegative coefficients on all bracket magnitudes and a
strictly positive coefficient on a nonzero K4. The standalone checker
reconstructs every source inequality and adds its coefficients with
rational arithmetic; no LP tolerance is used. These nine cases hold at
every `y>=8` and leave 119 chambers.

## 6. Lower the metric degree and cancel positive factors

[`remaining_null_chart.md`](remaining_null_chart.md) gives the exact
face-023 coordinate construction and its verification. Fixing the actual
nondegenerate face to its intrinsic plane cancels the common long-edge
term. This leaves 21 quadratic equations in 29 real variables, including
three anchor-distance differences. All coordinates have uniform bounds.
No cap area or edge length is assumed bounded away from zero.

Eight incidence minors admit strictly positive anchor factors. Dividing
those factors out preserves every sign and zero test. Six of the 24
relative-area alternatives become linear inequalities after cancellation
of the positive length of edge 23. The full face query also omits 24
phase tests already implied by the stronger coordinate bounds.

Use `--chart face` to select this formulation. It changes the continuous
metric equations only; the same certified orientation cover, weak signs,
nonvanishing witnesses, and retained actual circuits apply. A fresh full
face-query generation, including the coverage trace, completed in 8.03
seconds while other proof work ran concurrently.

## 7. Reproduce and use

Run from the repository root, with assertions enabled:

```sh
python3 research/type7_completion/remaining_null_verify.py
python3 research/type7_completion/solver_chambers.py /tmp/type7-chambers --proof --queries --chart face
python3 research/type7_completion/solver_verify.py /tmp/type7-chambers
g++ -O3 -std=c++17 research/type7_completion/solver_check_rup.cpp -o /tmp/type7-rup-check
/tmp/type7-rup-check /tmp/type7-chambers/coverage.cnf /tmp/type7-chambers/coverage.drat
```

The generated manifest records every model, exact symmetry and gauge,
strictness witness, remaining circuit partition, exclusion certificate,
and query size. It retains all 132 rows and emits 119 queries, omitting
the thirteen cases carrying verified exclusion certificates. Regeneration removes stale query files for
these excluded chambers.
Generated files and large proof traces stay outside the source tree.

The first targeted trials used chambers 0, 41, and 15, representing
different retained-circuit counts. All returned normal `UNKNOWN` with
the 3,000 ms limit; wall times were 3.57–3.77 seconds. Three alternative
NLSAT parameter configurations on chamber 41 also returned `UNKNOWN`
with cancellation. There is no reason to repeat unchanged timeouts across the remaining chambers.
A further metric inequality, elimination, or exhaustive interval
certificate must make the continuous part decidable.
