# Shared ray-1/2 finite sign compiler and quadratic face charts

## Result and scope

The two remaining markings have the same necessary generic orientation
and linking formula. Its complete normalized projection consists of
**18,080 assignments to the 70 four-point signs**. The finite-domain SAT
backend enumerates the same set in **3.951 seconds**, compared with
**121.338 seconds** for the existing general incremental SMT backend in a
matched local run. Both use whole-orbit blocking and make 1,151 solver
calls. The change is the Boolean backend, not a larger timeout.

The compiler groups the signs by the 16 necessarily strict K4 brackets.
After the finite gap-hull separation for each of the seven masks, there
are **1,436 branches per marking**, with only **3–50 actual circuit
conditions** in each branch, compared with 524 in the full source query.
A decision diagram of **51–148 nodes** retains all other generic sign
choices. It replaces 382 unknown Boolean variables, 8,305 clauses and
the explicit linking arithmetic with definitions in the actual minors.
Every possible zero of a nonstrict minor remains allowed.

The independent verifier checks all primary sign and linking conditions,
56,056 strictness witnesses, every branch's exact generic model set, and
every omitted circuit. A separate RUP replay certifies that the model
list is complete. The full quadratic face chart and the generated
branch formulas are also checked independently.

This is a necessary formulation. **No ray-1/2 marking or mask is excluded
by this compiler**, and no nonlinear solver decision is claimed here.

## 1. Shared Boolean formula and checked symmetries

Both archived markings have the same twelve disjoint horizontal triangle
pairs. Their linking numbers vanish. The alternating rings 0246 and
1357 have linking number in `{-2,-1,1,2}`; magnitude one has not been
proved for these markings and is not imposed.

Together with the existing orientation, acyclicity, strict-support,
mixed-side and simplex constraints, the counter encoding has 479 Boolean
variables and 8,607 clauses. The first 70 variables are the four-subset
signs, in lexicographic order. Global reflection normalizes `[0123]>0`.

The compiler checks all sixteen vertex permutations that preserve the
face complex, the twelve unordered unlinking pairs and the two long
cycles up to reversal, cyclic order and exchange. Their normalized action
has 1,150 orbits on the 18,080 sign assignments. The SAT producer blocks
an entire orbit after each satisfying result.

**These symmetries quotient only the shared topological enumeration.**
The compiler does not use them to quotient metric branches, change a
canonical finite mask, or assert a metric gauge. This distinction avoids
discarding a marked metric case through an unproved symmetry.

`solver_sat.py` selects Z3's `QF_FD` solver for these purely Boolean
clauses. Z3 is a producer. The completeness certificate consists of the
base CNF together with all 18,080 model-blocking clauses and an UNSAT
trace. `solver_remaining_verify.py` checks that `coverage.cnf` is exactly
that clause multiset, so an unrelated UNSAT file cannot certify a model
list. `solver_check_rup.cpp` separately checks every accepted proof step.

## 2. Finite gap separation

Section 2 of `../type7_focus/remaining_markings.md` proves, uniformly for
`y >= 10^6`, that the large cyclic steps have exactly two components,
separated by two gaps of small steps. All vertices along either gap lie
within normalized distance 0.009 of its endpoint. Across a large
component the normalized displacement exceeds 0.346, so the two entire
gap hulls have distance greater than 0.32.

This proves separation of the entire gap vertex sets, not just a selected
pair of triangles. For each five-subset meeting both gaps, the compiler
forbids the Radon sign partition that would place a convex combination
from one gap in the other. Strict separation survives the small generic
perturbation used for the orientation formula. The two clauses for each
such subset therefore hold for a compatible generic sign assignment.

| Mask | Gap vertex sets | Additional clauses | Sign models | K4 branches |
|---|---|---:|---:|---:|
| 03 | 123 / 45670 | 110 | 8,578 | 162 |
| 04 | 1234 / 5670 | 112 | 9,566 | 156 |
| 014 | 234 / 5670 | 42 | 12,278 | 207 |
| 015 | 2345 / 670 | 42 | 12,278 | 207 |
| 025 | 345 / 670 | 12 | 13,102 | 222 |
| 0125 | 345 / 670 | 12 | 13,102 | 222 |
| 0145 | 234 / 670 | 12 | 15,716 | 260 |

These are finite-height consequences of the existing seven-mask cover.
No finer limiting axial-order assumption is inserted into these queries.

## 3. Strictness, circuits and weak decision diagrams

For one representative of each topological orbit, the producer propagates
strict nonvanishing from the sixteen K4 brackets using the existing exact
cofactor and three-term Grassmann–Plücker rules. It stores every witness.
The verifier replays the witnesses against the actual sign model and
checks every transported strict set. Under the convention
`new_point[i] = old_point[p[i]]`, a known strict support is transported by
the inverse permutation. Different stabilizer proofs may safely be
united.

Within a K4 branch, the intersection of all member strict sets gives
53–69 universally strict four-brackets. Rank facts on three-point
supports are intersected separately: different models may prove a triple
noncollinear using different containing strict four-sets. The verifier
checks these facts with exact integer bitsets.

Every forbidden five-point minimal circuit has five nonzero cofactors.
Consequently its signs are exactly those of a compatible generic model,
and the common primary clauses already forbid it. A three- or four-point
circuit is removed only if every member model proves its support
affinely independent. The remaining actual circuit formulas are copied
unchanged from the complete source query. No forbidden three-point
circuit survives this rank propagation in the present cover; 3–50
four-point circuit tests remain per branch.

The diagram uses the other 54 sign columns and denotes exactly the
member generic assignments. Its independent replay expands the diagram
back to that finite set, including skipped columns. In the nonlinear
query a node for actual minor `M` is interpreted as follows:

- If `M` is proved nonzero throughout the branch, use
  `ite(M > 0, positive_child, negative_child)`.
- Otherwise use
  `(M >= 0 and positive_child) or (M <= 0 and negative_child)`.

At `M = 0`, the second expression permits either child. An accepting path
is therefore exactly a generic assignment compatible with the weak
actual signs. Using an ordinary strict `ite` at a weak node would lose
zero boundaries and is deliberately avoided.

The emitted query contains no unknown Boolean sign variables. Its
Boolean names are acyclic definitions in the actual minors. The query
verifier binds each definition to the checked diagram, checks every K4
sign and additional nonzero condition, and compares every retained
circuit with the full original formula before parsing the result.

## 4. A quadratic metric chart with an actual face anchor

`solver_remaining_face.py` supports actual face 013 or 023. Write the
normalized squared intrinsic edge length as

\[
D_{ij}=y^{-2}X_{ij}^2+V_{ij}^2.
\]

For anchor face `(0,a,b)`, choose normalized spatial coordinates

\[
P_0=(0,0,0),\qquad
P_a=(X_{0a}/y,V_{0a},0),\qquad
P_b=(X_{0b}/y,V_{0b},0).
\]

The cocycle closes on this actual face. Its three metric equations hold
identically. Every realization can be placed in this gauge by a spatial
isometry, since the face is nondegenerate. Reflection across the anchor
plane remains available for the global orientation convention.

The other five points have fifteen free spatial coordinates. Together
with the fourteen intrinsic coordinates this gives **29 real variables**.
The remaining **21 edge equations are quadratic**, with no Gram inverse,
bordered determinant, or denominator. The four nonedge squared distances
are actual quadratic coordinate expressions. All 252 original nonedge
contraction inequalities remain. The original shortest-lift, intrinsic
area, finite-mask and cyclic horizontal conditions remain verbatim.

Every actual coordinate minor is computed directly from these points:
84 one-dimensional, 168 two-dimensional and 70 three-dimensional minors.
Their degrees are at most 1, 2 and 3. Positive scaling by `1/y` preserves
their zero sets and signs. The chart imposes no lower bound on its chosen
face area; choosing a uniformly large face would require a separate joint
face/mask cover.

`solver_remaining_face_verify.py` checks all 21 metric identities, all
322 minor identities, all sixteen K4 determinants and all four nonedge
identities symbolically. It also checks literal preservation of the
unaffected original conditions and parses all 28 marking/mask/anchor
queries. Thus the degree reduction is an exact coordinate rewrite of the
existing necessary system.

## 5. Reproduction and measured work

From the repository root:

```sh
python3 research/type7_completion/solver_remaining_face_verify.py
python3 research/type7_completion/solver_remaining_chambers.py \
  /tmp/type7-remaining-compiled --proof --queries --mark 1 --mask 03
python3 research/type7_completion/solver_remaining_verify.py \
  /tmp/type7-remaining-compiled
c++ -O2 -std=c++17 research/type7_completion/solver_check_rup.cpp \
  -o /tmp/type7-check-rup
/tmp/type7-check-rup \
  /tmp/type7-remaining-compiled/coverage.cnf \
  /tmp/type7-remaining-compiled/coverage.drat
```

The complete example compilation took **33.77 seconds**, including
enumeration (4.92 seconds in this run), all seven mask covers, strictness
and diagram construction, the coverage trace, and 162 ray-1/mask-03
queries. The 162 queries range from 83,721 to 125,724 bytes, compared with
751,628 bytes for the full 29-real face query. Each full face query has
9,306 assertions. All 28 full chart queries parsed, and the 162 compiled
queries passed their independent formula binding and parser checks.

The coverage checker accepted 26,687 original clauses, 45,276 logged
input lines, 63,034 RUP additions and 47,628 deletions. The independently
checked sign list exactly matches the earlier general-SMT enumeration.

The remaining work is mathematical or nonlinear infeasibility of these
necessary systems, or a certified realization. Smaller formulas and
successful Boolean replay do not themselves decide any remaining mask.
