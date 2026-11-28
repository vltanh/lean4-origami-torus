# Complete exclusion of the interior ray-2 C1 component

**Research theorem.** There is no unbounded sequence of embedded
ray-2 realizations whose bounded-axis limit belongs to C1 with
`0<alpha,beta<1`.

The theorem follows from the geometric arguments, exact source
identities, and independently replayable Boolean certificates linked
below. This note assembles their complete case cover. It includes all
limiting horizontal-weight endpoints, coincident critical heights,
zero actual determinants, and unrelated rates of edge, cap-area, and
normal collapse. It asserts no exclusion at a height endpoint, no
ray-2 C0 exclusion, no numerical eventual-height bound, and no Lean
theorem or completed marking.

## 1. Common source and exhaustive first split

Use the [bounded-axis compactification](solver_remaining_axis.md)
and the [closed limit source](solver_remaining_limit.md). In C1,

\[
\begin{gathered}
P_0=P_1=0,\qquad
z=(0,\alpha/2,1/2,1/2,1/2,\beta/2,0,0),\\
0\le h_i\le\tfrac12,\qquad
\sum_{i=0}^7h_i=\tfrac52,\qquad
h_i+h_{i+1}\ge\tfrac12.
\end{gathered}
\]

Indices on h are cyclic. The
[closed C1 circle identities](solver_remaining_c1_geometry.md)
are polynomial consequences of all 29 original metric/product-scale
rows, including the five product-scale syzygies. The two caps have
edge-length lists

\[
234:\ (h_2,h_3,1-h_2-h_3),\qquad
067:\ (1-h_6-h_7,h_6,h_7).
\]

Each cap has perimeter one. The upper-cap conclusion is valid
throughout the open height square: the coefficient
`1-(alpha+beta)/2` of its third-edge stress is strictly positive
there. Its exceptional zero at `alpha=beta=1` is a height boundary
and is not used in this theorem.

Every cap is therefore either a noncollinear triangle or a nonconstant
collinear segment. A completely coincident cap is impossible. These
alternatives give the following exhaustive first split.

| Limiting caps | Complete exclusion and dependencies |
|---|---|
| Both noncollinear | [Nested-section theorem](remaining_c1_sections.md): finite convex inner critical sections, equal perimeter, and corner tracking. It covers both strict height orders and `alpha=beta`. |
| Exactly one collinear | [One-collinear theorem](remaining_c1_one_collinear.md): all strict orders and both zero cyclic edges, after the checked marked cap swap. The third-edge coincidence is excluded by the ray-2 slack budget. |
| Both collinear; `h2,h3,h6,h7>0` | [Common-line reduction](remaining_c1_flat_reduction.md), then [positive-edge normal stretch](remaining_c1_flat_positive_stretch.md): all 16 order pairs reduce to twenty scalar families, all excluded. |
| Both collinear; at least one of `h2,h3,h6,h7` is zero | The six disjoint marked order orbits in Section 2; all are excluded in Section 3. |

Here “positive cap edges” refers to the four displayed cyclic edges.
It does not exclude a zero third edge 24 or 06. Those coincidences
are order C below and are already included in the positive-edge row.

## 2. All collinear orders and all zero-edge symmetries

A collinear perimeter-one triangle has diameter `1/2`. It has exactly
one of the following six orders; there is no additional collapsed-cap
case.

| Label | Upper cap 234 | Upper cyclic lengths | Lower cap 067 | Lower cyclic lengths |
|---|---|---|---|---|
| A | 4 strictly between 2 and 3 | `h2=1/2`, `0<h3<1/2` | 0 strictly between 6 and 7 | `h6=1/2`, `0<h7<1/2` |
| B | 2 strictly between 3 and 4 | `h3=1/2`, `0<h2<1/2` | 6 strictly between 0 and 7 | `h7=1/2`, `0<h6<1/2` |
| C | `P2=P4`, distinct from P3 | `h2=h3=1/2` | `P0=P6`, distinct from P7 | `h6=h7=1/2` |
| D | 3 strictly between 2 and 4 | `h2,h3>0`, `h2+h3=1/2` | 7 strictly between 0 and 6 | `h6,h7>0`, `h6+h7=1/2` |
| E | `P2=P3`, distinct from P4 | `h2=0`, `h3=1/2` | `P6=P7`, distinct from P0 | `h6=0`, `h7=1/2` |
| F | `P3=P4`, distinct from P2 | `h3=0`, `h2=1/2` | `P0=P7`, distinct from P6 | `h7=0`, `h6=1/2` |

The four nearest-pair slacks
`h0+h1-1/2`, `h2+h3-1/2`, `h4+h5-1/2`, `h6+h7-1/2`
sum to `1/2`. In particular CC is impossible: its two cap slacks
already sum to one. If one cap is regular, a C coincidence in the
other consumes the entire available slack and contradicts the
regular cap's positive slack. These facts account for the coincidence
cases in the first table rather than omitting them.

The [relative short-edge source](remaining_c1_short_edges.md#4-complete-remaining-zero-edge-order-cover)
checks the marked reflection `i -> 6-i`, which simultaneously exchanges
`A/B` and `E/F` and fixes `C,D`, and the marked cap swap `i -> i+4`.
Their cocycle/gauge checks retain the ray-2 marking. The transformed
height parameters remain strictly interior. Their six disjoint orbits
are exactly the twenty pairs with at least one E or F:

| Representative | Entire orbit |
|---|---|
| EA | EA, AE, FB, BF |
| EB | EB, BE, FA, AF |
| EC | EC, CE, FC, CF |
| ED | ED, DE, FD, DF |
| EE | EE, FF |
| EF | EF, FE |

Together with the sixteen pairs in `{A,B,C,D}^2`, these cover all
36 collinear order pairs. A parameter endpoint in a strict A, B,
or D order changes its label to C, E, or F; it is included in this
same finite cover.

## 3. Every zero-edge orbit is excluded

| Orbit | Necessary geometric reduction | Final exclusion, with parameter endpoints |
|---|---|---|
| EA | [Flat-cap reduction, Section 4](remaining_c1_flat_reduction.md#4-two-zero-edge-order-orbits) makes the cap directions parallel; its explicit first-circle coordinates then put every vertex on the same transverse line. | [EA/EC scalar theorem](remaining_c1_ea_ec_scalar.md): four EA scalar families; the free middle weight is covered at zero, in its open interval, and at `1/2`. |
| EB | [Nonparallel exclusion](remaining_c1_single_zero_nonparallel.md), then [common-line theorem](remaining_c1_single_zero_common.md). | [Single-zero scalar theorem](remaining_c1_single_zero_scalar.md): the one EB family, including its zero outer weight, is excluded by macro and relative-23 normalizations. |
| EC | The same [flat-cap reduction](remaining_c1_flat_reduction.md#4-two-zero-edge-order-orbits), including the coincident lower third edge. | [EA/EC scalar theorem](remaining_c1_ea_ec_scalar.md): four EC scalar families, including both middle-weight endpoints and the complete `alpha<beta`, `alpha=beta`, `alpha>beta` cover where needed. |
| ED | [Nonparallel exclusion](remaining_c1_single_zero_nonparallel.md), then [common-line theorem](remaining_c1_single_zero_common.md). | [Single-zero scalar theorem](remaining_c1_single_zero_scalar.md): all three ED scalar families, with both anchor signs and all allowed directions. |
| EE | [Same-zero theorem](remaining_c1_same_zero.md) excludes `0<h0<1/2`. At `h0=0,1/2`, the [double-zero common-line reduction](remaining_c1_zero_common.md#2-the-two-ee-endpoints) applies. | The [endpoint theorem](remaining_c1_double_zero_endpoints.md) excludes both equal-direction endpoints. The [double-zero completion](remaining_c1_double_zero_completion.md) excludes both opposite-direction endpoints, using the checked cap swap for the right endpoint. |
| EF | [Opposite-zero theorem](remaining_c1_opposite_zero.md) forces parallel cap directions; the [double-zero common-line reduction](remaining_c1_zero_common.md#1-parallel-cap-ef) then puts every vertex on their common line. | The [endpoint theorem](remaining_c1_double_zero_endpoints.md) excludes `eta=-1, epsilon=+1`; the [double-zero completion](remaining_c1_double_zero_completion.md) excludes all remaining signs and the entire closed free-weight interval. |

The two rows involving a final double-zero completion have the following
explicit, exhaustive scalar partition. This makes their interfaces
with the earlier endpoint theorem precise.

### EF

Orient `U=P4-P3` positively, so `U=1/2`; write
`alpha P3=eta/2`, `P6=epsilon/2`, and `r=h5`.
The [closed scalar classifier](remaining_c1_zero_common.md#3-the-remaining-exact-scalar-families)
gives `eta,epsilon in {-1,+1}` and

\[
\epsilon=+1\Longrightarrow r=\beta/2,\qquad
\epsilon=-1\Longrightarrow 0\le r\le\tfrac12.
\]

The endpoint theorem handles `eta=-1,epsilon=+1`. The completion
handles `eta=+1,epsilon=+1` and each `eta=+1,-1` with `epsilon=-1`.
In the latter two families, its three cells `r=0`, `0<r<1/2`,
and `r=1/2` include every allowed weight. Thus all eight scalar
sign/parameter strata are covered.

### EE

The source forces

\[
h=(r,\tfrac12,0,\tfrac12,\tfrac12-r,\tfrac12,0,\tfrac12),
\qquad 0\le r\le\tfrac12.
\]

The strict interval is excluded by the same-zero theorem without a
parallel-cap assumption. At either endpoint orient `P6=P7=1/2`
and write `U=epsilon/2`. The common-line theorem gives exactly the
two directions `epsilon=+1,-1`; all four endpoint choices are
excluded by the two packages in the table. Their checked cap-swap
identities send each right endpoint to the corresponding left
endpoint after valid axis reanchoring. There is no missing endpoint
deformation or extra direction.

For EA and EC the analogous scalar equation is
`(beta/2-r)(epsilon-1)=0`: the negative direction has `r=beta/2`,
and the positive direction has the same closed three-cell weight
cover. For EB and ED the exact twelve-choice second-circle/budget
calculation leaves respectively one and three families. These are
the full classifications, rather than choices of sample parameters.

## 4. Why no degeneration boundary is lost

**Horizontal weights.** The limits use closed inequalities throughout.
Positive cyclic cap edges are handled by the twenty-family theorem,
including third-edge coincidences and outer weights at zero or `1/2`.
Its exceptional half/half circle and zero-radius cases are explicitly
excluded by the total budget. Zero cyclic cap edges enter the six-orbit
cover. The scalar tables above keep every permitted remaining weight
endpoint. No positive lower bound on an arbitrary small weight is used.

**Actual zero determinants.** Every package distinguishes an actual
limiting determinant from its finite generic completion. A nonzero
actual determinant fixes that generic sign; a zero determinant leaves
it free. Geometric convexity and nesting statements use finite
embedded sections or explicit winding limits. A zero limiting minor
is never converted into a strict sign to complete the case split.

**Independent scales.** The relative short-edge theorem proves

\[
|P_j-P_i|/h\longrightarrow1,\qquad
\zeta_j-\zeta_i=O(t h),\qquad
v_j-v_i=O(t h),\qquad t=1/y^2,
\]

at each shrinking cyclic cap edge, in its own scale. Its marked
symmetries cover 23,34,67,07. The source checks single-edge and
double-edge determinant normalizations with independent formal
lengths; no ratio between the two lengths is prescribed.

The common-line scalar proofs stretch only the transverse normal
coordinate by its positive width. They do not divide an axial error
by that width. Their scalar-axis anchor P3 is nonzero in every
classified family: the positive-edge budget excludes its zero-radius
exception, and the zero-edge tables give either a positive anchor
at least `1/2` or an anchor of magnitude `1/(2 alpha)`.
Thus no singular axis choice discards a scalar endpoint.
Whenever a macro stretched pair still coincides, its
short edge is resolved separately. The alternatives of bounded and
unbounded stretched-normal-to-edge ratio give all virtual directions
`(H,Y,0)`, `H in {-1,0,1}`, with `Y!=0` when `H=0`. Double-zero
completion treats both such directions independently. These are
subsequence covers of every relative rate, including edges much
smaller than `t` or the normal width.

Positive combinations of macro and independently normalized determinant
forms in the final scalar packages are checked only after expansion
in the same normal and virtual variables. Their coefficients retain
their exact magnitudes and their verified positive signs. The proofs
do not impose ordinary affine cocycles between unrelated normalization
scales. A relation with an uncertified coefficient sign is omitted
from a necessary relaxation, never assigned an assumed sign.

**Height equalities.** The theorem includes `alpha=beta` and arbitrary
approach to that diagonal. The section proofs have separate coincident
critical-height arguments. The scalar sources either retain exact
coefficients, weaken a relation whose sign varies, or use an exhaustive
three-cell height cover. No separation of the two interior heights is
assumed. In contrast, `alpha` or `beta` equal to zero or one is outside
this theorem; positive interior coefficients used here can vanish there.

## 5. Verification dependencies and conclusion

This assembly adds no new SAT or metric-solving premise. Its required
source/checker modules are the Python companions of the linked notes:

| Proof layer | Exact companions |
|---|---|
| Closed metric source | [C1 geometry](solver_remaining_c1_geometry.py), [full limit source](solver_remaining_limit.py) |
| Regular and one-collinear caps | [Sections](remaining_c1_sections.py), [one-collinear](remaining_c1_one_collinear.py) |
| Positive cyclic edges | [Flat reduction](remaining_c1_flat_reduction.py), [positive stretch](remaining_c1_flat_positive_stretch.py) |
| Relative edge bounds and complete order cover | [Short edges](remaining_c1_short_edges.py) |
| EB/ED reduction and exclusion | [Nonparallel](remaining_c1_single_zero_nonparallel.py), [common line](remaining_c1_single_zero_common.py), [scalar](remaining_c1_single_zero_scalar.py) |
| EA/EC exclusion | [EA/EC scalar](remaining_c1_ea_ec_scalar.py) |
| EF and EE reduction | [Opposite zero](remaining_c1_opposite_zero.py), [common line](remaining_c1_zero_common.py) |
| EE open interval and all double-zero endpoints | [Same zero](remaining_c1_same_zero.py), [endpoint exclusions](remaining_c1_double_zero_endpoints.py), [double-zero completion](remaining_c1_double_zero_completion.py) |

All emitted UNSAT obligations require independent replay with the
[CNF certificate driver](solver_cnf_certificates.py) and
[RUP checker](solver_check_rup.cpp), as specified by the individual
packages. Symbolic source identities and geometric proofs remain
separate necessary parts of the theorem; SAT enumeration alone does
not establish it. The double-zero completion's exact polynomial
certificate data is in
[its certificate packet](remaining_c1_double_zero_completion.json).

Assume an unbounded embedded sequence had an interior ray-2 C1 limit.
Its two caps fall in exactly one row of the first table. The first
three rows have complete exclusions. In the fourth row the checked
six-orbit cover selects one row of the zero-edge table; its geometric
reduction and complete scalar/relative-scale exclusion give a
contradiction. Hence no such limit exists.

An unbounded ray-2 sequence is therefore still allowed by this result
to approach C0 or the C1 height boundary. Closing those gates and
assembling the final Lean result remain separate tasks.
