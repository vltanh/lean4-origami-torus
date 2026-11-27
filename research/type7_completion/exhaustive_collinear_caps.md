# Two collinear caps cannot have nonparallel limiting lines

**Theorem.** In an unbounded canonical ray-3 sequence, if both transverse
caps become entirely collinear, their limiting lines must be parallel.
Since the chosen transverse anchors `P0=P2=0` lie on both lines, the
lines then coincide.

The proof covers every labelled one-dimensional vertex order, every
coincidence pattern, and every relative collapse rate. It combines an
exact finite order/stress cover, the arbitrary-rate two-triple-cluster
theorem, and twelve small Boolean contradictions for the last family.
This is an asymptotic research theorem; common-line limits and the full
finite-height systems remain open. A sequence with one collinear and
one noncollinear cap is not addressed by this theorem.

## 1. All 5,476 weak vertex-order pairs

Let `u,v` be unit directions along two proposed nonparallel limiting cap
lines. Write the cap vertices as scalar multiples of `u` or `v`. The
transverse anchors are both zero. The limit of each short-edge length
is its absolute scalar step; each ring has perimeter one. Neither cap
can consist of a single point.

Four labelled scalars have exactly 74 nonconstant weak orders: an
ordered partition into two, three, or four nonempty level sets. Thus
there are `74²=5,476` pairs of orders. Every actual coincidence pattern
is included.

For two vertices in each cap, the corresponding 3D affine bracket in
the normalized two-level limit is, up to its fixed permutation sign,

```
-(a_j-a_i)(b_l-b_k) det(u,v).
```
There are 36 such brackets. A nonzero scalar product fixes its eventual
generic-completion sign; zero products leave that sign unrestricted.
The other limiting brackets are zero and are left unrestricted.

Filter all order pairs against the complete 1,888 generic ray-3 sign
models and their global reversals. Exactly **1,336** order pairs remain;
**4,140** are excluded by necessary orientation and linking alone.

## 2. Positive gaps turn the stress test into an exact finite inequality

Within a fixed weak order, introduce a strictly positive gap between
every two consecutive distinct levels. Every scalar ring step is an
integer linear combination of these gaps. Its absolute value is another
linear combination with the sign fixed by the order.

Put `k=u·v`, so `-1<k<1`. The homogeneous limiting stress equation is

```
F=2 sum_ij M_ij(|a_i||b_j|-k a_i b_j)
   -(sum_i|a_i|)(sum_j|b_j|)=0.
```
Here `a_i,b_j` are scalar edge steps and `M` is the exact stress mask
from `cap_limit.md`. For each pair of positive gap variables, its
coefficient in `F` is affine in `k`. Evaluate these integer coefficients
at `k=+1` and `k=-1`.

For **1,176** of the 1,336 order pairs, every coefficient at both
endpoints has one common weak sign and at least one coefficient is
strict. Since `k` lies strictly between the endpoints and every gap is
positive, `F` has that strict sign. These orders contradict the metric
identity. This is an exact integer check, with no root isolation or
numerical optimization.

For the remaining **160** orders, both endpoint coefficient matrices
vanish identically. No metric-only contradiction is claimed for them.
The exact marked symmetries, together with reversal of either scalar
line coordinate, divide them into two disjoint families:

| Canonical family | Orders covered |
|---|---:|
| `A: (0,0,0,1)`, `B: (0,0,0,1)` | 32 |
| `A: (0,0,0,1)`, `B: (0,λ,0,1)`, `λ≠0` | 128 |

The verifier checks this cover as equality of finite sets, using the
verified phase-preserving marked symmetries. The first family is exactly
the labelled nonparallel two-triple-cluster limit excluded at every
relative rate in `exhaustive_nonparallel_corner.md`.

## 3. The last cluster/out-and-back family

In the second family,

```
P1,P4→P0=0, P5→p,
P6→P2=0, P3→λq, P7→q,
```
where `p,q` are nonparallel and `λ≠0`. The perimeter constraints give
`|p|=1/2` and `2(1+|λ|)|q|=1`. All four B-ring edges have positive
limiting length. The two A edges `a=01` and `b=14` collapse, but their
individually normalized transverse limits are nonzero.

Fix the moving affine anchors `0,2,5,7`. Their limiting positions, and
that of vertex 3, are

```
0=(0,0,0), 2=(0,0,1), 5=(1,0,0),
7=(0,1,1), 3=(0,λ,1), 6=(0,0,1).
```
Pass to a subsequence for the ratio of the two collapsing edge lengths.
It is either zero, finite and positive, or infinite. These are the three
A-edge scale cases.

The necessary bracket links are deliberately limited to ones with a
uniform factorization:

- A bracket with nonzero constant term has that eventual sign.
- A rank-two limiting bracket containing at least two of `0,1,4`
  factors the corresponding edge `a`, `b`, or sum `a+b`. Its leading
  coefficient is linear in their transverse coordinates.
- The four brackets containing `0,1,4` and one B vertex factor both
  `a,b`, and have leading coefficient `±det(a,b)`.

Every other bracket is left unrestricted. In particular no assumption
is made about the rate of motion of vertex 3 off the B line, the rate
of collapse of missing edge `26`, or the relation between any of these
rates and `1/y²`.

For the linear links, normalize a named single edge by its own length;
normalize `a+b` by the larger of the two lengths. In the comparable
case, the sum coordinates obey the exact ternary addition rule. In the
two unequal cases, their signs are those of the dominant edge. The
quadratic bracket error divided by the product of the two individual
edge lengths tends to zero, by the relative axial bounds. Motion of a
B anchor only changes a bounded coefficient by `o(1)` after the named
A-edge factor has been removed. Thus no hidden comparability assumption
is used.

The only nonconstant scalar factors in any constant or linear leading
coefficient are `±λ` and `±(λ-1)`. Consequently the exact four-cell cover

```
λ<0,   0<λ<1,   λ=1,   λ>1
```
requires no further subdivision. The verifier checks these symbolic
factors before evaluating one representative of each cell. At `λ=1`,
all newly vanishing coefficients are left free.

## 4. Twelve independently checked Boolean contradictions

Use seven ternary signs: the four coordinates of the two nonzero planar
vectors, their two coordinate sums, and their determinant. The exact
identity `det(a,b)=ax*by-ay*bx` supplies the necessary rank-two sign
condition, retaining zero coefficients throughout. Add the audited
orientation formula, the two horizontal unlinkings, and long linking of
magnitude two.

For `λ≠1`, the formula has 15 constant, 27 linear, and four quadratic
bracket links. At `λ=1`, it has 12 constant, 24 linear, and four quadratic
links. Each of the twelve cells is UNSAT. The independent exhaustive
C++ checker reports:

| Lambda cell | `a` dominates | Comparable | `b` dominates |
|---|---:|---:|---:|
| `λ<0` | 373 nodes | 389 nodes | 369 nodes |
| `0<λ<1` | 363 nodes | 375 nodes | 361 nodes |
| `λ=1` | 363 nodes | 375 nodes | 361 nodes |
| `λ>1` | 363 nodes | 379 nodes | 361 nodes |

Each formula has 423 variables and 8,609–8,638 clauses. Producing the
entire 5,476-order cover and all twelve formulas takes about six seconds
in the current environment; all independent replays together take about
three seconds. This excludes the last family and proves the theorem.

## Reproduction

```sh
python3 research/type7_completion/exhaustive_collinear_caps.py /tmp/type7-collinear-caps
g++ -O3 -std=c++17 research/orientation_checkpoint/check_unsat.cpp -o /tmp/type7-corner-checker
```

Replay each of the twelve emitted CNFs with the C++ checker and require
its explicit `UNSAT nodes ...` output. A zero exit status alone is not
a SAT/UNSAT discriminator for this checker. The underlying full model
cover has the independent RUP certificate described in
`solver_compilation.md`. The order cover, endpoint stress inequalities,
marked orbit cover, and symbolic lambda-cell factors are checked exactly
from repository inputs, without cached scratch models.
