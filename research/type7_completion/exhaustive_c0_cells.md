# Complete topology in the eighteen regular C0 cells

The anchor projection in exhaustive_c0_angles.py loses essential
topological information. This companion keeps every one of the 669
generic cap-compatible sign models, partitioned into the same 18
anchor cells. It supplies exact model covers, all conditional
unanimous signs, and compact decision diagrams with the correct
interpretation of zero actual minors.

The assumptions remain the two noncollinear endpoint caps 123 and
067 and $0<u,v<1/2$ in the C0 asymptotic chart. This is a necessary
limit reduction. No metric cell or marking is excluded.

## 1. Complete finite cells

The zero-based cell numbers agree with the pattern ordering in
exhaustive_c0_angles.py. Each cell has its own generic topology
formula: the shared ray-1/2 clauses, the ten positive-cap units,
and the 15 anchor signs.

| Cell | Generic models | Forced signs | Decision nodes |
|---:|---:|---:|---:|
| 0 | 68 | 39 | 174 |
| 1 | 36 | 52 | 45 |
| 2 | 37 | 50 | 80 |
| 3 | 112 | 34 | 460 |
| 4 | 80 | 38 | 314 |
| 5 | 44 | 40 | 157 |
| 6 | 1 | 70 | 0 |
| 7 | 26 | 61 | 31 |
| 8 | 7 | 65 | 7 |
| 9 | 80 | 38 | 314 |
| 10 | 48 | 43 | 100 |
| 11 | 1 | 70 | 0 |
| 12 | 7 | 65 | 7 |
| 13 | 1 | 70 | 0 |
| 14 | 36 | 52 | 43 |
| 15 | 4 | 68 | 0 |
| 16 | 37 | 50 | 80 |
| 17 | 44 | 40 | 155 |

The producer emits two CNFs per cell.

* The coverage CNF blocks every listed generic sign model. Its UNSAT
  certificate proves that the list contains every allowed model.
* The forced-sign CNF asserts that at least one listed unanimous
  sign is false. Its UNSAT certificate proves all those signs.

Complete Boolean SAT assignments witness both signs of every
nonunanimous bracket. The producer checks each such assignment
against every input clause. Thus the conditional forced-sign lists
are exact, rather than merely a selection of convenient consequences.

All 36 CNFs passed independent RUP replay. There are 33 distinct
proof packets because the two formulas coincide in each of the three
single-model cells. The replay took 2.645 seconds in the shared
workspace. Building the complete table took about 2–3.5 seconds.

Cells 6, 11, and 13 are particularly direct certificate targets:
their 70 signs already specify the entire generic topology. A
forced-sign-only relaxation of cell 0 still forgets the choices
among 68 models.

## 2. Exact diagrams and zero minors

After removing the forced columns, the producer builds an ordered
Boolean decision diagram for the remaining generic signs. A separate
counting recursion counts every accepted word, including all skipped
levels. Every listed model is then evaluated in the diagram. Equality
of the accepted-word count and the number of distinct listed models
proves that the diagram represents exactly the listed set.

A zero-node diagram need not mean a unique model. Cell 15 has two
unforced signs, and all four choices occur; its remaining diagram is
the constant true function.

For an actual minor $D$ at a node with positive child $C_+$ and
negative child $C_-$, the generated formula is

$$
 (D\ge0\ \wedge C_+)\ \vee\ (D\le0\ \wedge C_-).
$$

Both branches are available when $D=0$. The forced signs are also
weak, except for the ten cap units whose nonzero limits follow
from the stated regularity assumptions. Strictness of a finite
tetrahedron alone does not imply a nonzero limiting determinant,
so it is not transferred to other minors.

The resulting formula says exactly that the actual nonzero signs
have a completion in the cell's full generic model set. It preserves
all 70 signs and their dependencies. In particular, it rejects the
exact regular metric witness in exhaustive_c0_angles.md, even though
that witness satisfies the first anchor pattern.

## 3. Optional limiting metric queries

The producer can combine these diagrams with the closed C0 metric
basis from solver_remaining_limit.py. The uniform chart has 20 real
variables: seven intrinsic horizontal coordinates, eleven projected
coordinates, and $u,v$. It fixes

$$
 P_0=P_1=0,\qquad P_3=(p_{3x},0),\qquad p_{3x}>0,\qquad p_{2y}<0.
$$

The twelve metric equations, horizontal nearest-lift bounds,
nonnegative limiting horizontal lengths, intrinsic oriented face
areas, and projected-coordinate bounds remain. The exact linear
gauge

$$
 p_{3x}=1-h_1-h_2
$$

is included. It follows from the 13 metric equation, the nonnegative
horizontal lengths, and the positive axis gauge. Symbolic checks
verify that the oriented 310 area is
$(1-h_1-h_2)/2>0$ and that the sum of all oriented face areas is
exactly two. Thus the nonnegative face-area choice is necessary.

The twelve rows are checked against the original 29-row auxiliary
system before emission. The 70 actual minors are expanded directly
from $(P_i,z_i)$ with

$$
 z=(0,1/2,1/2,1/2,u,v,0,0).
$$

The uniform metric equations have degree at most four, and the
minors have degree at most three. With the optional quarter-height
specialization $u=v=1/4$, there are 18 real variables and the metric
equations are quadratic. A result at that specialization would not
be a uniform C0 theorem.

The query verification mode parses all 72 combinations of marking,
height choice, and cell without running nonlinear search. It also
checks that all 18 complete diagrams reject the exact regular anchor
witness and allow every non-cap minor to vanish at the sign-coupling
layer. Additional metric consequences can strengthen this necessary
system; the complete-model assertion here concerns the topology.

## Reproduction

    python research/type7_completion/exhaustive_c0_cells.py /tmp/type7-c0-cells --queries --mark 1 --verify-queries

    python research/type7_completion/solver_cnf_certificates.py /tmp/type7-c0-cells-rup --checker /tmp/solver-check-rup /tmp/type7-c0-cells/cnfs

The JSON contains the 18 complete model lists, forced signs, checked
SAT witnesses, and decision diagrams. The topology snippets can be
attached to another metric chart that supplies the same 70 named
actual minors. All formula exports remain necessary conditions; no
nonlinear UNSAT result is claimed.
