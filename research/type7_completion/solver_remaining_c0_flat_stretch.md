# Normal stretches of the common-line C0 families

For interior ray-1 C0, the
[common-line classification](exhaustive_c0_flat_common.md) leaves four
closed endpoint-deficit line families, four middle-deficit line
families, and one circle with coincident vertices 4 and 5.

This package excludes **all four endpoint-deficit interiors and the
zero-edge endpoints `h2=0` and `h6=0`**, without any assumption on
relative collapse rates. Eight CNFs give these exclusions; two pairs
are identical because adjacent closed families share endpoints.
Eight further CNFs give a complete necessary sign cover for the
remaining line families after a normal stretch.

The endpoints `h1=0` and `h7=0`, the four middle-deficit families,
and the coincident-vertex circle remain. The cover is not an
exclusion or a realization result for those cases. Nonparallel cap
lines and the nonflat directions of the circle are outside this
normal-stretch compiler.

## 1. A bounded nontrivial normal stretch

The original normalized heights are

\[
(0,1/2,1/2,1/2,u,v,0,0),\qquad 0<u,v<1/2.
\]

In every classified line family except the endpoint `h1=0`, the
transverse vector `P2` has strictly positive limiting length. Rotate
the actual transverse plane to put it on the negative horizontal
axis. At `h1=0`, use the positive limiting vector `P7` instead.
This preserves the original axis gauge `P0=P1=0`.

Write the actual transverse coordinates as `(X_i,Y_i)` and put
`delta=max_i |Y_i|`. Every finite realization has `delta>0` by the
established K4 nondegeneracy necessity. The line limit gives
`delta -> 0`. Divide the normal coordinate by `delta` and the
physical axial coordinate by the elongation parameter `y`. Both
transformations have positive determinant. Along a subsequence, the
stretched configurations converge to

\[
(P_{ix},N_i,z_i),\qquad N_0=N_1=N_a=0,
\qquad \max_{i\notin\{0,1,a\}}|N_i|=1,
\]

where the anchor `a` is 2 or 7 as specified above.

These transformations keep every coordinate bounded. In particular,
no axial error is divided by the normal width. Every nonzero limiting
bracket fixes a finite sign, while an actual zero leaves its generic
completion free. Passing to a subsequence fixes that completion in
the full necessary topology and linking formula. No comparison of
`delta`, `1/y^2`, a deficit, or a collapsing edge is required.

## 2. A complete polynomial parameter cover

After stretching, apply the positive affine map
`(X,N,z) -> (2X,N,2z)`. It has determinant four. Write the resulting
horizontal coordinates as `x_i` and heights as `z_i`.

For the four endpoint-deficit families, let

\[
a=2u,\quad b=2v,\quad t=2L,
\qquad 0<a,b<1,\quad 0\le t\le1.
\]

Choose upper and lower labels independently in `{a,b}`, as in the
classification. The upper label places the deficit `t/2` at 2 or 1;
the lower label places `(1-t)/2` at 7 or 6. Thus

\[
\begin{gathered}
x_0=x_1=0,\quad x_2=-1+2d_1,\quad x_7=1-2d_7,\\
x_3=-t\text{ or }t,\qquad x_6=-(1-t)\text{ or }1-t,\\
x_4=a x_3+(1-a)x_6-a,\\
x_5=b x_3+(1-b)x_6+1-b,
\qquad z=(0,1,1,1,a,b,0,0).
\end{gathered}
\]

Each closed `t` interval is split into its interior and its two
endpoints. The exceptional anchor 7 is used exactly for upper label
b at `t=1`. This is the endpoint `h1=0`; its limiting `x7` is 1.

For the four middle-deficit families take `0<a,b<1`. All have
`x0=x1=x3=x6=0`, `x2=-1`, `x7=1`, and `d4=(1-b)/2`.
Their remaining coordinates are:

| Family | `(2u,2v)` | `(x4,x5)` | Other deficit |
|---|---|---|---|
| `middle_lt_positive` | `(a,a+(1-a)b)` | `(1,1-b)` | `d5=b/2` |
| `middle_lt_negative` | `(a(1-b),a)` | `(b-1,-1)` | `d3=b/2` |
| `middle_gt_positive` | `(a+(1-a)b,a)` | `(1-b,1)` | `d3=b/2` |
| `middle_gt_negative` | `(a,a(1-b))` | `(-1,b-1)` | `d5=b/2` |

The exact substitutions reproduce the four rational deficit formulas
in the classification. Conversely each stated strict height order
gives a unique `a,b` in the open unit square. At `b=0`, the two line
directions of the diagonal circle remain: `u=v=a/2` and
`x4=x5=1` or `x4=x5=-1`. These are compiled separately.

Thus the complete line cover has eighteen strata: twelve from the
four closed endpoint families, four middle interiors, and two
diagonal line directions. The checker also verifies all twelve
closed projected source stresses on every parameterized family.
It does not impose metric equations on the stretched configurations.

## 3. Exact identities and uniform sign compilation

Each of the seventy actual brackets is linear in the five independent
normals. The compiler expands and checks every coefficient. It also
checks all 560 identities

\[
B_{ijab}A_{ijc}-B_{ijac}A_{ijb}+B_{ijbc}A_{ija}=0,
\]

where `Aijk` is the signed area in the `(x,z)` projection. Each
identity is verified in all five independent normal coordinates,
with the exact index permutation signs.

All coefficients are multilinear in `a,b,t`. Exact interpolation
from the eight unit-cube corners certifies their signs throughout
the open box. Endpoint strata substitute `t=0` or `t=1` first.
A coefficient with one weak sign at every corner and a nonzero value
at some corner has that strict sign throughout the relevant open
box. An identically zero coefficient stays zero. If any coefficient
has no uniform sign, the entire relation is omitted, weakening the
necessary system.

The Boolean source retains the full generic topology/linking
formula, both strict height cuts `{1,2,3}` and `{1,2,3,4,5}`, actual
positive/negative trits, affine cocycles, and the nontriviality of the
normal vector. A signed linear relation is relaxed only to the
necessary condition that all terms vanish or terms of both signs
occur. The same exact method was used in the
[complete flat C1 exclusion](solver_remaining_c1_flat_stretch.md).

## 4. Exclusions and residual normal cover

The following source formulas are inconsistent:

| Endpoint family | Excluded strata |
|---|---|
| aa | `0<t<1`, `t=1` |
| ab | `0<t<1`, `t=0`, `t=1` |
| ba | `0<t<1` |
| bb | `0<t<1`, `t=0` |

The shared `t=1` endpoint of aa and ab is `h2=0`; the shared `t=0`
endpoint of ab and bb is `h6=0`. This accounts for eight CNFs and
six distinct proof packets.

For every remaining stratum, the output records a short list of
possible normal sign patterns and a separate CNF excluding its
complement. The list retains normal zeros. There are eight distinct
residual sources and 32 listed patterns in total; the two duplicated
closed endpoints reuse exactly the same source clauses and proof.
For example, at `h7=0`, the normal order `(N3,N4,N5,N6,N7)` is one of

\[
(0,+,+,+,0),\quad(0,+,+,0,0),\quad(0,0,0,+,0).
\]

For every middle-deficit family and both diagonal line directions,
the cover forces `N3=N6=0`. The other normal signs remain as explicitly
listed in the packet. These statements constrain a subsequent metric
argument; they do not close those families.

## Reproduction

    python research/type7_completion/solver_remaining_c0_flat_stretch.py /tmp/c0-flat-stretch
    python research/type7_completion/solver_cnf_certificates.py /tmp/c0-flat-stretch-rup \
      --checker /tmp/type7-rup-check /tmp/c0-flat-stretch

All sixteen obligations require independent RUP replay. Eight prove
geometric exclusions and eight prove the residual normal sign cover.
