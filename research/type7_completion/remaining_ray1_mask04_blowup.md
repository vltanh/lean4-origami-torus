# Marking 1, mask 04: the first transverse stretch leaves four endpoints

Combine the common-line limit theorem in `remaining_ray1_mask04.md`
with the exact weak-slope cover below. Every unbounded marking-1
sequence in mask 04 has, after passing to a subsequence, one of

\[
h_1=0,\qquad h_3=0,\qquad h_5=0,\qquad h_7=0,
\tag{1}
\]

and all seven other limiting horizontal weights equal `1/2`.
The four endpoint families in (1) are **not excluded by this note**.
They are equivalent under the checked marked dihedral symmetries.

The argument uses no expansion in `t`, no comparison between a
vanishing weight and the transverse width, and no division by a
vanishing horizontal projection. The finite certificates have at most
611 variables and 11,954 clauses.

## 1. A nontrivial stretch exists and preserves all necessary signs

Use the bounded axis-01 coordinates from
`exhaustive_remaining_axis.md`. The preceding limit theorem puts all
transverse limits on one oriented line and gives

\[
\begin{aligned}
P_2&=-h_1E,&P_3&=(h_2-h_1)E,&P_4&=(h_2-h_1-h_3)E,\\
P_7&=h_7E,&P_6&=(h_7-h_6)E,&P_5&=(h_5+h_7-h_6)E,
\end{aligned}
\tag{2}
\]

with `P0=P1=0`. At least one of these transverse vertices has a
nonzero limit. Rotate each actual transverse plane so that a fixed
such vertex lies on the horizontal axis, with the positive orientation
converging to `E`. Write its coordinates as `(X_i,Y_i)` and put

\[
\delta=\max_i|Y_i|.
\]

Here `delta>0`: otherwise all actual vertices lie in one plane in
three-space, contradicting the proved nondegeneracy of every K4.
No uniform lower bound on a K4 determinant is needed. The common-line
theorem gives `delta -> 0`.

Pass to a subsequence on which every `Y_i/delta` converges. The stretched
points have bounded coordinates, at least one limiting normal
coordinate has absolute value one, and the chosen horizontal anchor
still has normal coordinate zero. Normalize the axial coordinate by
`y`. The upper cap has limiting axial level `1/2`, and the lower cap
has level zero. Thus, after harmless positive axial scaling, the
limiting incidence points are

\[
(X_i,\widehat Y_i,1)\quad(i\in\{1,2,3,4\}),\qquad
(X_i,\widehat Y_i,0)\quad(i\in\{0,5,6,7\}).
\tag{3}
\]

The actual coordinate transformation has positive determinant
proportional to `1/(y*delta)`. Every nonzero bracket of (3) therefore
fixes the same generic sign as the actual sequence. A zero limiting
bracket is left unrestricted. This is simply continuity in the bounded
stretched coordinates; it does not require `delta` to dominate any
axial error, since the axial coordinate is not rescaled by `delta`.

The cap vectors in (3) cannot all be parallel. If they were, the two
caps, both containing a vertex at transverse origin, would lie on the
same line. The horizontal anchor with nonzero `X` and zero normal
coordinate would make that line horizontal, contradicting
`max |Yhat_i|=1`.

## 2. Complete horizontal order cover

The preceding theorem gives

\[
h_0=h_4=\tfrac12,\quad H_A+H_B=\tfrac52,
\quad H_A,H_B\in[1,\tfrac32],
\]

and, for each cap, either its middle weight is `1/2` or both outer
weights are `1/2`. The five strict-chain order names below are the
ones from the preceding note. Four additional endpoint names retain
all coincidences.

| Cap type | Chain sum | Upper coordinates in order `(1,2,3,4)` |
|---|---|---|
| I | strictly between 1 and `3/2` | `(0,-2,-1,-3)` |
| II | strictly between 1 and `3/2` | `(0,-3,1,-2)` |
| II_left | strictly between 1 and `3/2` | `(0,-2,0,-1)` |
| II_right | strictly between 1 and `3/2` | `(0,-2,1,-2)` |
| II_both | `3/2` | `(0,-1,0,-1)` |
| I_zero | 1 | `(0,-1,-1,-2)` |
| II_sum | 1 | `(0,-1,1,0)` |
| II_sum_left | 1 | `(0,-1,0,0)` |
| II_sum_right | 1 | `(0,0,1,0)` |

The displayed coordinates specify only weak orders. No distance ratio
is inferred from the representative integers. The corresponding lower
orders in `(0,6,7,5)` are listed explicitly in the producer.

For example, type I has `h1=h3=1/2` and `0<h2<1/2`.
Its endpoint `h2=0` is I_zero; the other endpoint `h2=1/2` is
II_both. Type II has `h2=1/2` and both outer weights below `1/2`.
At chain sum one, `h1+h3=1/2`: both positive gives II_sum,
`h3=0` gives II_sum_left, and `h1=0` gives II_sum_right.

Because the two chain sums add to `5/2`, the complete order cover is:

- all 16 pairs from `{I,II,II_left,II_right}`;
- one of the four chain-one endpoints paired with II_both, in either
  order, giving eight more pairs.

There are therefore exactly 24 cases. A chain-one endpoint cannot be
paired with an interior chain, and two maximal chains cannot be
paired. All endpoint rates and all zero horizontal projections are
retained.

## 3. Exact weak slopes, including vertical edges

Take the six vectors joining each pair of upper-cap vertices and the
six joining each pair of lower-cap vertices. Their limiting horizontal
signs are fixed by the selected weak order.

For an edge with nonzero horizontal component, reverse it when needed
to obtain a vector `(x,x*s)` with `x>0`. Its slope `s` is a well-defined
real number. For every pair of these slopes, introduce a trit for the
sign of their difference. Every three slopes have one of exactly 13
weak orders. The producer explicitly forbids the other trit triples.
In particular, equality is retained throughout.

A zero-horizontal edge is retained as `(0,v)`, with its own trit for
`sign(v)`. It may be the zero vector. The exact cross-product rules are

\[
\begin{aligned}
[(x,xs),(z,zr)]&=xz(r-s),\\
[(0,v),(z,zr)]&=-vz,\\
[(x,xs),(0,v)]&=xv,
\end{aligned}
\tag{4}
\]

and two vertical vectors have zero determinant. The code applies the
original edge-direction signs explicitly.

For every cap triangle, its three edge vectors obey `w=u+v`, hence

\[
[u,w]=[u,v]=[w,v].
\tag{5}
\]

These determinant trits are equated exactly. If all three horizontal
coordinates coincide, (5) is identically zero; the producer also keeps
the necessary scalar sign-sum relation `v_ac=v_ab+v_bc` among the three
vertical components. No normalization of a zero edge is introduced.

For two upper and two lower vertices, the mixed spatial bracket in
(3) is the cross product of the corresponding cap edge vectors. For
three cap vertices and one opposite vertex, it is the cap triangle
area, with the checked axial sign. Thus all 68 mixed brackets are
linked to (4)–(5). A nonzero determinant trit implies its generic sign;
zero permits either generic completion. The two cap tetrahedron signs
are unrestricted.

Finally, the formula requires a nontrivial stretched configuration:
at least one vertical edge has nonzero normal component, or two
nonvertical edges have unequal slopes. Section 1 proves this
requirement for every actual sequence.

These are necessary geometric constraints only. They need not
characterize every realizable configuration, so UNSAT is sufficient
for exclusion while a Boolean SAT result makes no realization claim.

## 4. Exact exclusions and the four surviving endpoints

The shared Type-7 generic formula, the weak-slope constraints, and the
nontriviality condition are UNSAT for all 16 interior order pairs.
They are also UNSAT for I_zero/II_both and II_sum/II_both, in either
order. This excludes 20 cases.

The four remaining Boolean relaxations are:

| Upper type | Lower type | Limiting zero horizontal weight |
|---|---|---|
| II_sum_right | II_both | `h1` |
| II_sum_left | II_both | `h3` |
| II_both | II_sum_left | `h5` |
| II_both | II_sum_right | `h7` |

The original total `sum h_i=7/2`, together with `h_i<=1/2`, forces every
other weight to equal `1/2`. This proves (1). At the canonical endpoint
`h1=0`, the upper cap has cluster `{1,2,4}` and tip `3`, while the
lower cap has coincident pairs `{0,6}` and `{5,7}`.

For possible further relative estimates, the actual finite sequence
satisfies the exact identity

\[
h_1=\sum_{i\ne1}(\tfrac12-h_i).
\]

Each summand is positive and at most `h1`. This observation does not
by itself control the relative size of the vertical step `b1`.
All four endpoint families are now excluded by the
[complete two-block proof](ray1_two_block_exclusion.md), using the
verified marked equivalence and three exact endpoint contradictions.

## 5. Replay

```sh
python research/type7_completion/remaining_ray1_mask04_blowup.py OUTPUT
```

The producer checks the 68 determinant sign identities symbolically,
the exact triangle identities and vertical cross-product rules, and
all 24 formulas with the finite-domain backend. It writes every input
CNF and a complete `coverage.json`. The 20 UNSAT inputs admit
independent RUP replay. The four SAT entries retain Boolean witnesses
only, with no geometric witness assertion.

A fresh producer and all 20 independent RUP replays passed. Certificate
production and replay took 2.687 seconds in the shared workspace.
