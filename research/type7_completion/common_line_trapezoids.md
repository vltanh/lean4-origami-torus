# Common-line blow-ups with two noncollinear caps

**Conditional reduction.** Suppose a ray-3 sequence has a common-line
transverse limit, and stretching the transverse width produces a bounded
limit in which both caps are noncollinear. Then each original physical
cap limit consists of three coincident vertices and one tip. This includes
all ratios between the width, edge lengths, and `t=1/y²`.

This is a reduction inside the common-line case. The
[triangle-pair proof](remaining_two_triangles_blowup.md) now excludes
the resulting two-tip limits. The complete mixed and two-line covers
then give the [eventual ray-3 exclusion](ray3_boundedness.md), with no
explicit numerical height threshold.

## 1. The necessary shape cover survives stretching

Use transverse coordinates `(X,Y)` with the original limiting line
`Y=0`. Consider an invertible stretch `(X,Y) -> (X,Y/width)` for which
all eight transformed points converge. The original horizontal limiting
coordinate is still `X`; its edge-length cost is the seminorm `|dX|`.
The normalized axial coordinates still tend to the two cap levels.

Every short edge has axial increment bounded by `C*t*h`, with `h` its
original intrinsic length. Stretching does not decrease transverse norms,
up to a fixed bounded coordinate change. Thus the axial increment divided
by the stretched edge norm is still `O(t)`. Normalize a collapsing
stretched edge by its own norm before passing to a subsequence. The
weak direction-order implications, including virtual directions for
vanishing edges, apply exactly as in `exhaustive_cap_shapes.md`.

That finite cover leaves aligned trapezoids or the two V/V alignments.
The [full point-sign proof](exhaustive_vv_geometry.md) excludes both V/V
alignments without any metric assumption. We therefore consider the
trapezoids, allowing one zero base in either cap.

## 2. Bases perpendicular to the physical line are impossible

If their common base direction has zero `X` component, all four physical
base weights vanish. The complementary two legs of each cap then have
weight `1/2`. The exact stress mask gives a sum of either zero or one,
contradicting its required value `1/2`. The symbolic check is included in
`exhaustive_vv_geometry.py`. This argument is independent of the width.

## 3. Nonvertical bases give the same closed rational cones

If the base direction has a nonzero `X` component, a bounded shear of
the stretched `Y` coordinate makes it horizontal while leaving `X`
unchanged. Reflect if needed, and independently scale the two caps by
positive factors to make both leg heights one. The limiting stress
identity is homogeneous under these scalings, including for the seminorm.

After the checked parity symmetry, the edges have the familiar form

```
e=((X,-1),(L,0),(A-L-X,1),(-A,0)),
f=sigma*((U,-1),(M,0),(C-M-U,1),(-C,0)).
```

Here `A,L,C,M>=0`, with at least one positive base in each cap. The
normalized zero-base sign argument of `cap_limit.md` preserves the
separation inequalities

```
U=X-A-M-gap       if sigma=+1,
U=X+C+L+gap       if sigma=-1,          gap>=0.
```

The metric cost is now the absolute horizontal component of every edge.
Consequently the stress equation is exactly `F0=0`, for the quadratic
polynomial and 32 closed sign cones already used in `cap_limit.md`.
There is no Euclidean leg-length excess to invoke in this limit.

## 4. Exhaust every zero of the quadratic cone inequality

The original exact cone proof enumerates 116 extreme rays and checks
652 bilinear ray products, all nonnegative. Write any point of a cone as
`v=sum c_i*r_i`, with `c_i>=0`. If `F0(v)=0`, every ray pair in its
positive support has zero bilinear product, including each self-product.
Thus the zero set is covered by the finitely many ray supports with this
property. There are at most eight rays in any cone, so all supports can
be enumerated directly.

The new checker finds that every zero support has at most two positive
bases. Both noncollinear caps require a positive base; therefore there
is exactly one positive base in each cap. Among all 32 cones there are
16 such ray supports. They all have `gap=0` and one of four pairs of
zero physical edge sets:

| Orientation | A zero edge indices | B zero edge indices |
|---|---|---|
| `+1` | `0,3` | `0,1` |
| `+1` | `1,2` | `2,3` |
| `-1` | `0,1` | `1,2` |
| `-1` | `2,3` | `0,3` |

Indices are cyclic positions in `(0,1,4,5)` and `(2,3,6,7)`. In each
cap the two zero edges are consecutive, so three vertices coincide.
The other two physical edges have equal nonzero length; the original
unit perimeter makes each length `1/2`. The fourth vertex is the tip.

These are identities on each entire zero support. The verifier checks
every vanishing edge on every supporting ray. Since the absolute edge
steps are nonnegative linear forms on a fixed sign cone, no cancellation
between rays can create a false zero at their unit-coefficient sum.
Arbitrary positive ray coefficients give the same cluster conclusion.

## Reproduction

```sh
python3 research/type7_completion/common_line_trapezoids.py
```

The checker uses exact integer and rational arithmetic, enumerates all
extreme rays and every zero support, and imports no nonlinear solver.
This checker establishes the conditional shape reduction. Its resulting
two-tip families are excluded in `remaining_two_triangles_blowup.md`.
