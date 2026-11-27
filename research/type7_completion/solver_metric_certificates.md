# Exact relative metric exclusions for three weak chambers

For every `y>=8`, a five-sign obstruction excludes the complete weak
phase chambers **129, 130, and 131** in the 132-chamber enumeration.
Chamber 131 already has a final-polynomial exclusion, so this gives two
additional cases. Together with the final-polynomial proof of chamber
23, four chambers are excluded and 128 remain. This does not exclude a
complete marking or finish Type 7.

The argument uses one relative metric comparison and the five-point
affine cocycle. The search used a linear program, but the certificate
below is checked by exact determinant identities and rational arithmetic;
no numerical feasibility result is trusted.

## 1. Raw brackets and uniform bounds

All brackets in this note are **raw affine determinants in one common
coordinate frame**. They are not the individually rescaled incidence
definitions used by the generated SMT query. For example, the query
replaces `a0237c012=-A*z7` by `-z7`, where `A>0`. This preserves its sign
and zero set, but its magnitude must be multiplied by `A` before use in
an affine cocycle or a metric magnitude comparison.

Use the face-023 chart of `remaining_null_chart.md`, with `t=1/y^2`,
`beta=1/2+t`, and incidence points

`P0=(0,0,0)`,

`P2=(x2,0,1-2*t*gamma2)`,

`P3=(x3,0,1-2*t*gamma3)`,

`Pi=(ui,zi,-2*t*zeta_i)` for `i` in `{1,4,5}`.

Let `h=x2-x3>0`, `dg=gamma3-gamma2`, and

`A=x2*(1-2*t*gamma3)-x3*(1-2*t*gamma2)`.

The previously proved uniform coordinate bounds give

- `gamma2<3/8` and `|x2|<1/2`;
- `|dg|<beta*h`;
- `|zeta_i|<7/2` and `|ui|<33/64` for `i` in `{1,4,5}`.

In particular,

`A/h > 1-3*t/4-t*beta >= 4015/4096 > 31/32`.

This is a relative lower bound. Neither `A` nor `h` is assumed to have
a positive absolute lower bound, and both may tend to zero along a
sequence of admissible placements.

## 2. A relative comparison with no lost zero boundaries

Choose distinct `i,j` from `{1,4,5}`. Direct expansion gives

`[0ij3]-[0ij2] = -2*t*(h*(zeta_i*zj-zi*zeta_j)`
`                              +dg*(ui*zj-zi*uj))`,

and

`[023i]=-A*zi`, ` [023j]=-A*zj`.

If the assigned weak signs of the ordered brackets `[0ij2]` and
`[0ij3]` are opposite, their actual values are opposite or zero. Hence
their difference has magnitude equal to the sum of their magnitudes.
The coordinate bounds then imply

`|[0ij2]|+|[0ij3]|`

` <= t*h*(7+(33/32)*beta)*(|zi|+|zj|)`

` <= 8*t*(|[023i]|+|[023j]|)`.

The last step follows from
`(32/31)*(7+(33/32)*(1/2+1/64))<8`.
The conclusion is inclusive, so it retains every zero boundary.
It applies to all sixteen phase-preserving marked metric symmetries.
Those symmetries preserve distances and affine brackets up to relabeling
and one common orientation sign. Resetting the face chart is a rigid
motion; its incidence scaling has the same fixed factor `2/y`.

## 3. The five-sign obstruction

Suppose the weak bracket signs, after an allowed relabeling and one
common orientation choice, are

| Bracket | Sign |
|---|---|
| `0123` | `+` |
| `0127` | `-` |
| `0137` | `+` |
| `0237` | `+` |
| `1237` | `-` |

The clique bracket `0123` is strictly positive. The other four signs
may be weak: no extra nonvanishing assumption is used.

Apply the relative comparison with `i=1`, `j=4`, and the verified
phase symmetry `(3,2,1,0,7,6,5,4)`. In the displayed labels it becomes

`|[0237]|+|[1237]| <= 8*t*(|[0123]|+|[0137]|)`.

The exact five-point affine cocycle is

`[1237]-[0237]+[0137]-[0127]+[0123]=0`.

With these signs it says

`|[0237]|+|[1237]| = |[0123]|+|[0137]|+|[0127]|`.

Since `8*t<=1/8<1`, these two relations contradict `|[0123]|>0`.
For a particularly simple rational certificate, weaken `8*t` to `1/2`
and add the cocycle to the resulting inequality. This gives

`(|[0123]|+|[0137]|)/2+|[0127]| <= 0`,

although all terms are nonnegative and the first is positive.

## 4. Exact checking and compiler integration

Run the standalone checker:

```sh
python3 research/type7_completion/solver_metric_certificates.py
```

It symbolically expands the determinant-difference identity, the two
anchor-bracket identities, and the generic affine cocycle; checks the
uniform rational constants; verifies the marked symmetry; matches the
five signs in chambers 129, 130, and 131; and checks the final rational
coefficient cancellation. It does not import or trust the search LP.

`solver_chambers.py` records each applicable certificate in the manifest
and omits its nonlinear query. `solver_verify.py` repeats the exact
identities and coefficient checks, verifies that the strict bracket is
an actual K4, and binds the chamber coverage to the independently checked
CNF. The original final-polynomial certificates are retained, including
the overlapping certificate for chamber 131. The manifest retains all
132 representatives, of which 128 still require metric exclusion.
