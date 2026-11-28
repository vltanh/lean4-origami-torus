# C1 implications with one collinear endpoint cap

This package treats a collinear upper cap 234 and a noncollinear,
**positively oriented** lower cap 067, with `0<alpha,beta<1`.
Its five CNFs prove weak signs of the actual limiting brackets. They
retain arbitrary generic completion signs wherever an actual bracket is
zero. Independent RUP replay is required before using the implications.

## The three collinear orders

For ray 1, a noncollinear lower cap leaves
`delta2+delta3<1/2`. The perimeter-one upper cap is collinear precisely
when `delta2*delta3=0`. Thus its possibilities are:

| Parameters | Exact projected order |
|---|---|
| `delta2=0`, `0<delta3<1/2` | 4 strictly between 2 and 3 |
| `delta3=0`, `0<delta2<1/2` | 2 strictly between 3 and 4 |
| `delta2=delta3=0` | 2 equals 4, with 3 distinct |

In all three cases `E3` is a positive multiple of `E2`, so the upper
turning angle `A` in the [turning proof](solver_remaining_c1_turning.md)
is zero. The lower turning angle remains strictly positive.

## Actual brackets and generic completions are separate

The source is the shared necessary Boolean formula for both remaining
markings. Add two trit bits to each of the 70 actual limiting brackets:
positive, negative, or both false for zero. A nonzero trit forces the
corresponding generic sign. A zero trit imposes no generic sign.

The following constraints are necessary for actual point coordinates:

- The affine five-point cocycle has signed bracket sum zero.
- A point strictly between two others is their convex combination. Every
  bracket containing it is the corresponding positive weighted sum of
  the two substituted brackets. A duplicated vertex gives zero. The
  coincident case uses an exact equality instead.
- Every three-term rank-four Grassmann–Pluecker identity holds. Product
  trits use the complete exact three-valued multiplication table.
- A zero real sum either has both positive and negative terms, or all
  terms are zero. This is imposed on each cocycle, interpolation, and GP
  relation; no magnitude information is invented.
- The positively oriented lower triangle has strictly positive ordered
  brackets `[067j]` for all five outside vertices.

For a convex interpolation the coefficient values are deliberately not
encoded: they are positive, so the resulting signed-sum condition is
necessary. This is a relaxation, sufficient for an UNSAT proof.

The generic completion also retains both strict axial separations:
234 lies above the other vertices, and 067 lies below the other vertices.
Every five-point Radon partition crossing either cut is forbidden. The
height gaps are positive at these fixed interior parameters and persist
under a sufficiently small generic perturbation, even when 234 is
collinear. The two cuts therefore constrain generic signs directly.

The script symbolically checks the affine cocycle, convex interpolation,
and a universal GP identity. Its determinant parity is explicit for
all ordered bracket references.

## The five checked implications

For either strict collinear order, if actual `[0123]>0`, the source proves

\[
[0127]\le0,\qquad [3456]\le0,\qquad [4567]\le0.
\tag{1}
\]

For all three orders, without the strict-anchor assumption, it proves

\[
[0127]\le0,\qquad [4567]\le0.
\tag{2}
\]

Each CNF negates the conjunction of its claimed nonpositive signs by a
single disjunction of positive actual trit bits. Thus zero values remain
allowed in every conclusion.

For the ray-1 metric, `delta1>0` supplies the strict-anchor assumption in
(1). Put `p=delta0`, `q=delta1`, `r=delta2`, `h=h2=1/2-r` and
`rho=alpha(q+r)+(1-alpha)(1/2-p)`. The circle identity gives

\[
\cos\phi=1-\frac{q}{h\rho},
\]

where `phi` is the angle of `E2` against the positive face axis. Exact
expansion gives

\[
2h\rho-q
=2\alpha r(1/2-r-q)
 +(1-\alpha)(1/2-p-q-r+2pr)>0.
\]

The lower regular cap makes `1/2-p-q-r>0`; `0<alpha<1` makes the second
summand strictly positive. For `q>0`, therefore `-1<cos(phi)<1`.
The normalized anchor bracket is nonzero and positive.

## Metric consequences

The turning proof remains valid when `A=0`: its strict gap uses
`R=delta2+delta7>0` and `L=delta3+delta6>0`, which follow from the regular
lower cap even when one or both upper deficits vanish. Its lower angle
`B` is positive, so the final negative cross product remains strict.

Consequently (1) excludes both strict collinear orders when `delta1>0`.
The coincident order is not included in that particular conclusion.

There is a second useful exclusion. If `delta4=0`, the metric identities
`|R5|=rho5` and `R5·E3=-h3*rho5` imply that `R5` is antiparallel to
`E3`, hence `cross(E3,Y5)=0`. The middle orientation sign normally
provided by `[3456]<=0` is then automatic. The two signs in (2), together
with the always weak normalized anchor sign, give the same turning
contradiction. This excludes **all three orders when `delta4=0`**,
including `delta1=0` and the coincident pair 2=4.

These are conditional boundary exclusions. The
[rank and symmetry companion](solver_remaining_c1_collinear_rank.md)
now supplies the negative-cap cases and closes all interior limits
with exactly one collinear cap, including coincident vertices.
Two collinear caps still require further analysis; the entire collinear
boundary is not claimed closed.

## Reproduction

```sh
python research/type7_completion/solver_remaining_c1_collinear.py /tmp/c1-collinear
python research/type7_completion/solver_cnf_certificates.py /tmp/c1-collinear-rup \
  --checker /tmp/type7-rup-check /tmp/c1-collinear
python research/type7_completion/solver_cnf_certificates.py /tmp/c1-collinear-rup \
  --checker /tmp/type7-rup-check --replay-only
```

The generated metadata records every case, actual strictness assumption,
claimed sign, and exact CNF size. All five original CNFs must be checked;
raw SAT-backend statuses are not proof certificates.
