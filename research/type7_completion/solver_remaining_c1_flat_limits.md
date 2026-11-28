# Six explicit families for the two-collinear-cap C1 boundary

Consider a ray-1 C1 limit with `0<alpha,beta<1` in which both endpoint
triangles 234 and 067 are collinear. The five independently replayed
CNFs below, the circle identities, and the marked symmetries reduce
every such limit to six explicit families on a single transverse line.
All six families satisfy the full 29-row limiting metric system and all
six active nonedge inequalities. This is a classification of the
remaining necessary limit system, not an embedding construction or an
exclusion of this boundary.

The subsequent [normal-stretch proof](solver_remaining_c1_flat_stretch.md)
excludes all six families as limits of actual unbounded realizations,
including every endpoint and relative collapse rate. The metric
witnesses here remain valid for the unstretched necessary limit system.

Write `d_i=1/2-h_i`, so `d_i>=0` and `sum d_i=1/2`. The symbols
`P_i` denote transverse points, and the axial heights remain

\[
(0,\alpha/2,1/2,1/2,1/2,\beta/2,0,0).
\]

The companion is `solver_remaining_c1_flat_limits.py`. Its algebraic
checks include the full metric source, exact auxiliary witnesses, the
active nonedge expansions, and all finite-cover height identities.
All five generated CNFs must additionally pass independent RUP replay.

## 1. Collinear triangle orders

First assume `h2,h3,h6,h7>0`. A perimeter-one endpoint triangle is
collinear when its corresponding Heron product vanishes:

\[
d_2d_3(1/2-d_2-d_3)=0,\qquad
d_6d_7(1/2-d_6-d_7)=0.
\]

If `d2+d3=1/2`, all other deficits vanish. Vertex 3 lies strictly
between 2 and 4, so `E2=P2-P3` and `E3=P4-P3` point in opposite
directions. The first circle pair has `d0=d1=0`: `E2` and `Y0` point
in the same direction and `P7` points in the opposite direction.
The lower cap has `P6=0`, so `F=P7-P6=P7`. The second circle pair has
`d4=d5=0`, so `Y5` points with `E3` and `F` points against `E3`.
This contradicts the first pair. All norms used here are positive;
the relevant radii are `alpha*d2+(1-alpha)/2` and
`beta*d3+(1-beta)/2`.

The case `d6+d7=1/2` is analogous: the upper cap has `E3=E2`,
whereas the lower order gives `F` opposite to `P7`; the two
zero-deficit circle pairs require both `P7` and `F` opposite to `E2`.

Consequently the positive-edge cases have both tip angles zero:

\[
E_2=h_2u,\quad E_3=h_3u,\quad P_7=h_7v,\quad F=h_6v,
\qquad |u|=|v|=1.
\tag{1}
\]

There are three upper and three lower orders:

| Label | Upper cap | Lower cap |
|---|---|---|
| A | 4 strictly between 2 and 3 | 0 strictly between 6 and 7 |
| B | 2 strictly between 3 and 4 | 6 strictly between 0 and 7 |
| C | 2=4, with 3 distinct | 0=6, with 7 distinct |

The zero-edge endpoints, where one of `h2,h3,h6,h7` is zero, are
treated in Section 6; no division by such an edge is used in (1).

## 2. Five exact Boolean obligations

The source retains the full necessary generic orientation formula,
actual bracket trits with zero-safe generic completion, all affine
cocycles, weak Grassmann–Pluecker relations, and both strict axial
separations. Both cap triples have zero actual brackets with every
fourth vertex. Specified strict-between orders add their positive
convex interpolation identities; coincidences add exact equality.

The source also adds the two height identities from
[the one-collinear-cap proof](solver_remaining_c1_collinear_rank.md)
and 25 further determinant expansions involving only vertices other
than 5. Every expansion has the form

\[
\alpha[ijkl]=\sum c_{ab}[01ab],
\]

with signed coefficients among `1`, `alpha`, and `1-alpha`. Their
strictly positive magnitudes are dropped only when imposing the
necessary signed-zero-sum condition. The companion expands every
identity in arbitrary transverse coordinates, and checks the
coefficient signs symbolically throughout `0<alpha<1`.

The five UNSAT obligations are:

1. For upper order B and each of the three lower orders, the actual
   bracket `[2367]` cannot be nonzero. Each of these three CNFs has a
   single disjunction of its positive and negative actual trit bits.
2. With both cap triples collinear, actual
   `[0236]=[0237]=[2367]=0` is incompatible with actual
   `[0123]>0` and `[0127]>0`. This CNF assumes no strict line order.
3. With both cap coincidences, actual `[0123]>0` forces actual
   `[3456]=[4567]=0`. Its CNF negates that conjunction of zeros by
   the disjunction of all four nonzero trit bits.

The marked reflection `i -> 6-i` interchanges A and B on both caps.
The marked rotation `i -> i+4` swaps the caps. The exact gauge and
height checks are reused from the preceding package. The companion
checks that every order pair other than CC maps into BA, BB, or BC.
Thus the first three CNFs rule out nonparallel cap lines for all
non-CC order pairs. Reanchoring and a possible transverse reflection
preserve nonparallelism; the CNFs cover both signs of `[2367]`.

## 3. Every anchor bracket vanishes

Use the circle notation

\[
Y_0=\alpha P_2,\quad
R_1=-\alpha P_3,\quad
Y_5=\beta E_3-R_5.
\]

For the first pair put
`p=d0`, `q=d1`, `r=d2`, `t=d7`, `h=h2`, `k=h7`, and

\[
\rho=\alpha(q+r)+(1-\alpha)(1/2-p),\qquad
\sigma=1/2+(1-\alpha)p-\alpha q.
\]

Its projection difference is

\[
Y_0\cdot u-Y_0\cdot v=1-q/h-p/k.
\tag{2}
\]

The numerator of the right side has a nonnegative decomposition:

\[
hk-qk-ph
=\tfrac12(\tfrac12-p-q-r-t)+rt+pr+qt\ge0.
\tag{3}
\]

If the actual normalized anchor `[0123]` is positive, (3) is
strict. Indeed

\[
4[0123]^2=q(2h\rho-q),
\]

and

\[
2h\rho-q
=2\alpha r(1/2-r-q)
 +(1-\alpha)(1/2-p-q-r+2pr).
\tag{4}
\]

Positivity of the anchor implies `q>0`. Equality in (3) would then
give `t=0`, `p+q+r=1/2`, and `pr=0`; (4) would vanish, a
contradiction. These factorizations are checked exactly.

Suppose first that the cap directions are parallel. Equation (2)
and its strictness rule out `v=u`, so `v=-u`. The determinant
identities then give

\[
[0127]=(h_7/h_2)[0123]>0,
\qquad[0236]=[0237]=[2367]=0.
\]

The fourth CNF excludes this possibility.

If the cap directions are not parallel, the first three CNFs and
their symmetry cover leave only CC. The fifth CNF makes
`[3456]=[4567]=0`. Their exact determinant formulas imply that
`Y5` is parallel to both `E3` and `F`, hence `Y5=0`.
This is impossible. For either circle pair, with deficits `p,q`
and parameter `a`, the exact norm identity implies

\[
|Y|^2-(1/2-p-q)^2
=[ap+(1-a)q](1-2p-2q)+[ap-(1-a)q]^2\ge0.
\tag{5}
\]

Here `d1>0` gives `d4+d5<1/2`, so the second pair has `|Y5|>0`.

Thus actual `[0123]=0`. Applying the same result after the checked
reflection, rotation, and their composition proves

\[
[0123]=[0127]=[3456]=[4567]=0.
\tag{6}
\]

If a relabeled anchor were nonzero, the spatial orientation could be
normalized to make it strictly positive and the preceding argument
would apply. No sign of a generic completion of an actual zero is
used in this step.

## 4. All transverse points lie on one line

If `u,v` in (1) were independent, (6) would force both `Y0=0`
and `Y5=0`. But (5) gives

\[
|Y_0|+|Y_5|
\ge 1-(d_0+d_1+d_4+d_5)\ge1/2.
\]

Therefore the directions are parallel. They cannot agree. If `v=u`,
both projection differences vanish. Equation (3) then makes
`d3=d4=d5=d6=0`; the analogous equation for the second pair makes
`d0=d1=d2=d7=0`, contradicting the total deficit. Hence

\[
v=-u.
\tag{7}
\]

The zero anchor and `E2!=0` make `P3` parallel to `u`, and then
`P2,P4,P6,P7` lie on the same line through the origin. The zero
middle anchor similarly makes `R5`, and consequently `P5`, lie on
that line. This includes the cases `Y0=0` and `Y5=0`; neither norm
is divided out.

## 5. The six scalar families

Take `u` as the positive coordinate on the line. The first circle
pair and (7) give

\[
q(2h\rho-q)=0,\qquad
p/k=2\sigma-1+q/h.
\tag{8}
\]

If `q=0`, the second equation is
`p[1/k-2(1-alpha)]=0`. Its bracketed factor is positive because
`k<=1/2` and `alpha>0`. Thus `d0=d1=0`.

If `q>0`, (4) forces `p+q+r=1/2` and `pr=0`. The choice
`p=0` would make the second equation in (8) require
`1-2*alpha*q=0`, impossible for `q<=1/2` and `alpha<1`.
Hence `r=0`, `p+q=1/2`, and all remaining deficits vanish.
Equation (8) now gives `alpha=2q`. This is the left special family.
The same argument on the second pair gives either `d4=d5=0` or
the right special family.

If neither special family occurs, the remaining deficit lies entirely
in the two caps. Since `d2*d3=d6*d7=0`, choose
`i in {2,3}` and `j in {6,7}` and write

\[
d_i=r,\qquad d_j=1/2-r,\qquad 0\le r\le1/2,
\]

with every other deficit zero. The four choices are the ordinary
families. Their transverse coordinates are

\[
\begin{aligned}
P_0&=P_1=0,& P_2&=\frac1{2\alpha},\\
P_3&=\frac1{2\alpha}-\frac12+d_2,&
P_4&=\frac1{2\alpha}+d_2-d_3,\\
P_6&=d_7-d_6,& P_7&=d_7-\frac12,\\
P_5&=\frac\beta{2\alpha}-\frac12
       +\beta(d_2-d_3)+(1-\beta)(d_7-d_6).
\end{aligned}
\tag{9}
\]

The special families, with all unlisted deficits zero, are:

| Family | Deficits | Transverse points `P0,...,P7` |
|---|---|---|
| Left | `d0=(1-alpha)/2`, `d1=alpha/2` | `(0,0,0,1/2,0,1/2,0,1/2)` |
| Right | `d4=beta/2`, `d5=(1-beta)/2` | `(0,0,1/(2alpha),1/(2alpha)-1/2,1/(2alpha),beta/(2alpha),0,-1/2)` |

The left row reverses the transverse coordinate used in (8), so that
`P3>0` in the original axis convention. It has `Y0=0` exactly. The
right row has `Y5=0` exactly. The marked reflection interchanges
these families after its corresponding reanchoring.

## 6. Zero-edge endpoints

If one of `h2,h3,h6,h7` is zero, its deficit equals `1/2` and
all other deficits vanish. These are precisely the endpoints of
the ordinary families in (9). They also follow directly from the
circle identities, without using a zero edge as a direction.

For example, if `h2=0`, then `P2=P3`, `|alpha*P3|=1/2`,
`P6=0`, and the first dot equality gives `P7` opposite to `P3`.
The second pair makes `Y5` point with the nonzero `E3` and opposite
to `F=P7`, so `E3` points with `P3`. This gives (9) at `i=2,r=1/2`.
For the other three endpoints, write `E2=(1/2)e`, with `|e|=1`.
The first circle pair gives
`P3=((1-alpha)/(2alpha))e`, `P2=(1/(2alpha))e`, and
`Y0=(1/2)e`. The remaining directions are fixed as follows:

- If `h3=0`, then `P4=P3`, `P6=0`, and `P7=-(1/2)e`.
  Since `Y5=-R5` has norm `1/2`, its dot equality with
  `F=P7` forces `Y5=(1/2)e`. Hence
  `P5=beta*P3-(1/2)e`.
- If `h6=0`, then `P6=P7=-(1/2)e` and `E3=E2`.
  The nonzero `E3` dot equality gives
  `R5=-((1-beta)/2)e`, hence
  `P5=beta*P3-(1-beta)e`.
- If `h7=0`, then `P7=0` and `E3=E2`. The same `R5`
  equality gives `Y5=(1/2)e`. Its dot equality with the
  nonzero `F` forces `F=-(1/2)e`, so `P6=(1/2)e`
  and `P5=beta*P3`.

These are exactly the other three endpoints of (9). The companion's
full metric check includes all four endpoints: none of its denominators
contains `r` or `1/2-r`.

## 7. Exact metric witnesses and nonedge limits

For each family the companion substitutes (9), or the special row,
into all 24 limiting metric equations and all five product syzygies.
It constructs the 14 auxiliary values from a fixed square subsystem
whose determinant is

\[
2\alpha^3(\beta-1)^2\ne0.
\]

It then checks **all 29 rows** exactly. Every rational auxiliary
witness is retained in the generated JSON. This verifies consistency
of the complete limiting equations, not only of the circle subset.

The active nonedges are 04, 26, and 37, each with two tied vertical
lattice translates. In terms of the retained auxiliary variables,
their limiting residuals are `|Pj-Pi|^2-dx^2+C`, where

| Nonedge | Vertical translate | `dx` | `C` |
|---|---:|---|---|
| 04 | 0 | `d0+d1+d2+d3` | `H4+q14/(1-alpha)` |
| 04 | -1 | `d0+d1+d2+d3-1/2` | `H4+q05/beta` |
| 26 | 0 | `d2+d3+d4+d5-1/2` | `-H6+H2+w` |
| 26 | 1 | `d2+d3+d4+d5` | `-H6+H2-w+q25/(1-beta)` |
| 37 | 0 | `d3+d4+d5+d6-1/2` | `-H7+H3` |
| 37 | 1 | `d3+d4+d5+d6` | `-H7+H3+q47` |

These residuals must be nonpositive. The companion checks their
first-order expansions directly in the original squared distances.
The product equations, with `alpha,beta` fixed in the interior, give
bounded first-order rates

\[
q_{05}=2\beta a_3,\quad
q_{14}=2(1-\alpha)(a_3-a_4),\quad
q_{25}=2(1-\beta)(a_2-a_3),\quad
q_{47}=2(a_3-a_7).
\]

Here `v2,v3,v4=1/2+t*a2,a3,a4`, `v7=t*a7`, and
`v6=t*(a3+w)`; the finite parameters `2v1` and `-2v5` are used as
`alpha,beta` before passing to their limits. Thus no unproved rate
assumption is introduced. The six horizontal translations above are
actual lattice translations, so their necessity does not depend on a
numerical nearest-point choice.

In the displayed order of the six inequalities, the residuals are:

| Family | Six residuals |
|---|---|
| `(i,j)=(2,6)` | `2r/(alpha-1), (2r-1)/beta, 0, 0, 0, 0` |
| `(2,7)` | `2r/(alpha-1), 0, (2r-1)/alpha, 0, 2r(2r-1), 0` |
| `(3,6)` | `0, (2r-1)/beta, 0, 2r/(beta-1), 0, 2r(2r-1)` |
| `(3,7)` | `0, 0, (2r-1)/alpha, 2r/(beta-1), 0, 0` |
| Left | `0,0,0,0,-1,0` |
| Right | `0,0,0,0,0,-1` |

All are nonpositive on the stated closed `r` interval and open height
rectangle. The many equalities explain why these first-order
contraction inequalities do not exclude the remaining families.

## Reproduction and scope

```sh
python research/type7_completion/solver_remaining_c1_flat_limits.py /tmp/c1-flat-limits
python research/type7_completion/solver_cnf_certificates.py /tmp/c1-flat-limits-rup \
  --checker /tmp/type7-rup-check /tmp/c1-flat-limits
python research/type7_completion/solver_cnf_certificates.py /tmp/c1-flat-limits-rup \
  --checker /tmp/type7-rup-check --replay-only
```

The regular-cap and exactly-one-collinear-cap C1 cases are treated in
their separate verified packages. The present result identifies the
two-collinear-cap boundary and supplies the exact families used in
the subsequent [complete normal-stretch exclusion](solver_remaining_c1_flat_stretch.md).
This classification package does not assert a finite
height threshold, a Lean closure, or a realizable embedding.
