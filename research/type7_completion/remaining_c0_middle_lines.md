# The remaining common-line C0 limits are impossible

No unbounded embedded ray-1 sequence has an interior C0 limit in any
of the four middle-deficit line families or either line direction of
the coincident-vertex circle. Together with the
[endpoint proof](remaining_c0_line_endpoints.md) and the
[nonflat circle proof](exhaustive_c0_circle.md), this excludes **every
interior C0 limit whose two endpoint caps lie on one common line**.
The [nonparallel-cap proof](exhaustive_c0_flat_asymmetric.md) therefore
completes the other part of the both-collinear interior stratum.

There are 66 independently replayable Boolean obligations. The
additional analytic ingredient is a cap-area blow-up relative to both
the shrinking diagonal and the actual normal width. No two rates are
assumed comparable.

## 1. The six families and a nontrivial normal stretch

Use the [classified families](exhaustive_c0_flat_common.md). In every
one of the six remaining cases,

\[
P_0=P_1=P_3=P_6=0,\qquad P_2=-e/2,\qquad P_7=e/2,
\]
\[
z=(0,1/2,1/2,1/2,u,v,0,0),\qquad 0<u,v<1/2.
\]

The four middle families have the strict height orders and coordinates
listed in the preceding classification; the two diagonal families
have `u=v` and `P4=P5=±e/2`. In all six cases `h0=1/2` and `h3>0`.

For each finite realization, rotate the transverse plane so that
`P2` lies on the negative horizontal axis. Write `Pi=(Xi,Yi)`, and put

\[
\delta=\max_i|Y_i|>0.
\]

Positivity follows from finite K4 nondegeneracy. The common-line limit
gives `delta -> 0`. Pass to a subsequence after the positive affine
stretch `(X,Y,zeta) -> (2X,Y/delta,2zeta)`. Its bounded limit has
normal coordinates `Ni`, with `N0=N1=N2=0` and `max |Ni|=1`.

The original [normal source](solver_remaining_c0_flat_stretch.md),
including all actual-zero brackets and the full generic topology and
linking conditions, forces

\[
N_3=N_6=0.                                                   \tag{1}
\]

One fresh CNF for each family independently proves precisely (1).
Thus at least one of `N4,N5,N7` is nonzero. The checker replays all
twelve closed projected metric stresses on each of the six families.

## 2. Two short diagonals with independent normalizations

At every finite stage the positive horizontal diagonal lengths are

\[
L=d_1+d_2=X_{13}>0,\qquad
M=d_6+d_7=-X_{06}>0.
\]

Both tend to zero in the present families. The already source-checked
[upper](exhaustive_c0_double_coincidence.md) and
[lower](exhaustive_c0_double_flat.md) relative estimates give

\[
|P_3|/L\to1,\quad \zeta_3-\zeta_1=O(tL),\qquad
|P_6|/M\to1,\quad \zeta_6=O(tM),\quad t=1/y^2.                \tag{2}
\]

Their absorption coefficients are `-(1-2u)` and `2v`, both nonzero
throughout the open height square. These estimates do not require
nonparallel cap lines. The new checker replays their finite metric
identities and cocycle bindings.

For diagonal 13 consider

\[
\rho_3=\max(2L,|Y_3|/\delta).
\]

If `rho3/L -> infinity`, division of the stretched diagonal by its
positive scale `rho3` gives a nonzero pure normal direction
`(0,Y,0)`. Its axial component tends to zero by (2). Otherwise divide
by `2L`. The normal component stays bounded, so `Y3/L -> 0`; the unit
transverse estimate in (2) gives a horizontal component `c3=±1`.
The resulting virtual direction is `(c3,Y,0)`.

Apply the identical dichotomy independently to diagonal 06, obtaining
`(c6,Z,0)`, with `c6` in `{-1,0,1}` and `Z != 0` if `c6=0`.
There is no comparison between `L`, `M`, `delta`, or `t`.

All 29 brackets containing pair 13 or pair 06 are normalized by their
own positive short-column factors; bracket 0136 is divided by their
product. Factoring both columns before taking limits prevents any
uncontrolled ratio of their lengths. The checker expands each
determinant directly. Its limiting expression is linear in
`N4,N5,N7,Y,Z`; every coefficient sign is certified by exact
multiaffine interpolation over the complete open parameter square.

A nonzero normalized determinant fixes the same generic completion
sign as the original finite determinant. A zero normalized determinant
leaves that sign free. Differently normalized brackets are not assigned
an unjustified common affine cocycle.

Seven CNFs per family exclude all virtual-direction cases except

\[
(c_3,c_6)=(-1,-1)\quad\hbox{or}\quad(+1,+1).                 \tag{3}
\]

For the negative case, six further CNFs prove

\[
Y=0,\qquad\text{equivalently }Y_3/(L\delta)\longrightarrow0. \tag{4}
\]

The lower virtual normal `Z` is not set to zero. It remains unrestricted
except for the existing exact source relations.

## 3. A relative cap tilt excludes both negative directions

Suppose the first alternative in (3) occurs. Use the finite rates

\[
a_2=(\zeta_2-\zeta_1)/t,\qquad
a_3=(\zeta_3-\zeta_1)/t.
\]

The relative estimates and the existing upper-cap polarizations make
`a2` and `a3/L` bounded. After taking a subsequence let their limits be
`a2` and `A`. The physical virtual direction is `P3/L -> -e=2P2`.
The exact source combination already checked in the upper relative
proof gives

\[
\kappa:=\frac A2-a_2=\frac{h_3}{1-2u}>0.                    \tag{5}
\]

Let `Cij=Pi × Pj` and `B=C23`. The normalization of the actual
finite configuration has generic `chi0123=+`, so `B>=0`. For
`j=4,5,7` the following identity holds exactly:

\[
[123j]=(\zeta_j-\zeta_1)B
       +t(a_2C_{3j}-a_3C_{2j}).                            \tag{6}
\]

Because `Y2=0` exactly, (4) retains the full normal factor:

\[
\frac{C_{2j}}\delta\to-\frac{N_j}{2},\qquad
\frac{C_{3j}}{L\delta}\to-N_j.
\]

Consequently (5) gives

\[
\frac{a_2C_{3j}-a_3C_{2j}}{L\delta}\to\kappa N_j.           \tag{7}
\]

The checker verifies this cross-product factorization independently.
In particular the error in (7) is small relative to `L delta`, not
merely small relative to `L`. This is what makes the argument valid
even when the normal width collapses faster than inverse height.

Pass to a further subsequence for the nonnegative ratio

\[
\beta_n=\frac{B_n}{t_nL_n\delta_n\kappa}.
\]

There are two exhaustive possibilities:

* If `beta_n -> beta < infinity`, dividing (6) by its positive scale
  gives the limiting form
  `Hj beta + Nj`, where `Hj=zj-1/2<0`. The finite sign of every
  nonzero form agrees with generic `chi123j`; zero stays free. One
  CNF per family shows that these three linear sign constraints,
  `beta>=0`, and the complete virtual source are inconsistent.
* If `beta_n -> infinity`, the second term in (6) is `O(t L delta)`
  by (7), so `[123j]/B -> Hj<0`. Thus all three generic signs
  `chi1234,chi1235,chi1237` must be negative. One CNF per family
  excludes this alternative too.

These twelve CNFs close both negative virtual directions in all six
families, including `beta=0` and all actual-zero normalized brackets.

## 4. Reflection excludes both positive directions

Use the checked marked reflection `p(i)=1-i mod 8`, translate to old
vertex 1, and apply spatial inversion. It preserves the ray-1 marking
and sends

\[
(u,v)\longmapsto(1/2-v,1/2-u),\qquad
(P'_2,P'_7)=(-P_7,-P_2).
\]

It exchanges the positive and negative families separately in each
of the `u<v`, `u>v`, and diagonal pairs. In the polynomial family
parameters, the exact substitution is `(a,b) -> (1-a,b)`; all eight
coordinates, heights, and deficits are checked symbolically.

The new diagonal 13 is minus the old diagonal 06, and the new diagonal
06 is minus the old diagonal 13. Thus a sequence with both physical
unit directions positive becomes one with both physical unit
directions negative. Choose the new transverse normal orientation to
restore `chi0123=+`, which leaves the horizontal directions unchanged.

The normal width of the reflected sequence need not be comparable to
the old width. Repeat the complete normal-stretch dichotomy for that
sequence. Pure normal virtual directions are excluded by Section 2;
the physical negative unit directions therefore put it in the
negative alternative of (3), already excluded by Section 3. This
avoids assuming any relation between the two normal gauges.

All six residual line families are consequently impossible.

## Reproduction and scope

```sh
python research/type7_completion/remaining_c0_middle_lines.py /tmp/c0-middle-lines
python research/type7_completion/solver_cnf_certificates.py /tmp/c0-middle-lines-rup \
  --checker /tmp/type7-rup-check /tmp/c0-middle-lines
```

All 66 obligations require independent RUP replay. They comprise six
normal-zero implications, 42 virtual-direction exclusions, six upper
virtual-normal implications, and twelve cap-tilt exclusions. The
producer also replays the two finite relative metric sources, 29
divided determinants in every required case, the exact normal-factor
identity, all six marked family reflections, and the original twelve
projected stresses per family.

Together with the preceding endpoint, circle, and nonparallel proofs,
this completes **the entire both-collinear interior ray-1 C0 stratum**.
It does not exclude one-collinear-cap cases or degenerate height
boundaries, and it does not claim a complete ray-1 or Lean theorem.
