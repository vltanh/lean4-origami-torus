# Ray 3: a quadratic metric chart and exact nonedge reduction

`remaining_null_metric.py` gives an exact alternative to the 27-variable
quartic chart. It uses **29 variables and 21 quadratic metric equations**,
with no radicals or divisions by variable expressions. Three equations
are differences of anchor distances and are linear in the corresponding
spatial vertex coordinates. The full necessary generic-sign, linking,
and degeneracy-complete circuit constraints are retained. No full phase
is excluded by this change.

## 1. Fix an actual face

Put `t=1/y^2`, `c_i=1` on cap `2367` and zero on cap `0145`. Use a spatial
isometry to place face `023` exactly in its intrinsic plane:

- `r_0=(0,0,0)`;
- `r_2=(x_2,-y/2+gamma_2/y,0)`;
- `r_3=(x_3,-y/2+gamma_3/y,0)`.

This is possible for every realization because face `023` is nondegenerate
and isometric to its intrinsic triangle. Write the other five vertices as

`r_i=(u_i,-y*c_i/2+zeta_i/y,z_i)`.

There are fourteen intrinsic variables and fifteen spatial variables.
Reflection in the anchor plane fixes the remaining orientation ambiguity.
The archived intrinsic area of face `023` is negative, so `z_1<0` makes
the clique bracket `0123` positive. K4 nondegeneracy makes this inequality
strict. No lower bound for a cap area or an edge length is assumed.

For an edge let `ell=c_j-c_i`, `dg=gamma_j-gamma_i`, and
`dzeta=zeta_j-zeta_i`. Its baseline intrinsic vertical displacement `ky`
satisfies `ky^2=ell^2/4`. Cancellation of the common `y^2*ell^2/4` terms
gives the exact equation

`(du)^2+(dz)^2-X_ij^2-ell*dzeta-2*ky*dg+t*(dzeta^2-dg^2)=0`.

All terms are quadratic. The three anchor-face edge equations hold
identically, leaving twenty-one. For vertices `1,5,7`, subtract their
edge-to-2 equation from their edge-to-0 equation; this cancels their
`u_i^2`, `z_i^2`, and `zeta_i^2` terms. The generator retains one original
equation and the exact difference for each pair.

## 2. Uniform coordinate bounds

The long-ring shortest-lift bounds imply
`-1/8<gamma_j-gamma_i<3/8` on each directed edge of `0246` and `1357`.
Indeed, each normalized vertical edge step is greater than
`-1/2-t/8`, and their four-step sum is exactly `-2`. Applying the three
other lower bounds gives the upper bound `-1/2+3*t/8` for each step.
In particular `-1/8<gamma_2<3/8`. Set

`a=1-2*t*gamma_2`, `den=a^2+4*t*x_2^2`.

At `y>=8`, `a>253/256` and `sqrt(den)<33/32`.
For a short edge, the existing physical axial bound relative to `02`
and the cap edge length bound imply

`|d zeta| < (2*|x_2|*|d u| + 5*h*sqrt(den))/a < 7*h`.

Thus every point's `zeta` differs from its own cap anchor by less than
`7/2`, including arbitrarily short edges. Each cap point lies within
`33/64` of its anchor in physical space, bounding `(u,z)` as well.
The short-edge metric equation also gives the quadratic estimates

`(1-49*t)*h^2 < (du)^2+(dz)^2 < (1+t*(1/2+t)^2)*h^2`.

These estimates are necessary cuts, not replacements for the metric
or embedding equations.

The explicit cap bounds also make the 24 earlier phase tests redundant.
On a short edge, `|dg|<(1/2+t)/2<7/4`. On a cross edge,
`|dg|<3/8+(1/2+t)<7/4`. Thus every cross-edge vertical displacement
has the sign of its fixed `ky=+/-1/2` and the required magnitude.
The generator removes all 24 repeated phase tests, including sixteen
absolute-value disjunctions.

## 3. Two translates suffice for each missing edge

Every missing edge joins opposite vertices of one short cap ring. Its
two two-edge arcs have intrinsic horizontal displacements `-s` and
`1-s`, where `0<s<1`; both have vertical displacement `t*dg`.
The relative gamma bound gives `|dg|<1/4+t/2`. Consequently the nearer
horizontal arc has squared physical length below one, while every
nonzero vertical translate has squared vertical length greater than
sixteen at `y>=8`. Among the zero-vertical translates, `-s` and `1-s`
contain a closest horizontal translate.

Therefore the two arc inequalities are exactly sufficient to impose
contraction against every lattice translate. This reduces the previous
252 finite-translate inequalities to **eight quadratic inequalities**,
two for each missing edge. Positive spatial nonedge distances are retained.

## 4. Incidence and the relative area union

Use incidence coordinates `(u_i,z_i,c_i-2*t*zeta_i)`. The linear map from
physical coordinates has determinant `2/y>0`. It therefore preserves
all affine circuits and oriented full minors. For a minor involving the
third coordinate whose points all lie in one cap, dividing by positive
`2*t` replaces that coordinate by `-zeta_i`; this preserves its sign and
zero set. All 322 inherited incidence definitions are replaced in this
way, retaining every actual degeneracy test.

For a short edge, its coordinate in the transverse direction perpendicular
to `02` inside the anchor plane is

`(a*du+2*t*x_2*d zeta)/sqrt(den)`.

Hence, writing `D_old` for the orthogonal transverse determinant and
`D_uz=du_e*dz_f-dz_e*du_f`,

`sqrt(den)*D_old = a*D_uz + 2*t*x_2*(d zeta_e*dz_f-dz_e*d zeta_f)`.

The established relative union supplies `|D_old|<=36*t*h_e*h_f` for
at least one of the same twenty-four comparisons. Using the bounds
above gives

`|D_uz| < (13200/253)*t*h_e*h_f < 53*t*h_e*h_f`.

The new query uses the inclusive coefficient `53`. Both sides are
quadratic, and zero determinants remain allowed. Cap-triangle weights
still refer to consecutive ring edges, including when the determinant
is written using a diagonal.

## 5. Cancel positive anchor factors exactly

Two anchor factors can approach zero, but are strictly positive in every
admissible placement:

`h23=x2-x3>0`,

`A=x2*(1-2*t*gamma3)-x3*(1-2*t*gamma2)=-2*area023>0`.

The incidence definitions are used only in sign and zero tests. Five
full brackets containing face `023` equal `-A*z_i`: the sorted brackets
`0123`, `0234`, `0235`, `0236`, and `0237`. Their definitions may therefore
be replaced by `-z_i`. The two-dimensional minor `a023c02` equals `A`
and may be replaced by `1`. Finally, `a236c01=-h23*z6` and
`a237c01=-h23*z7` may be replaced by `-z6` and `-z7`.
These eight positive rescalings preserve every strict sign, weak sign,
and zero boundary. They do not assume a uniform lower bound on `A` or
`h23`.

The anchor edge `23` has transverse vector `(-h23,0)`. For each of the
four comparisons of an A-cap edge with `23`, the relative area atom is
therefore equivalent to

`|delta z_A| <= 53*t*h_A`.

The cap atoms `236` and `237` similarly become
`|z6|<=53*t*h36` and `|z7|<=53*t*h72`. These six atoms are linear,
and their equality boundaries are retained. Dividing out the strictly
positive `h23` prevents a tiny anchor edge from hiding the directional
constraint.

## Verification

```sh
python3 research/type7_completion/remaining_null_verify.py
python3 research/type7_completion/remaining_null_metric.py /tmp/type7-face023.smt2
```

The independent checker compares every metric expression against physical
squared distances in exact rational coordinates, checks all 322 incidence
minors and all 70 physical full brackets, verifies zero fixtures, checks
the two-arc cocycle identities and rational constants, establishes degree
two for every metric equation, checks the eight symbolic factor identities
and all six normalized area atoms, and parses the full query. The full
query retains 29 reals, 312 Booleans, and 524 actual circuit partitions;
the finite chamber compiler removes the Boolean variables and the
separately proved redundant circuit tests. A solver result or complete
marking exclusion is a separate requirement.
