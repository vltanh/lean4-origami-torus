# Ray 3: relative cap bounds, including arbitrarily short edges

## Status

For every actual canonical `ray3_phase0` realization at `y>=8`, all eight
short edges have negative horizontal intrinsic displacement and satisfy a
uniform relative slope bound. Their extrinsic projections perpendicular to
edge `02` are nonzero, even when an edge is arbitrarily short. This removes
an axial, vanishing-edge exception from the cap analysis. It does **not**
exclude the full phase: nearly parallel projected directions remain.

The metric estimates below use edge-length equality, strict nearest lifts,
the established phase localization, and consistent intrinsic face
orientation. They do not use the strict-support or orientation-SAT
premises. The final application of the existing two-cap obstruction uses
the hand-proof geometric lemmas in [the audit](geometric_audit.md).
No new marking is closed, and the Lean bridge remains open.

## 1. Notation and exact eight-entry stress identity

Use the cyclic short rings

    A=(0,1,4,5), B=(2,3,6,7), w=y^2.

For an oriented graph edge `e=ab`, write its intrinsic physical vector as
`a_e=(X_e,y*V_e)` and its spatial vector as `E_e=r_b-r_a`. For a short
edge put `gamma_e=w*V_e`. The established canonical-phase bounds are

    |X_e|<1/2, |V_e|<7/(4*w), |E_e|<11/20,

where the last inequality follows at `w>=64` from
`|E_e|^2<1/4+49/(16*w)`. Every cross edge has baseline vertical
displacement `+1/2` or `-1/2`, with error less than `7/(4*w)`.

For cyclic A-edge `ab` and B-edge `cd`, define

    R(ab,cd) = a_ab dot a_cd - E_ab dot E_cd.

All four cross distances are prescribed edges, so polarization gives

    E_ab dot E_cd = (D_ad+D_bc-D_ac-D_bd)/2.

Substituting the archived ray-3 cocycle gives these **exact**, finite-`w`
identities. Each of the eight short edges occurs once in the right column.

| A-edge | B-edge | Exact value of R |
|---|---|---|
| 01 | 36 | `-X_01/2-gamma_01` |
| 14 | 23 | `-X_14/2+gamma_14` |
| 45 | 72 | `-X_45/2-gamma_45` |
| 50 | 67 | `-X_50/2+gamma_50` |
| 50 | 23 | `-X_23/2-gamma_23` |
| 45 | 36 | `-X_36/2+gamma_36` |
| 14 | 67 | `-X_67/2-gamma_67` |
| 01 | 72 | `-X_72/2+gamma_72` |

Both rings have period `(-1,0)`. The sum of the oriented face double
areas, in the archived face orientations, is identically `-2`.
Consequently a consistently oriented degree-one intrinsic realization
has negative area at every listed face.

## 2. Uniform relative intrinsic slope

**Theorem.** Every short edge satisfies

    X_e<0, |gamma_e|<2*(-X_e).

First apply the absolute Cauchy bound to the stress entry associated to
`e`. If `f` is its partner short edge, equality of intrinsic and spatial
edge lengths gives

    |R(e,f)| <= 2*|a_e|*|a_f|
              < (11/10)*sqrt(X_e^2+gamma_e^2/w).

The sign and order of the two factors do not affect this inequality.
The exact table and `sqrt(u^2+v^2)<=|u|+|v|` therefore give

    |gamma_e| < (8/5)*|X_e| + (11/(10*y))*|gamma_e|.

At `y>=8`, this implies

    |gamma_e| < (128/69)*|X_e| < 2*|X_e|.

In particular `X_e` cannot vanish: it would force `gamma_e=0`, violating
positive edge length. This argument makes no division by an edge length.

To determine its sign, choose the following positively ordered face for
each oriented ring edge. The third vertex `c` has canonical
`V_ac>1/2-7/(4*w)` in all eight rows.

| Edge ab | Third vertex c |
|---|---|
| 01 | 6 |
| 14 | 2 |
| 45 | 2 |
| 50 | 6 |
| 23 | 0 |
| 36 | 4 |
| 67 | 4 |
| 72 | 0 |

The face double area is `X_ab*V_ac-V_ab*X_ac`. The second term has
magnitude less than `|X_ab|/w`, while the first has magnitude greater
than `(1/2-7/(4*w))*|X_ab|`. Since `w>=64`, the first dominates, so the
area has the sign of `X_ab`. All these areas are negative; hence
`X_ab<0` as claimed.

Put `h_e=-X_e>0`. The winding identities now give

    sum_A h_e = sum_B h_e = 1,   0<h_e<1/2,
    |E_e|^2 < (1+4/w)*h_e^2,   |E_e|<(33/32)*h_e.

Each short ring has perimeter less than `33/32`. Any two of its vertices
are joined by a ring path of at most half that perimeter, so its vertex
set and convex hull have diameter less than `33/64`.

### Sharpening by the exact row and column sums

In fact the relative slope has the stronger bound

    |gamma_e| < (1/2+1/w)*h_e.

Write `q_e=gamma_e/h_e` and let `Q` be the maximum of their eight absolute
values, already known to be less than 2. If `e,f` are cap edges in
opposite rings, edge-length equality gives the exact identity

    R(e,f)/(h_e*h_f)
      = (|E_e/h_e-E_f/h_f|^2-(q_e-q_f)^2/w)/2
      >= -2*Q^2/w.

The intrinsic ring vectors sum to `(-1,0)` and the spatial ring vectors
sum to zero. Thus

    sum_f R(e,f)=h_e,  sum_e R(e,f)=h_f.

For the special stress entry associated to any short edge, divide by
that edge's `h`. Its value is `1/2+q` or `1/2-q`. The lower bound on that
entry and the sum of the lower bounds on the other three entries in its
row or column give

    -2*Q^2/w < 1/2+q < 1+2*Q^2/w

or the same inequalities with `-q`. Here `Q=0` is immediate; for `Q>0`
strictness follows because every opposite-ring weight lies in `(0,1)`
and the weights sum to one. Hence `Q<1/2+2*Q^2/w`.

For `0<=u<v<=2`, the function `F(q)=q-1/2-2*q^2/w` satisfies

    F(v)-F(u)=(v-u)*(1-2*(u+v)/w)>0.

Moreover, at `q0=1/2+1/w`,

    F(q0)=(w^2-4*w-4)/(2*w^3)>0.

Since `F(Q)<0`, we obtain `Q<q0`, proving the sharper bound. This step
uses division only by the already-proved positive `h_e`; its constants
are uniform as those weights tend to zero. The simpler bound `Q<2`
suffices for all the geometric constants used below.

## 3. Uniform relative extrinsic axial slope

Choose the physical longitudinal axis `02`, with

    r_0=0, r_2=(0,0,L), L>y/2-7/(4*y)>(15/32)*y.

Write `r_i=(P_i,z_i)`. For every short edge `e=ab`,

    |z_b-z_a| < 5*h_e/y,
    (3/4)*h_e < |P_b-P_a| < (33/32)*h_e.

Here is an endpoint proof that covers changes of nearest lattice lift.
For an A-edge use opposite anchor `q=2`; for a B-edge use `q=0`.
Let `u_a` be its prescribed shortest intrinsic vector from `q` to `a`.
The vector `u_a+a_e` is a candidate lift from `q` to `b`. Thus

    D_qb-D_qa <= 2*u_a dot a_e + |a_e|^2.

Use the reverse comparison for the opposite sign. Every nearest lift
satisfies `|X|<=1/2` and `|V|<=1/2+1/(8*w)`, so

    |D_qb-D_qa|
      <= h_e+(1+1/(4*w))*|gamma_e|+|a_e|^2
      < (7/2+5/(2*w))*h_e
      <= (453/128)*h_e.

This compares all candidate translates, rather than assuming that a
single cross-edge lift remains nearest along the short edge.

For the anchor `p` in the same ring, both distances to its endpoints are
less than `33/64`. Consequently

    |D_pb-D_pa| <= (|r_b-r_p|+|r_a-r_p|)*|E_e|
                 < (1089/1024)*h_e.

Subtract the two squared-distance differences. As
`2*L*(z_b-z_a)=D_0b-D_2b-D_0a+D_2a`,

    |z_b-z_a| < (4713/960)*h_e/y < 5*h_e/y.

Finally `|E_e|>=h_e`, so

    |P_b-P_a|^2 > (1-25/w)*h_e^2
                >= (39/64)*h_e^2 > (9/16)*h_e^2.

Every projected short edge is therefore nonzero. Arbitrarily short cap
edges cannot point mainly along the longitudinal axis.

## 4. Relative determinant error and remaining angular degeneracy

Normalize only the axial coordinate, writing `H_i=z_i/L`, with cap
levels `c_i=0` on A and `c_i=1` on B. The preceding bounds imply

    |H_b-H_a| < 11*h_ab/w,
    |H_i-c_i| < 11/(2*w),   |P_i|<33/64.

The height bound for a vertex uses the ring path with horizontal length
at most `1/2` to its own anchor. In particular the two cap rings are
strictly separated by `H=1/2`.

Consider either two consecutive edges in one cap, or one edge from
each cap. Denote their horizontal lengths by `h,k` and their projected
vectors by `p,q`. The relevant four-point determinant, up to its fixed
ordering sign, is `det((p,a),(q,b),(C,c))`, where

    |a|<11*h/w, |b|<11*k/w,
    |c-sigma|<11/w, |C|<33/32, sigma in {1,-1}.

Replacing the cap heights by 0 and 1 gives `sigma*det(p,q)`. Expansion
along the axial coordinate proves

    |D-D_planar|
      < [33*(33/32)^2/w]*h*k
      < (36/w)*h*k.

For two consecutive edges, subtracting the first edge from the second
row converts the corresponding three-vertex cap determinant to this
form. For an A-edge/B-edge pair, exchanging the second and third rows
accounts for the usual minus sign in its K4 bracket.

The eight consecutive cap-edge pairs and sixteen A-edge/B-edge pairs
are exactly the 24 comparisons in the existing
[`two-cap obstruction`](../type7_focus/cap_order_obstruction.md).
If all 24 projected cross products had magnitude greater than
`36*h*k/w`, every actual 3+1 and K4 sign would agree with its planar
replacement. The necessary orientation formula and its exact signed
line-order contradiction would then apply. Using those audited geometric
lemmas, at least one comparison therefore satisfies

    |det(p,q)| <= 36*h*k/w.

Since `|p|>(3/4)*h` and `|q|>(3/4)*k`, this implies the scale-free
angular condition

    |sin(angle(p,q))| < 64/w.

At the common target `y=10^6`, one comparison thus has sine magnitude
less than `6.4*10^-11`. This conclusion is about almost parallel or
antiparallel **directions**, not a small area caused only by a vanishing
edge. It still permits zero cross products and supplies no contradiction
through that angular region. Full `ray3_phase0` remains open.

## Reproduction

    python3 research/type7_completion/verify_relative_cap_bounds.py

The exact verifier checks the eight stress identities directly from the
archived cocycle, both windings, the area identity, the chosen face and
baseline signs, and every rational constant above. The Cauchy,
nearest-lift comparison, and determinant estimates are the hand proof
given here. This is research verification, not a new Lean theorem.
