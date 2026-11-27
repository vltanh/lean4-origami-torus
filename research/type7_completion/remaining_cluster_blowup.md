# Ray 3: a triple cluster cannot face a positive-weight noncollinear cap

## Result

Consider a common-line ray-3 sequence whose first normal blow-up has
one collinear cap and one noncollinear cap. If exactly the two adjacent
edges of a triple cluster in the collinear cap have zero limiting
physical weights, and all four partner weights stay positive, the
sequence is impossible. The argument allows arbitrary relative rates
of both collapsed lengths, the normal width, and `t=1/y²`.

The complete degenerate-norm cover contains 544 such cells. The verifier
maps them to 61 canonical shapes and considers all three ratios of the
two independently normalized small edges. Of these 183 cases, 153 have
direct necessary-sign contradictions. The remaining thirty cases,
including their reflected copies, reduce to the following metric
arguments:

| Shape | Directional cases | Method |
|---|---:|---|
| Opposite-pair V | 8 | A factored cap volume has positive sign |
| Complementary V | 6 | A factored cap volume has negative sign |
| Flat-family endpoint | 12 | Two signed length defects and a negative cubic term |
| Exceptional trapezoid endpoint | 4 | Two signed defects, a length comparison, and a strict limiting slope |

The two trapezoid rows represent 48 and 16 original cells respectively.
No fixed height threshold or Lean bridge is claimed here.

## 1. A directional cover that retains all zero cases

Use the verified marked symmetries and horizontal reflection to put
`A=(0,1,4,5)` at the limiting positions `(0,0,0,1/2)` on a horizontal
line. Let `B=(2,3,6,7)`. Write `a=01`, `b=14`, and normalize a and b
separately by their own stretched transverse norms. Their nonzero
limiting vectors have coordinates `(ax,ay)` and `(bx,by)`. A capital
component denotes the leading component of `a+b`.

The two small vectors can have comparable stretched norms, or either
can dominate. In the comparable case the verifier imposes necessary
ternary sign addition for each coordinate and each cross product with
a B difference. In a dominant case the sum has the dominant vector's
leading signs. Opposite cancellation, including a zero sum, is retained.

The planar geometry is constrained by the rank-three determinant
identities for eight homogeneous points:

\[
 E=(1,0,0),\quad F=(0,1,0),\quad
 a=(a_x,a_y,0),\quad b=(b_x,b_y,0),\quad
 B_i=(X_i,Y_i,1).
\]

The B horizontal and vertical weak orders fix their pair differences;
their four triangle signs come from the finite cap-shape cover. All
other signs are trits, including zero. Every three-term determinant
identity is enforced with its full weak-sign condition: either all
three terms vanish or there are both positive and negative terms.

The symbolic eight spatial points give 34 constant leading brackets,
30 linear brackets, and four quadratic brackets. Every linear bracket
contains the corresponding actual edge or difference `01`, `14`, or
`04` as a factored row. Every quadratic bracket contains both a and b
as factored rows. Thus the error after division remains relative to
that edge or edge product. No absolute coordinate error is divided by
an arbitrarily smaller length. The relative axial estimate gives an
axial error `O(t)` after each stretched edge normalization.

These constraints are added to the complete necessary orientation and
linking formula, allowing either global orientation. The 153 direct
UNSAT certificates and fifteen implication certificates retain every
zero leading bracket. In particular, the strict slope assertion in
Section 5 is proved by excluding its *zero limit trit*, not by treating
a finite strict sign as a strict limiting inequality.

The mirror `(0 4)(2 6)` preserves the marking, exchanges the two small
edges with reversed orientations, and reverses their dominance. It
reduces the thirty surviving cases to fifteen forms.

## 2. The two V shapes

In this section coordinates refer to the stretched transverse plane,
with longitudinal levels zero and one on A and B. A physical horizontal
component is unchanged by the stretch.

### Opposite-pair V

The canonical configuration is

\[
 A=(0,0,0,\tfrac12E),\qquad
 B_2=B_6=0,\quad B_3=-\chi E,\quad B_7=Q=(w,1),
\]

where `s=|w|>0`, `chi>0`, and `chi+s=1/2`. The directional certificate
forces a along positive E, b along positive Q, and `[0145]≤0`.
Writing the actual intrinsic weights as `alpha=h01`, `beta=h14`, the
forced nonzero horizontal components compare their stretched scales
with alpha and beta. In the moving frame `0,2,5,7`,

\[
 a_x/\alpha\to2,\quad a_y/\alpha\to0,\quad
 b_x/\beta\to0,\quad b_y/\beta\to1/s.
\]

The relative stress identities from `remaining_one_collinear.md` give
`c0/alpha→4s`, `gamma01/alpha→1/2`, where
`c0=-x2+1/4+2gamma2`. Also
`gamma2→(x2-1/4)/2`, `x5→0`, and
`gamma5→1/4-(s+w)/2`. Dividing the exact distance polarization for
vertex 1 by alpha before taking limits gives

\[
 a_z/(t\alpha)\longrightarrow 2w-6s<0,
 \qquad b_z=O(t\beta).
\]

The exact factored volume is `[0145]=a_y b_z-a_z b_y`. Therefore

\[
 [0145]/(t\alpha\beta)\longrightarrow6-2w/s\in\{4,8\},
\]

contradicting its required weak negative sign.

### Complementary V

Here

\[
 B_2=0,\quad B_3=B_7=Q=(-s,1),\quad
 B_6=Q+\chi E,\qquad s,\chi>0,\quad s+\chi=\tfrac12.
\]

The certificate forces a along negative Q, b along negative E, and
`[0145]≥0`. In the moving frame `0,2,5,3`,

\[
 a_y/\alpha\to-1/s,\quad b_x/\beta\to-2,
 \quad b_y/\beta\to0.
\]

The exact stress for edge 14 against edge 23 gives
`gamma14/beta→-1/2`. The limiting stress equations give
`x2→chi`, `gamma2→chi/2-1/8`, `x5→0`, and `gamma5→1/4`.
For squared distances define `rho_i=D0i-Di2+D02`. Although 04 is
not an edge, its actual squared length satisfies the exact identity

\[
 D_{04}-D_{01}=2a\mathbin\cdot b+|b|^2.
\]

After division by beta its right side tends to zero, independently
of the ratio alpha/beta. The intrinsic expression for
`D24-D12` factors beta exactly. Consequently

\[
 (\rho_4-\rho_1)/\beta\to\tfrac12-2\chi,
 \qquad \rho_5\to\tfrac34-\chi.
\]

The usual relative-axis conversion, followed by the moving frame,
gives

\[
 b_z/(t\beta)\to
 2\big((\tfrac12-2\chi)+2(\tfrac34-\chi)\big)=8s.
\]

Also `a_z=O(t alpha)`. Thus the same factored cap volume divided by
`t alpha beta` tends to `(-1/s)(8s)=-8`, contradicting its required
weak positive sign. The mirror covers the reversed hierarchy cases.

## 3. Shared metric tools for the two trapezoids

Relabel by `(5,0,3,6,1,4,7,2)`. The cluster is now `0,1,5`, with
tip 4. Use the exact face-023 gauge with incidence coordinates
`(P,Z,c-2t*zeta)` and `P=-U`. Edge 23 has positive limiting weight,
so the plane is well conditioned. Put

\[
 \delta=Z_6>0,\qquad Z_7/\delta\to1,\qquad
 Z_1/\delta,Z_4/\delta,Z_5/\delta\to0.
\]

Let `r=h01>0`, `beta=h50>0`, and define the actual signed defects

\[
 \mu_1=r+U_1,\qquad \mu_5=\beta+U_5.
\]

Replace just the two collapsed-edge equations by these linear
definitions, retaining the other nineteen metric equations. Every
actual configuration satisfies this system with its own two defects.
Its twenty-one dependent planar variables have an invertible Jacobian
in each family below. The resulting implicit solution is analytic
jointly in t, the three free parameters, the defects, and the five
normal coordinates. Its derivatives are uniformly bounded near any
proposed limiting configuration.

The same four weak signs as in `remaining_flat_blowup.md` are forced:
`-[0124]≥0`, `[0146]≥0`, `[0345]≥0`, `[1256]≥0`.
Their positive combination L uses weights

\[
 ((1-2u)N/D,\ 2uN/D,\ N/D,\ 1),\quad
 N=4+t(4r-1)^2,\quad D=4+t(32ru-8r-8u+1),
\]

where `u=h23` is always its actual finite value. The nearest-lift
conditions give `0<u<1/2`, and `D>0`. Hence `L≥0` even in the second
family, where u tends to `1/2`.

The directional certificates force edge 01 to be horizontal at its
own stretched scale, in the positive P direction. Thus
`U1/r→-1` and `Z1/(delta r)→0`. There is an especially useful exact
metric identity:

\[
 (1-2t\gamma_3)(\zeta_1-\gamma_1)=2x_3\mu_1.
\]

Combining it with the original edge-01 equation yields

\[
 \mu_1\left[(r-U_1)
 -\frac{2t x_3(\zeta_1+\gamma_1)}{1-2t\gamma_3}\right]=Z_1^2.
\]

The bracket is at least r eventually: `r-U1~2r`, the denominator
tends to one, and the uniform relative axial bounds make the other
term `O(tr)`. Therefore

\[
 0\le\mu_1=O(Z_1^2/r)=o(\delta^2r).                 \tag{1}
\]

For edge 50 the original equation is

\[
 \mu_5(\beta-U_5)=Z_5^2+
 t(\zeta_5-\gamma_5)(\zeta_5+\gamma_5).             \tag{2}
\]

The relative bounds give `|zeta5+gamma5|≤C beta`. These exact
identities are checked symbolically.

All expansions used below are uniform: defect differences factor
their parameters by analytic integration, while simultaneous `Z→-Z`
makes planar corrections quadratic with remainder `O(|Z|⁴)`.
Brackets are linear in Z with planar coordinates fixed, so their
remaining error is `O(|Z|⁵)`. No expansion divides by t, delta, or a
collapsed weight.

## 4. The flat-family endpoint

The limiting transverse coordinates are

\[
 A=(0,0,\tfrac12,0),\qquad
 B=(0,0),(u,0),(\tfrac12,1),(z,1),\quad 0<u,z<\tfrac12.
\]

Use the exact planar family from `remaining_flat_blowup.md`, including
its endpoint `r=0`, and choose actual free parameters `r=h01`,
`u=h23`, `z=h72`. The regularized Jacobian determinant is

\[
 4096z(2u-1)(2z-1)\ne0.
\]

At zero defects and normals that reference family satisfies all
metric equations exactly for every t and r, and has `zeta=gamma`.
The necessity rank-fourteen intrinsic and rank-five height systems
identify the actual limit with this family.

The exact reference linear term and the full inverse-Jacobian
coefficients give

\[
 L=-c_nrt\delta+
 \mu_1\delta(u+o(1))+
 \mu_5\delta(-z+o(1))+
 \delta^3(-1/(4z)+o(1)),                           \tag{3}
\]

where `c_n→2u>0`. Analyticity and even normal dependence give

\[
 |\zeta_5-\gamma_5|
 \le C(|\mu_1|+|\mu_5|+\delta^2).
\]

If `mu5<0`, the denominator in (2) is
`beta-U5=2beta-mu5≥2beta`; dropping the nonnegative square gives

\[
 (\mu_5)_-\le Ct(|\mu_1|+|\mu_5|+\delta^2).
\]

Absorb the `Ct|mu5|` term. The harmful negative part is bounded by
`C't(|mu1|+delta²)`. A positive mu5 decreases (3). By (1), the mu1
term is `o(delta³)`, and the harmful part of the mu5 term is also
`o(delta³)`. Its cubic coefficient is strictly negative. Hence `L<0`
eventually, contradicting `L≥0`. This argument needs no bound on
`beta/r`, including the hierarchy where that ratio tends to infinity.

## 5. The exceptional endpoint and its slope boundary

After the same relabeling the remaining limiting shape is

\[
 A=(0,0,\tfrac12,0),\qquad
 B=(0,0),(\tfrac12,0),(a,1),(z,1),\quad 0<z<a<\tfrac12.
\]

Its exact planar reference solution, in vertex order `0,...,7`, is

\[
\begin{aligned}
 P&=(0,0,0,\tfrac12,\tfrac12,0,a,z),\\
 x&=(0,0,0,-\tfrac12,0,-\tfrac12,a-\tfrac12,z-\tfrac12),\\
 \gamma=\zeta&=(0,0,-\tfrac18,\tfrac18,-\tfrac14,0,
                           a/2-\tfrac18,z/2-\tfrac18).
\end{aligned}
\]

This satisfies all metric equations for every t. The same constant
rank-fourteen and rank-five necessity systems determine it uniquely.
Choose actual parameters
`r=-x1`, `a=x6-x2+1/2`, `z=x7-x2+1/2`.
The regularized Jacobian determinant is

\[
 -8192z(z-a)(2a-1)\ne0.
\]

The exact inverse-Jacobian coefficients are

| Quantity | r coefficient | mu1 coefficient | mu5 coefficient | Normal quadratic coefficient |
|---|---:|---:|---:|---:|
| `beta=h50` | `2a` | `-a` | `a-z+1/2` | `-1/(4z)` |
| Farkas correction divided by delta | `2a-1` | `1-a` | `a-z-1/2` | `-1/(4z)` |

The reference Farkas functional has only the two small-edge normals:

\[
 L_{\rm ref}=
 \frac{(2a-1)(t+4)}{8(4-3t)}
       \big((t+4)Z_1+(3t-4)Z_5\big).              \tag{4}
\]

The directional certificate gives a negative horizontal component
for edge 50 at its own stretched scale. Consequently `U5/beta→-1`
and `Z5=O(delta beta)`. Analyticity about the reference family gives

\[
 |\zeta_5-\gamma_5|\le
 C(r+|\mu_1|+|\mu_5|+\delta^2),\qquad
 \beta\le C(r+|\mu_1|+|\mu_5|+\delta^2).
\]

Use (2), whose denominator is now asymptotic to `2beta`. It follows
that

\[
 |\mu_5|\le C\delta^2\beta+
 Ct(r+|\mu_1|+|\mu_5|+\delta^2).
\]

Substitute the bound on beta and absorb the small multiple of
`|mu5|`. Together with (1), this proves

\[
 |\mu_5|=o(r+\delta^2),\qquad
 \beta=2ar-\frac{\delta^2}{4z}+o(r+\delta^2).      \tag{5}
\]

Positivity of beta implies `delta²=O(r)` and hence `beta=O(r)`.
This excludes the directional hierarchy `beta/r→infinity` directly.
The third hierarchy `beta/r→0` is already among the direct finite
exclusions. In the metric estimates below, that case would also give
`L/(r delta)→-1`, since `Z5=O(delta beta)`; the strict slope condition
is needed only in the comparable hierarchy.

In the comparable hierarchy put
`eta=lim Z5/(delta beta)`. The full weak-trit certificate proves

\[
 0\le\eta<1/a.                                   \tag{6}
\]

Here is the exact correspondence with the trits, in the cluster labels
before relabeling. The small vector a, divided by its physical weight,
has stretched coordinates `(-1,-eta)`. The difference `B7-B3` is
`(-a,-1)`. Thus its determinant trit `a13` is the sign of `1-a eta`.
The certificate forbids a positive `ay`, giving `eta≥0`, and forces
the *limiting* `a13` trit to be positive. Its zero trit, which would
give equality in (6), is explicitly included in the UNSAT check.

Write `R=beta/r`. Equation (5) gives
`delta²/(4zr)=2a-R+o(1)` and `0≤R≤2a+o(1)`. From (4),
`Z1=o(r delta)`, and the checked correction coefficients,

\[
 \frac{L}{r\delta}
 =-1+R\big(1+(\tfrac12-a)\eta\big)+o(1)
 \le -2(\tfrac12-a)(1-a\eta)+o(1)<0.
\]

The multiplier of R is positive because eta is nonnegative. The
strict final inequality follows from the strict limiting condition
(6), not from a finite strict bracket. This contradicts `L≥0` and
finishes the exceptional family.

## Reproduction

```sh
python3 research/type7_completion/remaining_cluster_blowup.py /tmp/type7-cluster-blowup
g++ -O3 -std=c++17 research/orientation_checkpoint/check_unsat.cpp -o /tmp/type7-cluster-checker
```

Replay all 169 CNFs in the output directory with the independent
checker, passing each file on standard input and requiring explicit
`UNSAT nodes ...` output. There are 153 direct directional exclusions,
fifteen necessary-sign implications, and one complete 1,888-model
coverage certificate. The JSON records all 544 mappings, the complete
183-case split, and the exact metric coefficients.

The result uses only necessary constraints. It excludes the stated
asymptotic cells and does not assert a numerical-height bound or a
finished Type 7 theorem.
