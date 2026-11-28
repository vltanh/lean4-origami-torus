# A transport phase for the two C0 annuli

The regular C0 problem has one geometric target that does not depend on
the order of the two intermediate heights. Define the real transport
phase `Delta` below. The complete limiting metric forces

\[
\Delta=0\quad\text{for marking 1},\qquad
\Delta=1\quad\text{for marking 2}.                         \tag{1}
\]

A geometric proof of `0<Delta<1` for the two nested annuli would therefore
exclude both markings in this setting. **That strict window is not
proved here.** This note establishes the invariant, binds it to the
original source metric, and identifies a positive swap formula that
might prove the window. It introduces no further geometric classes.

## 1. Coordinates, orientations, and scope

Use normalized height `tau=2z`, so the C0 vertex levels are

\[
(0,1,1,1,\alpha,\beta,0,0),\qquad
\alpha=2u,\quad\beta=2v,\quad 0<\alpha,\beta<1.
\]

The axis gauge is `P0=P1=0`. Assume the two projected cap triangles
`123` and `067` are noncollinear with the positive orientations used
in the existing C0 section proofs. Put

\[
\begin{gathered}
L=|P_3|=1-h_1-h_2,\qquad M=|P_6|=1-h_6-h_7,\\
E=P_3-P_2,\quad F=P_7-P_6,\quad d_i=\tfrac12-h_i,\\
D=h_3+h_4+h_5-1,\\
Q_4=P_4-\alpha P_3-(1-\alpha)P_6,\qquad
Q_5=P_5-\beta P_3-(1-\beta)P_6,\\
\rho_4=h_3-(1-\alpha)D=|Q_4|,\qquad
\rho_5=h_5-\beta D=|Q_5|.
\end{gathered}                                                \tag{2}
\]

Each cap and each interior section has perimeter one. This follows
from the limiting face isometry: its horizontal direction has unit
length, and an intrinsic horizontal section has period one. The
companion independently checks all sixteen horizontal face-norm
stresses against the full 29-row system, including the product
syzygies on faces `245` and `457`.

Both section curves are parameterized **clockwise**, agreeing with
increasing intrinsic horizontal coordinate. For the direct annulus
`B`, start arclength `sigma=0` on edge `01`, whose transverse point is
the origin. Its section is

\[
(0,\ \tau P_3,\ \tau P_2,\
\tau P_2+(1-\tau)P_7,\ (1-\tau)P_7,\ (1-\tau)P_6).
                                                               \tag{3}
\]

For the complementary annulus `A`, start at the point on edge `36`,

\[
C(\tau)=\tau P_3+(1-\tau)P_6.                            \tag{4}
\]

The clockwise section-edge orders are as follows. Each pair denotes
the original edge intersected by the section plane.

| Height interval | Edges in order, starting on `36` |
|---|---|
| Below both intermediate heights | `36,56,05,57,47,46` |
| Between them, if `alpha<beta` | `36,56,05,57,45,24,14,34` |
| Between them, if `beta<alpha` | `36,35,25,45,47,46` |
| Above both intermediate heights | `36,35,25,24,14,34` |

The checker binds these walks to the ten actual faces of `A`; their
complement is exactly the six faces of `B`. The two height orders are
handled by one argument below, not by separate sign classifications.

The piecewise affine argument is stated where the leading intrinsic
face charts are nondegenerate, so the arclength/height parameterization
has finite facewise derivatives. Collapsed faces, collinear caps, and
height endpoints require a separate limiting argument. No exclusion
of these boundaries is asserted here.

## 2. The circulation of a section sweep

Let `P(sigma,tau)` be either anchored, unit-arclength section map, with
`sigma` taken modulo one. On each open face write

\[
p=P_\sigma,\qquad v=P_\tau,\qquad |p|=1,
\]

and define

\[
\omega=(p\cdot v)\,d\sigma+\tfrac12|v|^2\,d\tau,
\qquad
J(\tau)=\int_0^1p\cdot v\,d\sigma.                    \tag{5}
\]

On an affine face `omega` is constant. Across a nonhorizontal crease
`sigma=c tau+d`, continuity of the section map makes

\[
T=cp+v
\]

the same vector on both sides. Its tangential trace satisfies

\[
\omega(c,1)=c\,p\cdot v+\tfrac12|v|^2
=\tfrac12(|T|^2-c^2).                                \tag{6}
\]

Thus the tangential traces agree. The piecewise constant form is
closed in the weak sense, and integration over a cylinder between two
regular heights shows that `J` is constant. Passing an intermediate
vertex adds no point term: the form is bounded on finitely many faces,
and its edge traces already match.

When `alpha!=beta`, every interior edge of these annuli is
nonhorizontal. This proves constancy through all three height intervals
for either ordering. When `alpha=beta`, edge `45` is horizontal.
Continuity and `|p|=1` alone do **not** match the traces there: the
required condition is `p dot (v_plus-v_minus)=0`. The full metric
supplies that compatibility. Section 4 also checks it at the level of
the two circulations directly, without inferring it from equal
perimeters.

For a polygon with vertices `V_i(tau)`, side lengths `ell_i(tau)`,
and partial arclengths `s_i=sum_{j<i} ell_j`, the integral has the useful
formula

\[
J=\sum_i\bigl((V_{i+1}-V_i)\cdot V_i'
                     -\ell_i s_i'\bigr).             \tag{7}
\]

Indeed on side `i`,
`P=V_i+p_i(sigma-s_i)`, with fixed unit direction `p_i`; hence
`P_tau=V_i'-p_i s_i'`. Formula (7) also permits endpoint evaluation
when some section sides shrink, without dividing by their lengths.

## 3. The direct annulus and its intrinsic phase

The six lengths in (3) are

\[
\tau L,\quad\tau h_2,\quad(1-\tau)h_7,\quad
\tau h_1,\quad(1-\tau)h_6,\quad(1-\tau)M.
\]

Substitute them in (7), using the cap cosine laws and the exact core
stress

\[
d_0=h_1h_7+P_2\cdot P_7.
\]

The result, at every height, is

\[
\boxed{J_B=d_0-\tfrac12=-h_0.}                         \tag{8}
\]

This has a direct intrinsic interpretation. If the horizontal
coordinate of the anchor is `a(tau)`, then `x=sigma+a(tau)` and

\[
P^{\rm intrinsic}(x,\tau)=P(x-a(\tau),\tau),\qquad
J_{\rm intrinsic}=J_{\rm anchored}-a'.                 \tag{9}
\]

The source cocycle gives `X01=-h0`, so the anchor on `01` has
`a'=-h0`, agreeing with (8). In the intrinsic coordinate, the effective
second-order axial potential is periodic around this annulus and its
horizontal derivative is a nonzero constant multiple of
`-P_x dot P_tau`; therefore `J_intrinsic=0`.

This statement is separate for each annulus. The effective potentials
include the intrinsic vertical correction with opposite signs on
`A` and `B`. They need not have equal cap traces, and this argument
does not assert equal transport energies.

## 4. The complementary annulus, checked at both ends

The two exact dot stresses are

\[
\begin{aligned}
\Lambda_F={}&F\cdot(\beta Q_4-\alpha Q_5)
 -h_6(\beta\rho_4+\alpha\rho_5)
 +\alpha(h_6-d_5)=0,\\
\Lambda_E={}&E\cdot((1-\beta)Q_4-(1-\alpha)Q_5)
 -h_2((1-\beta)\rho_4+(1-\alpha)\rho_5)
 +(1-\beta)(h_2-d_3)=0.                              \tag{10}
\end{aligned}
\]

They are the full-source circle/dot identities already bound in
`remaining_c0_nested_quadrilaterals.py`, with `alpha=2u`, `beta=2v`.
No marking-1 deficit budget is substituted for marking 2.

At the lower endpoint, (7) gives

\[
J_{A,0}=
\frac{h_6\rho_4-F\cdot Q_4}{\alpha}
+\frac{F\cdot Q_5+\tfrac12-h_6-(1-h_6)\rho_5}{\beta}.
                                                               \tag{11}
\]

At the upper endpoint it gives

\[
J_{A,1}=
\frac{E\cdot Q_5+h_2\rho_5}{1-\beta}
+\frac{\tfrac12-h_2-E\cdot Q_4-(1-h_2)\rho_4}{1-\alpha}.
                                                               \tag{12}
\]

The exact residual identities are particularly simple:

\[
J_{A,0}-D=-\frac{\Lambda_F}{\alpha\beta},\qquad
J_{A,1}-D=-\frac{\Lambda_E}{(1-\alpha)(1-\beta)}.       \tag{13}
\]

Equations (10)–(13), together with Section 2, prove

\[
\boxed{J_A=D}                                        \tag{14}
\]

throughout the height interval. They also settle equal intermediate
heights: the two open intervals have the same circulation `D`. If
the horizontal edge `45` has positive length, its trace jump is constant
along that edge, and its integral is `J_{A,1}-J_{A,0}=0`; hence the
jump vanishes. A zero-length edge contributes no interval integral,
although a collapsed face chart still needs the scope qualification
in Section 1.

The phase interpretation agrees exactly. Increasing `tau` along edge
`36` travels from vertex 6 to vertex 3, and the original cocycle gives

\[
X_{63}=h_3+h_4+h_5-1=D.
\]

Thus (9) yields the same anchored circulation. The companion verifies
both anchor displacements against the marked horizontal formulas.

As a useful check, at `alpha=beta` put `N=P4-P5`. The critical section
is a triangle of side lengths `rho4,rho5,h4`. Equations (10) reduce to

\[
|N|=h_4,\qquad
E\cdot N=d_3-h_2h_4,\qquad F\cdot N=d_5-h_6h_4.
\]

Consequently

\[
J_A=D=h_4(1-h_2-h_6)-(E+F)\cdot N.                   \tag{15}
\]

Formula (15) is the diagonal expression of the same invariant; the
definition and proof of (14) do not require equal heights.

## 5. One scalar target for both markings

Define

\[
\boxed{\Delta=d_0+L+M-J_A.}                           \tag{16}
\]

The two marked source cocycles give
`sum h_i=7/2` and `sum h_i=5/2`, respectively. Therefore

\[
D=d_0+L+M\quad\text{or}\quad D=d_0+L+M-1,
\]

which proves (1). The anchored definition fixes a real number, not
just a phase modulo an unspecified integer.

The remaining proposed theorem is a geometric strict window:

> For the actual nested section sweeps of a metric-compatible regular
> C0 embedded limit, with the nearest-lift bounds retained,
> `0<Delta<1`.

Neither the endpoint formulas nor the nearest bounds currently prove
this statement. In particular, containment at one height, equal
perimeters, or consistent signed section areas cannot replace a proof
using the actual sweep and its metric compatibility.

## 6. A positive adjacent-swap identity

There is a concrete geometric reason that the interval `(0,1)` is a
natural target. In a unit-arclength polygonal sweep, swap two adjacent
fixed directions `e,f`, with lengths `ell(tau),m(tau)`, preserving
the block endpoints and the arclength coordinate outside that block.
By direct integration of (7), the change from order `e,f` to `f,e` is

\[
J_{fe}-J_{ef}=(m\ell'-\ell m')(1-e\cdot f).            \tag{17}
\]

For an upper-cap edge of length `ell=a tau` and a lower-cap edge of
length `m=b(1-tau)`, this is

\[
W=ab(1-e\cdot f)\ge0.                                \tag{18}
\]

Let the two cap edge lists be `a_i e_i` and `b_j f_j`. Their lengths
sum to one and their vectors sum to zero. Hence the nine weights

\[
W_{ij}=a_i b_j(1-e_i\cdot f_j)
\]

satisfy

\[
\sum_jW_{ij}=a_i,\qquad
\sum_iW_{ij}=b_j,\qquad
\sum_{i,j}W_{ij}=1.                                  \tag{19}
\]

All are nonnegative; a term is positive when both edge lengths are
positive and their directions differ. Reversing a swap reverses its
sign. Thus a representation of `Delta` as a proper nonempty positive
portion of this work, with positive weight also omitted, would prove
the desired strict window.

**The required representation is unproved.** The actual complementary
annulus contains edges incident to vertices 4 and 5, with directions
not generally belonging to either cap. Nesting does not yet supply an
ordered decomposition into the swaps in (18), and no such decomposition
may be assumed from a drawing or a generic sign completion. Establishing
it, or finding another direct phase bound that includes those edges,
is the substantive remaining geometric step.

## Verification and limits

```sh
python research/type7_completion/geometric_transport.py
```

The checker replays the two marked cocycles and all 29 source rows;
checks the sixteen face-norm stresses; binds the five section walks
to the original faces; verifies both endpoint circulations, the
diagonal check, the phase values, and (6), (17), (19) exactly.

It does not prove the strict window, any new branch exclusion, a
uniform finite height bound, or closure at collinear caps and height
endpoints. The rational endpoint formulas divide by
`alpha,beta,1-alpha,1-beta`; those divisions are confined to the
stated interior domain. A proof for a whole marking must also address
the boundary limits rather than infer strictness from continuity.
