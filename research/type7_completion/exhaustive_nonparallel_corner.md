# Ray 3: exclusion of the complete labelled nonparallel two-stick limit

## Result and scope

There is no sequence of actual canonical ray-3 realizations with `y→∞`
such that, in the transverse coordinates of `relative_cap_bounds.md`,

- `P1,P4→P0=0` and `P3,P6→P2=0`;
- `P5→p` and `P7→q`, with `p,q` linearly independent.

**No comparability assumption on the four collapsing edges is needed.**
This replaces Section 5's comparable-edge hypothesis by an exhaustive
scale analysis. The difficult final case includes two nearly cancelling
edges whose sum is the missing edge `26`. A separate relative height
estimate for that displacement closes the case.

This is a computer-assisted research theorem, using the audited necessary
orientation and linking conditions. It is not yet a Lean theorem, does not
supply a numerical height threshold, and does not exclude other labelled
cap limits or the full ray-3 marking.

## 1. Notation and uniform estimates

Put `t=1/y²`. Use full physical spatial vectors, with vertex `0` at zero
and vertex `2` on the longitudinal axis:

```
a=r1-r0, b=r4-r1, p=r5-r0,
c=r3-r2, d=r6-r3, q=r7-r2,
A=a+b, C=c+d=r6-r2.
```
The short rings have vectors `(a,b,p-A,-p)` and `(c,d,q-C,-q)`.
Their horizontal intrinsic lengths are `(α,β,u,v)` and `(χ,δ,r,s)`.
Write `σ=α+β`, `H=χ+δ`, and let `γ_e` denote the vertical correction
used in `relative_cap_bounds.md`. Set

```
T=γ_a+γ_b, S=γ_c+γ_d, U=γ_45.
```
The established bounds give

```
|E_e|²=h_e²+tγ_e²,  |γ_e|≤(1/2+t)h_e,
α,β,χ,δ→0, u,v,r,s→1/2, |p|,|q|→1/2.
```
Every short edge has normalized axial increment `O(t h_e)`, uniformly
in its length. In this note constants in `O` estimates are uniform along
the chosen sequence. All statements are unchanged on a subsequence.
The axial components of the full physical vectors tend to zero, so the
limiting `p,q` above can also be regarded as planar physical vectors.
Write `z=p·q` for their limiting dot product; `|z|<1/4`.

Fix the moving affine frame of vertices `0,2,5,7`, exactly as in
`relative_cap_bounds.md`, so these four vertices become

```
0=(0,0,0), 2=(0,0,1), 5=(1,0,0), 7=(0,1,1).
```
The transformations and their inverses are bounded in normalized axial
coordinates. Their axial shear coefficients are `O(t)`. This frame is
fixed at every member of the sequence, before any directional limit.

## 2. Exhaustive first directional limits

Normalize each of `a,b,c,d` by its own length, except that two comparable
edges can share their maximum length as denominator. These directional
limits are nonzero by the uniform projection bound. Within each of the
pairs `(a,b)` and `(c,d)`, the length ratio has, after a subsequence, one
of three types: the first dominates, the lengths are comparable, or the
second dominates. There are nine cases, independent of the relative
scale of the two pairs.

The nine constant and 42 linear bracket links from the earlier verifier
remain necessary under these independent normalizations. For a singleton
coefficient, the exact bracket has the corresponding edge as a factor;
its remainder divided by that edge's length tends to zero. A coefficient
such as `ax+bx` is instead normalized by `max(α,β)`. For comparable
lengths its coordinate signs satisfy the ordinary ternary addition table;
for unequal lengths it has the dominant edge's directional sign. A zero
coefficient places no restriction on the eventual bracket sign.

For all three scale types of `(c,d)`, the necessary Boolean formula is
UNSAT when `a,b` are comparable. This already permits arbitrary scale
ratios between the two caps.

It suffices to handle `β/α→0`. The opposite case is equivalent by the
exact symmetry

```
(0 4)(2 6), together with intrinsic horizontal reflection.
```
The verifier checks preservation of the 16 faces and all 24 cocycle
edges. In the correction coordinates, the required horizontal gauge is
`(0,-1/2,0,-1/2,0,-1/2,0,-1/2)`; the vertical cocycle is unchanged.
The limiting anchors remain `p,q`, and the two A-edge roles are exchanged.

For `β/α→0`, add all 17 nonzero planar quadratic bracket formulas and
the necessary rank-two Grassmann–Plücker sign conditions for the planar
vectors `E,F,a,b,c,d`. The latter include zero determinants. Only 4,800
finite sign clauses are needed. Exhaustively blocking the following
coordinate-sign cells makes each formula UNSAT. Here `+E,+F` mean
positive multiples of the two moving-frame coordinate directions.

| Scale type of B edges | Every possible directional cell |
|---|---|
| `δ/χ→0` | `a=+E,b=+F,c=-F,d=-F` |
| `χ,δ` comparable | `a=+E,b=+F,c=-F,d=-F`, or `a=+E,b=+F,c=-E,d=+E` |
| `χ/δ→0` | `a=+E,b=+F,d=-F`, and `c` is `-F`, `-E`, or has both coordinates negative |

The enumerations are complete for this necessary relaxation, not samples
of directions. Each listed cell is checked satisfiable before all cells
are blocked. Realizability of the relaxation is not asserted.

## 3. A stress relation that survives arbitrarily severe cancellation

For A-edge `e` and B-edge `f`, let

```
R(e,f)=h_e h_f+t γ_e γ_f-E_e·E_f.
```
The archived cocycle gives the exact mask identity `sum(mask*R)=1/2`, with

```
mask = ((1,0,1,1),(1,0,0,0),(1,1,1,0),(0,0,1,0)).
```
Its spatial and horizontal-weight parts expand to

```
a·d-b·c+A·q-p·C,
α-αδ+βχ+uH+(1-σ)r.
```
Its gamma part is

```
G=-γ_a γ_d+γ_b γ_c+U S-T γ_67.
```
The two special stresses `R(50,23)=χ/2-γ_c` and
`R(45,36)=δ/2+γ_d` give exactly

```
(1-tU)S-tTγ_c=(u-1/2)H+σχ-p·C+A·d.             (1)
```
The A-ring length-difference equation gives `u-1/2=O(σ)`:

```
(u-v)(1-σ)=-2p·A+|A|²+tT(γ_45-γ_50).
```
Consequently (1) yields the stronger estimate

```
S=-p·C+O(σH+t|C|).                              (2)
```
This estimate controls the gamma sum by the **actual displacement** `C`,
even when `c,d` nearly cancel. Bounding `S` only by `H` would lose the
argument.

The B-ring length-difference equation is

```
(r-s)(1-H)=-2q·C+|C|²+tS(γ_67-γ_72).
```
Substitute it and (2) into the mask identity. The result is

```
α-β+2q·A-2(p+q)·C=o(σ+|C|).                    (3)
```
More explicitly the discarded terms are bounded by a constant times

```
σH+(σ+H)|C|+|C|²+t(σ+|C|),
```
which is `o(σ+|C|)`. There is no comparison of `σ`, `H`, and `t` here.

In all cells of the table except `c=-E,d=+E`, one has
`C/H→-2q`. Since `β=o(α)`, `a/α→2p`, and `|p|=|q|=1/2`, the left side
of (3) is

```
(1+4z)(α+H)+o(α+H).
```
Its leading coefficient is positive. These cells are impossible.

For the remaining cell `a=+E,b=+F,c=-E,d=+E`, equation (3) becomes

```
(1+4z)α-2(p+q)·C=o(α+|C|).                     (4)
```
It follows that `liminf |C|/α>0`. After normalizing `C` by `|C|`, its
limiting direction satisfies `(p+q)·lim(C/|C|)≥0`. This remains valid
when `|C|/α→∞`; equality is allowed.

## 4. Relative axial bound for the missing displacement 26

The previous short-edge height estimate cannot directly be applied to
`26`, which is not an edge. The following exact identities provide the
required replacement.

Let `x2,γ2` be the canonical intrinsic correction variables, and put

```
C0=-x2+1/4+2γ2=2R(01,67)+2R(01,72),
J=R(01,36)+R(14,36).
```
The cocycle also gives

```
x2=H/2-S-C0/2-J.
```
Polarization against the longitudinal anchor, with `r0=0`, gives

```
2r2·C = C0 H+S(-1+2H+2tγ2)-2(1-H)J+tS²-|C|².  (5)
```
The verifier checks these identities symbolically. The direct stress
formulas give `C0=O(α)` and `J=O(σH)`. Together with (2), equation (5)
therefore implies

```
normalized axial displacement of C = O(t(|C|+σH)).
```
In the remaining cell, `σ/α→1` and `|C|` is bounded below by a fixed
positive multiple of `α`. Thus the axial displacement is `O(t|C|)`.
The full physical axial component is `O(sqrt(t)|C|)`, so the limiting
transverse direction of `C/|C|` is nonzero. The moving affine frame
preserves the relative normalized axial estimate.

If its frame coordinates are `(Cx,Cy)`, inequality (4) now says

```
Cx+Cy≥0,
```
up to a positive common factor: `(p+q)·(Cx p+Cy q)=(1/4+z)(Cx+Cy)`.
Both coordinates cannot vanish. This derives a new normalized direction
without assuming a lower bound on the original four edge lengths or on
the amount by which `c,d` fail to cancel.

## 5. A signed axial inequality and the final Boolean contradiction

In the remaining cell, `a/α→2p`. The exact stresses give

```
C0/α→2,  γ_a/α→1/2.
```
The limiting intrinsic corrections are

```
x=(0,0,0,0,1/2,0,1/2,0),
γ=(0,0,-1/8,-1/8,0,-z,-1/8,1/8).
```
For completeness, the short-ring windings first determine the `x` list
up to `x2`; the nearest horizontal inequalities on edges `12` and `16`
force `x2→0`. The small-edge gamma bounds, `C0→0`, and the special
stress entries then give the displayed gamma values.

Let `H_i` denote axial coordinates before the moving affine shear and
let `L=|r2|`, so `2L²t→1/2`. The exact distance formulas yield

```
2L² H1=-C0+(1-2x2)α+γ_a+2tγ2γ_a,
H1/(tα)→-1,              H5/t→1-2z.
```
The moving-frame transverse coordinates of `1`, divided by `α`, tend
to `(2,0)`. The axial shear is
`H-H5*(MP)_x+(1-H7)*(MP)_y`. Hence its new axial coordinate `Z1` satisfies

```
Z1/(tα)→4z-3<0.
```
This sign is uniform in every collapse rate and all angular corrections.
In the fixed affine frame there is the exact determinant identity

```
[0125]+[0157]=Z1.
```
Thus at least one of these two actual brackets is negative. Every
necessary generic sign completion obeys the clause
`not χ0125 or not χ0157`; zero real brackets are still allowed.

The final CNF uses:

- the audited orientation, two horizontal unlinkings, and long linking
  of magnitude two;
- the directional cell `a=+E,b=+F,c=-E,d=+E`;
- the separately normalized, nonzero direction `C` with `Cx+Cy≥0`;
- the existing linear and 17 quadratic bracket implications, now using
  the relative height estimate for `C`;
- the last signed axial clause.

No addition rule is imposed between the separately normalized `C` and
`c,d`. In particular their cancellation rate is unrestricted.

Here is the factorization justification for reusing every bracket link.
Subtracting the endpoints of the relevant edges writes each of the 17
quadratic brackets as a determinant with two short difference rows and
one row joining the caps. Its planar part is the listed cross product.
The relative height estimates make the remainder `o(l m)`, where `l,m`
are the **individual normalizing lengths of those two rows**. This uses
no comparison of `l` and `m`. For example, bracket `1246` is
`det(r2-r1,b,C)` and has planar leading term `det(b,C)`; the axial
components of `b` and `C` are `O(tβ)` and `O(t|C|)`, so its error is
`O(tβ|C|)` with bounded anchor differences. If a row is `A=a+b`, use
`|A|/α→1` and its height bound `O(tα)`; if it is `C`, use the new bound
from Section 4. The 42 linear links similarly factor their named edge
or the displacement `A` or `C`; their residual anchor coefficients tend
to the displayed constants. Thus an individual nonzero leading
coefficient fixes the actual bracket sign even at arbitrarily disparate
scales, while a zero coefficient leaves it free.

The final formula has **449 variables and 13,366 clauses** and is UNSAT.
The exact formula treats zero leading coefficients as unconstrained signs.
This finishes the remaining cell and hence the theorem.

## Reproduction

```sh
python3 research/type7_completion/exhaustive_nonparallel_corner.py /tmp/type7-exhaustive-corner
g++ -O3 -std=c++17 research/orientation_checkpoint/check_unsat.cpp -o /tmp/type7-corner-checker
```

Replay each of the seven emitted CNF files with the independent checker,
requiring explicit `UNSAT nodes ...` output. A zero exit status alone is
not a SAT/UNSAT discriminator for that checker. The generator also checks
the cocycle symmetry, stress-mask and missing-edge identities, and all 17
quadratic bracket formulas exactly. Its dependencies are repository data,
SymPy, and shared libz3; there is no scratch-script dependency.
