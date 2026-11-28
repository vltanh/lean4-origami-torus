# Type 5 F1: cap bounds and a geometric reduction

**Scope.** These are necessary identities and inequalities for every realization
in any of the five F1 cells. They do not exclude a cell. They identify the
possible cap degenerations explicitly, without a lower bound on cap area.
The cap identities use the exact edge metric and the strict horizontal
nearest-lift inequality, not a nonzero tetrahedron or an orientation archive.
The later geometric reduction also uses embeddedness, the separated cap
hulls, and the strict support/K4 facts proved in `coverage.md`.

## 1. A primitive horizontal triangle has three positive short increments

Orient an essential triangle so its horizontal winding is +1. Write its
three lifted horizontal increments as `h1,h3,h2` in cyclic order. Their sum
is 1 and each lies strictly between -1/2 and 1/2. Each is therefore positive:
if one were nonpositive, the sum of the other two would be strictly less
than 1. Thus

    0 < hi < 1/2,       h1+h2+h3 = 1.

Set `ui=1-2*hi`. The three short-edge margins satisfy

    ui > 0,            u1+u2+u3 = 1.

In particular at least one `hi` is at least 1/3. A reconstruction may align
its first coordinate with a longest cap edge using three charts, and that
edge has squared length at least 1/9. This does not give a positive lower
bound on the cap's altitude.

Gauge the intrinsic coordinates at the common endpoint of the `h1` and
`h2` edges. The other two lifted coordinates are `(h1,b1)` and `(-h2,b2)`;
the opposite edge uses horizontal shift +1. The three squared spatial
edge lengths are exactly

    d01 = h1^2+b1^2,
    d02 = h2^2+b2^2,
    d12 = h3^2+(b2-b1)^2.

## 2. Positive cap Gram decomposition

Let `B` be the two-by-two spatial Gram matrix at the chosen base vertex.
Write `s=h1+h2-1/2=u3/2` and `b=(b1,b2)^T`. Polarization gives

    B = T+b*b^T,
    T = [[ h1^2,       -h1*h2+s ],
         [ -h1*h2+s,   h2^2     ]].

`T` is positive definite. Indeed `h1>0` and

    D := det(T)
       = 2*(1/2-h1)*(1/2-h2)*(h1+h2-1/2)
       = u1*u2*u3/4 > 0.

The exact determinant is

    det(B) = D + h2^2*b1^2 + h1^2*b2^2
                 + 2*(h1*h2-s)*b1*b2
           = D + b^T*adj(T)*b.

As `adj(T)` is positive definite, vertical phase differences cannot reduce
the cap determinant. Hence

    det(B) >= u1*u2*u3/4 > 0,
    16*(spatial triangle area)^2 >= u1*u2*u3.

The first weak inequality can be equality: this happens exactly when
`b1=b2=0`. It must not be replaced by a strict inequality.

For a division-free sum-of-squares certificate, put

    c = h1*h2-s.

Then

    h2^2*(det(B)-D) = (h2^2*b1+c*b2)^2 + D*b2^2,
    h1^2*(det(B)-D) = (h1^2*b2+c*b1)^2 + D*b1^2.

These polynomial identities prove the inequality even for arbitrarily
small positive shortest-edge margins. Their closed versions remain valid
on every boundary stratum.

There is also a useful normal form for the cap vectors themselves. Write
`R1,R2` for the spatial vectors whose Gram matrix is `B`, and put

    Wplus  = h2*R1+h1*R2,    Pplus  = h2*b1+h1*b2,
    Wminus = h2*R1-h1*R2,    Pminus = h2*b1-h1*b2.

Then exact polarization gives

    |Wplus|^2  = Pplus^2  + h1*h2*u3,
    |Wminus|^2 = Pminus^2 + h1*h2*u1*u2,
    Wplus dot Wminus = Pplus*Pminus.

After subtracting the coherent vertical rank-one contribution, these two
combinations are orthogonal. Their squared horizontal lengths explicitly
separate the `u3=0` boundary from the `u1*u2=0` boundary. They provide a
coordinate-free form of the cap collapse conditions that does not invert
`B` or divide by any small margin.

## 3. The three collapse faces and their kernels

Suppose a convergent sequence of such cap data has spatial cap determinant
tending to zero. In the closed limit `ui>=0`, `sum(ui)=1`. The determinant
identity forces at least one `ui=0`; a cap cannot collapse while all three
horizontal margins stay positive. On each boundary face the determinant
becomes one square:

| Boundary face | Horizontal relation | Exact limiting `det(B)` | Necessary condition for collapse |
|---|---|---|---|
| `u1=0` | `h1=1/2`, `h2+h3=1/2` | `(h2*b1-h1*b2)^2` | `h2*b1=h1*b2` |
| `u2=0` | `h2=1/2`, `h1+h3=1/2` | `(h2*b1-h1*b2)^2` | `h2*b1=h1*b2` |
| `u3=0` | `h3=1/2`, `h1+h2=1/2` | `(h2*b1+h1*b2)^2` | `h2*b1=-h1*b2` |

The formulas also cover intersections of boundary faces, including a
vanishing horizontal edge. No division by `hi`, `ui`, or a cap area is
needed in the table. The conclusion is conditional on convergence of the
displayed vertical phase data; it does not itself supply a uniform bound
on those phases in an elongated sequence.

## 4. Substitution for both F1 caps

Use the sharp marking gauged at vertex 1, physical horizontal coordinates
`xi`, and physical vertical coordinates `vi` (`vi=y*bi` in the fixed
generator's normalized notation). The same two essential triangles occur
in every F1 cell, even when vertices 2 or 7 also enter a cap.

| Cap and orientation | Base | `h1` | `h2` | `h3` | `b1` | `b2` |
|---|---:|---|---|---|---|---|
| `1 -> 0 -> 4 -> 1` | 1 | `x0` | `-x4` | `1+x4-x0` | `v0` | `v4` |
| `5 -> 6 -> 3 -> 5` | 5 | `x6-x5+1/2` | `x5-x3+1/2` | `x3-x6` | `v6-v5+y` | `v3-v5+y` |

The first cap uses spatial Gram vectors `(r0-r1,r4-r1)`; the second uses
`(r6-r5,r3-r5)`. The formulas hold for the whole marked realization,
independently of the particular localized cell. The verifier checks the
listed horizontal and vertical winding directly from the archived cocycle,
checks all five F1 memberships, and verifies the polynomial identities.

If squared distances are normalized by `y^2`, the corresponding Gram
determinant is divided by `y^4`. The necessary bound is then

    det(B_normalized) >= u1*u2*u3/(4*y^4).

## 5. A related exact angular inequality

At a corner of the cap, let `u,v` be the two consecutive intrinsic edge
vectors, and let `w` be the opposite edge. Let `theta_ext` be the exterior
turning angle of the spatial cap triangle, in `[0,pi]`. Let `theta_int` be
the unsigned angle between `u` and `v`. Since the intrinsic edge vectors
sum to `(1,0)` while the spatial edge vectors sum to zero,

    cos(theta_ext)-cos(theta_int)
       = (2*h_opposite-1)/(2*|u|*|v|) < 0.

Thus `theta_ext>theta_int`. Equivalently, if either side of the intrinsic
annulus is capped by its spatial triangle, the total angle at each cap
vertex is strictly less than `2*pi`: the annulus angle is `pi` plus or
minus the signed intrinsic turn, whereas the cap angle is
`pi-theta_ext`. This is an angular inequality only. It does not establish
convexity or embeddedness of the capped polyhedron.

## Reproduction

    python research/type5_completion/f1_geometry_verify.py

The new bounds isolate exactly where the cap-plane estimates lose
uniformity: the three explicit horizontal margin faces. A whole-cell
exclusion still needs to combine these bounds with the cross-cap metric
equations and the embedding conditions.

## Extension to every essential triangle

The same argument applies to any three-edge cycle with nonzero lattice
period `ell`, at any modulus. Put `w=|ell|^2>0`. For each lifted intrinsic
edge vector `e`, uniqueness of its shortest lift against `e+ell` and
`e-ell` gives

    -1/2 < (e dot ell)/w < 1/2.

The three quantities sum to 1, so they again are the positive `hi` above.
After gauging at one vertex, write the other two intrinsic vectors as

    p1 = h1*ell+c1*J(ell),
    p2 = -h2*ell+c2*J(ell),

where `J` is a quarter-turn and `ci=det(ell,pi)/w`. The opposite edge uses
the period `ell`. Exact polarization now gives

    B = w*(T+c*c^T),
    det(B) >= w^2*u1*u2*u3/4 > 0.

This is a quantitative noncollinearity theorem for every essential
triangle. It uses no convexity, strict support, or K4 premise. The two
displayed SOS identities apply after replacing `B` by `B/w` and `b` by
`c`; all denominators are known positive and may be cleared. The bound is
an additional useful consequence of the exact edge metric and the
shortest-lift inequalities, not an independent assumption.

## 7. Cutting along the caps

Write `A=conv(r0,r1,r4)` and `B=conv(r3,r5,r6)`. In every one of the five
finite F1 cells, the two triangles are nondegenerate by the cap determinant
bound, and their convex hulls are disjoint by the quantitative localization.
Neither statement requires a positive lower bound on the cap area.

Cutting the abstract torus along their boundary cycles gives two annuli:

| Annulus | Actual faces | Interior vertices |
|---|---|---|
| Short annulus | `031 053 045 136 164 465` | None |
| Other annulus | `012 024 152 147 175 263 237 274 256 357` | `2,7` |

Adding the two cap disks to the short annulus gives the abstract octahedral
sphere with opposite vertex pairs `06,15,34`. Adding the caps to the other
annulus gives the boundary of the abstract tetrahedron chain

```
0124 --124-- 1247 --127-- 1257 --257-- 2357 --235-- 2356.
```

All five tetrahedra are strict K4s. This last statement is a combinatorial
decomposition: it does not assert that the spatial tetrahedra have disjoint
interiors or that the capped second annulus is embedded.

### Empty-annulus capping lemma

**Claim.** The short annulus together with `A` and `B` is an embedded
polyhedral sphere.

Here is a general proof, including coplanar configurations. Let `F` be one
of the short-annulus triangles. Its vertices split into a nonempty proper
face `I` of the triangular cap `A` and a nonempty set `J` of vertices of
`B`. Suppose `p` belongs to `F intersect A` but not to `conv(I)`. Write

```
p=(1-t)*a+t*b,   a in conv(I), b in conv(J), 0<t<=1.
```

Since `A` and `B` are disjoint, `b` is outside `A`. Continue the segment
from `a` through `p` toward `b`. Both `a` and `p` lie in the plane of `A`,
so this segment does also. It exits `A` at a point `q` of its boundary,
still in `F`. The point `q` cannot belong to `conv(I)`: a segment starting
in a proper face of a triangle and passing outside that face cannot return
to it along the same ray. Thus an actual boundary edge of `A` meets the
actual face `F` beyond their common simplex, contradicting embeddedness.

It follows that `F intersect A=conv(I)`. The same proof applies to `B`.
The caps do not meet each other, and all remaining face intersections are
already those of the embedded torus. The augmented abstract octahedron is
therefore embedded. Denote its sphere by `S` and its bounded complementary
region by `K`.

This argument is independent of cap-plane exposure. In particular, it
does not infer convexity from positive capped angle deficits.

## 8. Three exhaustive positions of the anchor face

The actual face `125` now gives a geometric alternative covering all of
F1. The following argument uses no orientation-sign enumeration.

First, `r2` is outside `conv(A union B)` and hence outside the closure of
`K`. Indeed vertex 2 is adjacent to every other vertex, so its strict
supporting functional separates it from the six cap vertices. Also, any
point outside their convex hull is outside the bounded region: a separating
linear functional gives a ray to infinity avoiding the entire sphere.

Next, the actual edge `15` meets `S` only at its endpoints. Embeddedness
already gives this for the six side faces. The cap intersections follow by
the same exit argument as above, now with one vertex in each cap. Its open
segment is consequently either entirely inside `K` or entirely outside.

Define two possible piercings:

```
P_A: the open edge 25 meets the relative interior of cap 014;
P_B: the open edge 12 meets the relative interior of cap 356.
```

The relevant K4 conditions make both piercings transverse: vertices 2 and
5 are off the plane of `014`, and vertices 1 and 2 are off the plane of
`356`. Every extra intersection of face `125` with cap `A` must be the
segment from `r1` to a piercing point on edge `25`. Otherwise continuing
a ray from `r1` through the intersection reaches an actual cap boundary
edge while still in face `125`, violating embeddedness. The corresponding
statement for `B` uses the segment from `r5` to edge `12`.

**The two piercings cannot occur together.** Translate `r2` to zero and
write `U=r1`, `V=r5`. If both occur, there are `0<t,s<1` with `t*V in A`
and `s*U in B`. The segments `[U,t*V]` and `[V,s*U]` then meet at

```
z = (s*(1-t)*U+t*(1-s)*V)/(1-s*t).
```

Both segment parameters lie strictly between zero and one, so `z` belongs
to both cap hulls, a contradiction.

Finally, take a point `m` in the open edge `15` and follow the segment
from `r2` to `m` inside face `125`. It cannot cross a short-annulus face
or a cap boundary edge. If neither piercing occurs, it never meets `S`.
If one piercing occurs, it crosses the corresponding cap interior exactly
once. Its endpoints are on opposite sides of the cap plane: `r2` is on
one side, and `m` is on the side of `r5` (or `r1` for the second cap).
Thus the crossing is transverse.
Since its starting point is outside, these observations prove the following
**disjoint, exhaustive three-case reduction**:

| Case | Position of the open edge `15` | Anchor-face intersection with cap interiors |
|---|---|---|
| Exterior | Outside `K` | Neither cap is pierced |
| First-cap entry | Inside `K` | `25` pierces `014`; `12` does not pierce `356` |
| Second-cap entry | Inside `K` | `12` pierces `356`; `25` does not pierce `014` |

### Entry forces nesting of the whole opposite cap

The entry cases are stronger than a single edge piercing. Suppose `25`
pierces `A`. Intersect actual face `256` with the plane of `A`. Its plane
is distinct from the cap plane because vertices 2 and 5 are off that plane.
Starting at the piercing, the intersection segment cannot exit through
edge `56`, which is contained in the disjoint cap `B`. It also cannot
leave `A` through its boundary, since that would intersect an actual cap
edge with actual face `256`. Thus its other endpoint lies strictly inside
edge `26` and strictly inside `A`. This also proves that vertex 6 is off
the cap plane and on the same side as vertex 5. Apply the identical argument
to face `236` to force an interior piercing by edge `23`.

Consequently **all three segments from 2 to cap `B` pass through the
interior of cap `A`**. Central projection from `r2` maps the whole triangle
`B` into the relative interior of `A`. The projection is a nondegenerate
triangle: `r2` is off the plane of `B` by K4 `2356`. Its projective
denominators have one strict sign, so its image is precisely the convex
hull of the three projected vertices, all in `relint(A)`.

Symmetrically, a piercing of `B` by `12` propagates through actual faces
`012` and `024`: edges `20` and `24` also pierce `B`, and central projection
from 2 maps the whole of `A` strictly inside `B`. Propagation works in
reverse along each two-face fan as well. Thus the exterior case has no
opposite-cap piercing by any of the six radial edges from 2.

### A cap-entry bound from the isometric anchor face

Use the physical intrinsic vertical coordinates `vi`, with `v1=0`, and set

```
R_A=max(|r0-r1|,|r4-r1|),
R_B=max(|r3-r5|,|r6-r5|).
```

The actual face `125` is isometric to its coherent intrinsic triangle.
Its intrinsic vertical coordinate therefore extends to a unit linear
functional on its spatial plane, taking the values `0,v2,v5` at its
vertices. In the first-cap entry case its piercing point `p` is in
`relint(A)`, so `|p-r1|<R_A`. Its vertical coordinate is strictly between
`v2` and `v5`. Since `v5>R_A`, this forces

```
P_A implies v2<R_A.
```

For the second-cap entry, the piercing point on `12` satisfies
`|p-r5|<R_B`. Its vertical coordinate exceeds `v5-R_B>0`, and is strictly
between zero and `v2`. Hence

```
P_B implies v2>v5-R_B.
```

These estimates divide by no cap area. In all five finite F1 cells,
localization and the short horizontal increments give

```
R_A,R_B <= sqrt(2000^2+1/4) < 2001,
v5 > (237/500)*10^6 = 474000.
```

Thus throughout the closed phase interval `2001<=v2<=v5-2001`, only the
exterior case is possible. In the three F1 cells with vertex 2 in the
first cap, `v2<=2000`, so the second-cap entry case is impossible altogether.
The remaining entry regimes have not been excluded.

These are positions of complete continuous configurations, not isolated
samples or a replacement of the five-cell localization. All three cases
remain open. In particular, an embedded octahedron need not be convex, so
its opposite-vertex segment `15` cannot simply be declared internal.

If both cap planes strictly support the entire vertex set, neither piercing
is possible, and the exterior case is forced. The hand visibility theorem
in [`exposed_caps.md`](exposed_caps.md) now rules out that configuration:
it uses only the six side faces, the four corner-fan faces, and strict
support at vertex 2. A perturbation argument also rules out simultaneous
weak support. Thus at least one cap plane strictly cuts the seven-vertex
set `0,1,2,3,4,5,6`. The argument uses no orientation archive, linking
assumption, or positive cap-area margin.

This is an additional necessary condition in all three positions above.
It does not show that every finite F1 realization has exposed caps. The
cutting-cap configurations, including nearly collapsed ones, remain to
be excluded or realized.

The exact checker verifies the face decomposition, the octahedron's
opposite pairs, the tetrahedron chain, and the displayed simultaneous-piercing
identity. The capping and three-case implications are the geometric hand
proofs above; they are not claimed as compiled Lean theorems.

## 9. A second geometric tool: leaf reflection

The separate hand proof in [`leaf_geometry.md`](leaf_geometry.md) treats
all three leaves at every modulus, including singular root-lift boundaries.
Positive weighted five-cycle deficits give two real local completions of
an arbitrary five-point core in the signed space `R^(3,2)`. At a saturated
root lift, strict support instead gives one tangent completion. At most
one of the three distinguished hinges `05,16,27` can be unfolded.

The candidate completions vary both the spatial and intrinsic leaf
coordinates; they are not automatically embedded torus vertices. The
missing geometric step is a joint restriction on the three selected
completions in the exterior and cap-entry cases above. Their signed-space
reflection hyperplanes use different coherent intrinsic lifts and cannot
be identified as one common spatial reflection plane.
