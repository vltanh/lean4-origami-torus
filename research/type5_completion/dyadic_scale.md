# Dyadic-grid Type 5 unfolding

**Research result.** The one-scale construction no longer requires the
special value 1/19. A different intrinsic core uses only points of a
64-by-64 square grid, apart from the two common unfolding displacements.
At the square modulus it realizes the torus for every 0<s<=1/512.
The same core works on the full rectangular range 1<=y<=41/40
and the small nonrectangular box 0<=x<=1/4096, 1<=y<=4097/4096,
for all sufficiently small positive s, with a uniform threshold on
the union of those compact sets. The threshold away from the square
is not evaluated. The earlier explicit fixed-perturbation certificates
remain available and are not weakened.

## Construction

Use the square marking and reconstruction of [simple_family.md](simple_family.md)
and [one_scale.md](one_scale.md). In physical intrinsic coordinates
for periods (1,0),(x,y), define

    X = 1/2-3a
    p1 = (0,0)
    p2 = (X, ((s^2-1/2)*(x^2+y^2)-x*X)/y)
    p3 = (1/2-s^2, 5*a*y)
    p4 = (-4*a, (1/2-5*a)*y)
    p5 = (-2*a, -12*a*y).

Set a=1/64. Thus in a square of side 64 the four nonzero core
points have the especially simple coordinates

    (29,-32+delta), (32-delta,5), (-4,27), (-2,-12),

where delta=64*s^2. The remaining three vertices are reconstructed
by the same linear equations and radicals, with root signs (+,-)
and leaf signs (+,-,+). No additional fit or nonlinear solve is
needed. This template was found by screening small rational grids,
not by a proof of optimality of its simplicity.

In fact the exact value of the scale is unnecessary: at the square,
every a in [127/8192,129/8192] also works for every sufficiently
small positive s, uniformly in a. Thus a=1/64 is just a convenient
dyadic choice from a genuine continuum of valid scales.

## Proof and certification

The tied deficits remain exactly S_12=s^2*(x^2+y^2) for leaf 6
and S_13=s^2 for leaf 7. These equalities depend only on the
prescribed p2 projection onto (x,y) and the first coordinate of p3,
not on the value of a. The discriminant product formula and exact
vanishing of the two exceptional volumes 1236 and 1357 at s=0
are unchanged from one_scale.md. Take the explicit s factor
outside each of the two square roots. All remaining factors and
denominators are strictly signed on the certified domains.

At the limiting square with a=1/64 the two exceptional volume
derivatives are negative. The reference volume signs, using the
derivative signs for these two exceptions, satisfy all 138
disjoint edge-face separation checks. The interval checker proves
all sixteen intrinsic face areas positive, the other 68 volume
signs fixed, and both partial s derivatives strictly negative.
Together with the exact zero identities this implies all required
volume signs for positive s. The unchanged degree-one area identity
and embedding proof then establish an isometric Type 5 torus.

For the last three rows of the table below, the interval certificate
is on the compact boundary s=0. All quantities after removing
the two explicit square-root factors extend smoothly in s in a
neighborhood of that boundary. Uniform continuity supplies a
single positive threshold on each compact set, and integration
of the exceptional derivatives supplies the strict signs for
positive s up to that threshold. This is a uniform existence
theorem; do not interpret these three rows as giving the explicit
square threshold 1/512.

| Domain | Parameter range checked | Accepted boxes | Max depth |
|---|---|---:|---:|
| Square, a=1/64 | 0<=s<=1/512 | 64 | 6 |
| Square, free a | 127/8192<=a<=129/8192, s=0 | 39 | 6 |
| Rectangle, a=1/64 | 1<=y<=41/40, x=s=0 | 285 | 9 |
| Oblique box, a=1/64 | 0<=x<=1/4096, 1<=y<=4097/4096, s=0 | 8 | 3 |

The 396 subboxes were checked with outward-rounded 100-bit integer
interval arithmetic and exact rational subdivision. In the square
interval the lower bounds for the oriented double area, ordinary
absolute volume, and absolute exceptional derivative are respectively
greater than 0.02405, 0.00003128, and 0.001308. On the rectangular
boundary the corresponding lower bounds are greater than 0.01995,
0.000000439, and 0.07676. These decimals are rounded down for
display only. All actual comparisons use integer arithmetic.

Run from the repository root:

    python3 research/type5_completion/verify_dyadic_scale.py

The checker reuses the one-scale engine by accepting a core template.
The old one-scale square interval also passed again with its original
64 subintervals after the refactor. The local replay used the existing
square-marking tables; the repository invocation additionally audits
the actual source tables. The larger oblique box from simple_family.md
was attempted, but the full subdivision did not finish within the
execution limit. No coverage claim for that larger box with this
new template is made. No new Lean theorem or Lean build is claimed.

The limiting configuration at s=0 is not an embedded torus. The
positive unfolding remains necessary in this construction. This
simplifies the known construction, but the radical reconstruction
and Type 5 universality remain as before.
