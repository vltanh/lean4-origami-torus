# One-scale construction by unfolding two tangent leaves

**Research result.** Set a=1/19 and let s be a free unfolding parameter,
with epsilon=s^2. The core below and the fixed radical branches in
[simple_family.md](simple_family.md) realize the square torus for every
0<s<=1/512. For each modulus in the closed box
0<=x<=1/4096, 1<=y<=4097/4096, they realize that modulus for every
sufficiently small positive s, with one common positive threshold
for the whole box. No explicit threshold on the two-dimensional box
is claimed. This is a simpler construction, not an expansion of the
previously certified larger modulus ranges.

## 1. Core with one scale

Use the square marking from OrigamiTorus/Type5/Square.lean. In physical
coordinates, for periods (1,0), (x,y), take

    p1 = (0,0)
    p2 = (1/2-a, ((s^2-1/2)*(x^2+y^2)-x*(1/2-a))/y)
    p3 = (1/2-s^2, (3a/2)*y)
    p4 = (-3a/2, (1/2-3a/2)*y)
    p5 = (-2a/3, -4a*y).

The coordinates use the repeated root offset 3a/2 and the single
scale a instead of six independently chosen fractions. At the square
the second coordinates of 2 and the first coordinate of 3 differ
from -1/2 and 1/2 respectively by the same amount s^2.

Apply the anchor, root and leaf formulas in simple_family.md, with
root signs (+,-) and leaf signs (+,-,+). This still uses the general
radical reconstruction; it is not a purely elementary spatial model
or a fully symmetric realization. The single rational scale was
selected by a structured numerical search and then checked exactly.

## 2. Exact double tangency at the limiting core

For each leaf j, the signed core deficit matrix S has a five-cycle
of nonzero potential entries and all other entries zero. Its
discriminant identity is

    Delta_j = 8 product(S_ik)/D^2,

where D is the anchor determinant. The proof in simple_family.md
is purely algebraic and does not require a strictly positive product.

For leaf 6 the pair 12 has alternate period shift (0,1) in integer
lattice coordinates. With b=(x,y), its deficit is exactly

    p2.b + ||b||^2/2 = s^2 ||b||^2.

For leaf 7 the pair 13 has alternate period shift (-1,0), so its
deficit is exactly

    -p3_x+1/2 = s^2.

All other complementary factors are strictly positive on the
certified closed domains. Thus the square roots of the discriminants
for leaves 6 and 7 are s times smooth positive square roots, after
removing their explicit s^2 factor. Leaf 0 has an ordinary positive
discriminant. This extends the formulas smoothly to s=0 without
differentiating sqrt at zero. The equations hold at s=0 as well,
by the quadratic formula, or by continuity from positive s.

In the limit s=0 exactly two of the 70 affine volume determinants
vanish on the certified boundary domain: 1236 and 1357. The zero
identities follow without numerical evaluation. For leaf 6,
its link contains consecutive neighbors 1,3,2, so S_13 and S_23
vanish by coherence of the two incident faces, and S_12 vanishes by
the displayed formula. The three spatial rays from 6 therefore
have exactly the same Gram matrix as the three corresponding
intrinsic planar rays. Its rank is at most two, proving volume
1236 is zero. The same argument with neighbors 1,5,3 at leaf 7
proves volume 1357 is zero. The other 68 volumes are certified
strictly signed by intervals.

Instead of seeking a positive lower bound on these two small
volumes, the verifier certifies their derivatives with respect to s
strictly negative. Integration from their exact zero at s=0 gives
the needed signs for all positive s on the certified square interval.
The reference signs of the 70 volumes, using these two derivative
signs at the limit, pass all 138 disjoint edge-face circuit checks.
All sixteen intrinsic face areas are strictly positive and the
degree-one area identity is unchanged from simple_family.md.
Consequently the same embedding and intrinsic covering arguments
apply to every positive s covered by this proof.

The limiting configuration itself is NOT asserted to be embedded.
In particular, its tied lifts would contradict injectivity of an
actual flat embedding.

## 3. Uniform verification

The standalone Python verifier verify_one_scale.py uses outward-rounded
integer intervals with denominator 2^100. As in the previous checker,
it intersects the ordinary interval evaluation with a mean-value
enclosure, here using partial derivatives with respect to x,y,s.
All denominators and strictly positive radicands are certified.
The zero-limit determinants are tested via their partial s derivatives;
all others are tested directly against the fixed reference signs.

The exact square interval is covered by 64 closed subintervals,
maximum subdivision depth 6. All subintervals certify the two
derivative signs, the other 68 volume signs, and all 16 intrinsic
face orientations. The minimum lower bounds printed by the verifier
(rounded decimal display only) are approximately 0.02589388 for
oriented double area, 9.880351e-6 for ordinary absolute volume and
0.04439180 for the absolute exceptional derivatives.

For the two-dimensional modulus box, we only certify the boundary
s=0. It is covered by 32 closed subboxes, maximum depth 5, with
strictly positive lower bounds for the same quantities (approximately
0.02686014, 1.1135843e-5 and 0.06797618, respectively).
All expressions with the two factors removed are smooth on a
neighborhood of this compact box, by the strict denominator and
radicand checks. Uniform continuity gives a common s0>0 such that
for all moduli in the box and all 0<=s<=s0 the ordinary signs and
both derivative signs persist. Since both exceptional determinants
vanish identically at s=0 for all those moduli, their strict signs
follow for 0<s<=s0. This proves a common unfolding interval exists,
but does not calculate its endpoint.

Replay from the root:

    python3 research/type5_completion/verify_one_scale.py

Both covers passed locally in a standalone copy with the square
marking and faces transcribed from the archived verifier; the source
audit is enabled on a repository checkout. Attempts to use the same
fixed sign pattern over the larger rectangular interval were not
certified (an ordinary boundary volume approached zero near y=1.0063).
A nonzero unfolding interval and alternate valid sign patterns there
remain possible. No failed check is a geometric nonexistence result.
Keep the earlier wider explicit rectangular/box construction.

No Lean theorem, universal construction, or elimination of the
near-tie mechanism is claimed. The gain is that the tiny parameter
is now an actual geometric unfolding variable, not a specially
fitted rational coordinate. The next useful constructive gate is
to find a similarly simple boundary core that can be unfolded over
a substantially wider modulus region.
