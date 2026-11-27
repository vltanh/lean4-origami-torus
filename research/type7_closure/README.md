# Type 7 closure attempt: exact scope

Types 4 and 7 remain open on the sharp-rhombic ray. This note rules out a
specific proposed shortcut: applying the existing open-strip trapezoid
construction in a different lattice basis and retuning its parameters.
It supplies no new marking exclusion or universality theorem.

## The modularly transformed sharp ray

For `tau = 1/2 + i*y`, reflection of `-1/tau` gives the equivalent modulus

    x = 1 / (2*(y^2+1/4)),
    w = y^2 / (y^2+1/4)^2 = 2*x-x^2.

For `y >= sqrt(3)/2` this has `0 < x <= 1/2`. Except at the hexagonal
endpoint, it lies below the domain `w >= 1-x^2` of the existing
open-strip certificates. Merely changing basis therefore does not apply
those certificates.

## An exact obstruction for every parameter choice in the existing chamber

Use the trapezoid formulas in
`../torus_remaining_certificate/verify.py`, now with arbitrary `H>0`
and `r`, and put

    D = H-1+H*x,
    N = D^2 + H^2*(2*x-x^2) > 0.

Assume the formulas are defined (`D != 0`, `D+r != 0`). Let `Aijk` be
the oriented double area of the three planar points `i,j,k` before
multiplication of the second coordinate by `sqrt(w)`. On the transformed
sharp arc the formulas simplify to

    A302 = H^2*(H-1)*D / (2*(D+r)*N),
    A214 = -H*(D+r)/(2*D),
    A524 = H*(H-1)*(2*H*x-1)/(2*N),
    A674 = H*(2*H*x-1).

Consequently the exact identity

    2*A302*A214*A674 + H^3*A524 = 0

holds. The existing chamber requires

    A302 > 0, A214 < 0, A524 > 0, A674 < 0.

Both summands in the identity would be positive, a contradiction. Reversing
all face orientations changes the sign of both summands and gives the same
contradiction. These four faces are unchanged by the Type 4 diagonal flip,
so the obstruction applies to both current constructions.

This sign identity alone excludes the existing chamber. The following
argument also excludes every other flat chamber of the same formulas.
Neither result excludes a singular limit requiring different formulas
or a genuinely different spatial construction.

## Stronger theorem: no flat member in any chamber of this family

The sign-chamber obstruction strengthens to a full obstruction for this
**particular trapezoid parametrization**. Fix `0<x<=1/2`,
`w=2*x-x^2`, `H>0`, and defined formulas. There is no member with all
faces nondegenerate and every cone angle `2*pi`, for either the Type 7
face list or its specified Type 4 diagonal flip.

Write the planar points as `P_i=(X_i,Y_i)` and the physical points as
`(X_i,sqrt(w)*Y_i)`. In this paragraph an angle means the ordinary
Euclidean angle, between zero and pi.

**Flatness at vertex 2.** The points `0,2,4` are collinear, with vertex 2
strictly between the other two. Its Type 7 link splits into paths
`0,3,5,4` and `4,1,7,0`. Each path of directions has angular length at
least pi, since its endpoints are antipodal. If their total is `2*pi`,
both paths attain this lower bound and follow a single semicircle
monotonically. Nondegenerate faces make each turn strict. The second
path contains vertex 7 at height `H>0`, so `Y1>0` and `A217>0`.
The first path gives `Y3*Y5>0`. For Type 4 that first path is
`0,3,6,5,4`; the same conclusions hold.

The formulas give

    Y1 = H*(D+r)/D,
    Y3 = H^2*(H-1)*D/((D+r)*N),
    Y5 = H*(H-1)*(2*H*x-1)/N,
    A217 = -H*r*(2*H-1)/(2*D).

Thus `Y1>0` and `Y3*Y5>0` force `2*H*x-1>0` (the nonzero face areas
exclude `H=1`). Since `x<=1/2`, we get `H>1` and `D>0`. Now `A217>0`
and `Y1>0` give `-D<r<0`.

**The angle at vertex 7 is too small.** Put `a=H*x>1/2` and
`h=H*sqrt(w)>0`. The direction to vertex 6 is the positive horizontal
axis. Every other neighbor lies strictly below that axis. In particular

    Y5-H = -H^2*(2*a+H-1)/N < 0.

Let `phi_j` be the argument in `(-pi,0)` of the direction from vertex 7
to `j`, for `j=0,1,2,4,5`, and put `phi_6=0`. Then

    phi_0 < phi_4 < phi_5 < 0,
    phi_0 < phi_2 < phi_1 < 0.

For the first ordering, the vectors to 0 and 4 are `(a-1,-h)` and
`(a,-h)`, and

    A745 = H*(H-1)*(2*a-1)*(2*a+H-1)/N > 0.

For the second, the vector to 2 is `(a-1/2,-h)`, and the vector to 1 is
a positive multiple of `(1,-q*sqrt(w))`. Its cross product with the
vector to 2 has the sign of

    -H+q*(a-1/2) = H*(1/2-H)/D < 0.

The unchanged link of vertex 7 is `0,5,4,6,1,2,0`. Because all its
neighbor arguments lie in a single half-open semicircle, its cone angle
is the sum of the absolute argument differences, namely

    alpha_7 = 2*phi_5 - 2*(phi_0+phi_4).

Finally `phi_0+phi_4>-pi`. One direct check is that the imaginary part
of `(a-1-i*h)*(a-i*h)` is `-h*(2*a-1)<0`; since the sum belongs to
`(-2*pi,0)`, it must belong to `(-pi,0)`. As `phi_5<0`,

    alpha_7 < -2*(phi_0+phi_4) < 2*pi.

This contradicts flatness at vertex 7 and proves the theorem. The same
argument applies after a global reflection of the planar image.

All algebraic identities used in the angle argument are checked in the
same exact verifier. The angular path argument is elementary triangle
inequality and equality on the unit circle. This result excludes all
parameter chambers of the stated formulas; it makes no assertion about
other planar folding families or spatial origami tori.

## Reproduction

    python3 research/type7_closure/verify_transformed_chart.py

The checker uses exact SymPy rational identities and passed on the current
repository formulas. No floating computation is a premise.

## Full ray_3 metric/linking experiment

`linked_metric.py` imports the archived exact 18-variable Gram formulation
and augments it with the following necessary conditions:

- all 524 minimal affine-circuit tests between disjoint simplices (the
  existing positive distances handle the other 28 vertex pairs);
- the necessary generic orientation formula and unlinking of both short
  ring pairs, with a Boolean sign completion for zero nonclique minors;
- linking number of magnitude two between the long rings `0246` and `1357`.

The last condition is necessary at `y>=4`. The earlier diameter theorem
makes the horizontal slope unlinked. Write its linking form as
`q(m,n)=B*m*n+C*n^2`; the discriminant-one theorem gives `B=+1` or `-1`.
The two disjoint-triangle slopes `(0,-1)` and `(-1,1)` give
`|C|<=1` and `|C-B|<=1`, because two triangles link at most once.
Hence `C=0` or `C=B`, so `q(1,-2)=-2*B+4*C` has magnitude two.
The archived exact embedded orientation witness has long-ring linking
`+2`. The archived nonembedded metric witness has zero and is excluded
by this added condition.

The actual spatial coordinates are represented by their inner products
with a positive definite anchor basis. This is an invertible linear map,
so the affine incidence tests apply to them directly. Nonclique minors
are constrained only weakly by the auxiliary generic signs; the full
minimal-circuit conditions still apply to the actual minors. Thus an
actual embedding with coplanar nonclique quadruples is not lost merely
because it is nongeneric. A sufficiently small generic perturbation
supplies its necessary orientation/linking completion, as in the earlier
orientation reduction. The geometric premises and linking-form theorem
are inherited from those prior arguments.

To reproduce a 300-second solver attempt, with generated output outside
the repository:

    timeout 330s python3 research/type7_closure/linked_metric.py /tmp/ray3_y4_linked.smt2 4 300000
    timeout 330s python3 research/type7_closure/linked_metric.py /tmp/ray3_y1000000_linked.smt2 1000000 300000

Each query has 18 real variables, 312 Boolean variables, and 8,075 Boolean
clauses, in addition to the metric and affine-circuit constraints. A
solver timeout is not an exclusion; a satisfying assignment would still
need certified exact reconstruction and validation. These systems do not
by themselves resolve ray_3 or either of the other remaining markings.

### Recorded outcome

Both systems were generated and submitted to libz3 with a 300,000 ms
solver timeout. Neither call returned a result within more than 300
seconds of wall time; both were externally interrupted (process status
130). The exact internal stage at interruption was not identified.
Consequently no SAT, UNSAT, or solver-reported UNKNOWN result is claimed.
The `timeout` wrapper in the reproduction commands bounds this behavior
in future runs. The branch count and Type 7 universality status are
unchanged.
