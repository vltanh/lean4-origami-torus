# Type 4, ray2_2: exact identities at the collapsing cap

**The active case remains open.** This note treats only the fixed target
`tau=1/2+10^6 i`, marking `ray_2`, cell `20220012`, with lift vector
`(0,0,0,-1,0,0,0,-1)`. Its designated caps are `145` and `0273`;
vertex 6 lies in the broadened intervening strip. Endpoints of that strip
and every cap degeneration remain included.

The identities below hold before imposing the cell bounds and therefore
remain valid at all of its boundaries. They preserve the small cap
parameters instead of dividing by an uncontrolled cap area. They do not
prove a sidedness assertion or exclude this case.

## 1. Coordinates and the three positive cap margins

Put `y=10^6`, `W=y^2`, and use physical intrinsic coordinates, so the
lattice generators are `(1,0)` and `(1/2,y)`. In the established gauge
at vertex 4, write

    p4=(0,0), p5=(-s,T/y), p1=(a,R/y),
    p2=(c,y/2+u/y), p3=(d,-y/2+v/y).

Write `r_i` for the spatial vertices and set `r4=0`. The horizontal
winding triangle `145`, together with strict shortest lifts, gives

    0<s<1/2, 0<a<1/2, 0<k=1-a-s<1/2.

Equivalently,

    A=a+s-1/2>0, B=1/2-a>0, C=1/2-s>0,
    A+B+C=1/2, s=A+B, a=A+C, k=B+C.

The exact spatial Gram entries of this triangle are

    |r5|^2=s^2+T^2/W = L,
    |r1|^2=a^2+R^2/W,
    r5 dot r1=q0+RT/W,
    q0=A-as=A/2-BC.

In particular, if `Delta=|r5 cross r1|^2`, then

    Delta = 2ABC*L/s^2 + [sR-q0*T/s]^2/W.             (1)

The ordinary squared area of triangle `145` is `Delta/4`.
Both terms in (1) are nonnegative, and the first is strictly positive.
This is an exact finite-metric identity, including when `s`, `A`, `B`,
or `C` is arbitrarily small. The checker clears the positive denominator
`s^2`; it does not rely on a numerical lower bound for `s`.

## 2. Actual points on the opposite edges

Each possible collapse of the horizontal triangular cap has a concrete
vertex-to-edge interpretation. Define the following points on actual
edges, with all interpolation weights strictly positive:

| Small margin | Vertex | Point on opposite edge | Denominator | Vertical numerator |
|---|---|---|---|---|
| A | 4 | `bA=(s*r1+a*r5)/(a+s)` | `ellA=a+s` | `GammaA=sR+aT` |
| B | 5 | `bB=(k*r4+s*r1)/(s+k)` | `ellB=s+k=1-a` | `GammaB=sR-ellB*T` |
| C | 1 | `bC=(k*r4+a*r5)/(a+k)` | `ellC=a+k=1-s` | `GammaC=aT-ellC*R` |

Their exact distances satisfy

    ellA^2 |bA-r4|^2 = 2asA + GammaA^2/W,
    ellB^2 |bB-r5|^2 = 2skB + GammaB^2/W,
    ellC^2 |bC-r1|^2 = 2akC + GammaC^2/W.            (2)

These are distances to the displayed edge points, not necessarily the
minimum distances to those edges. Each formula follows by expanding a
squared norm with the three prescribed side lengths of triangle `145`.
Thus a small-margin regime must retain its corresponding vertical
numerator as well; small `A`, for example, alone does not imply a small
distance from vertex 4 to edge 15.

## 3. Positive nearest-lift deficits control the same scale

For the A-corner set `ell=a+s`, `Gamma=sR+aT`, `K=2asA`, and `b=bA`.
Define three exact edge deficits:

    S12=(a-c)/2+u-R-1/8,
    S25=(s+c)/2+u-T-1/8,
    S35=(s+d)/2+T-v-1/8.

All three are strictly positive: each equals one half of the difference
between the squared length of the unshifted intrinsic chord and the
prescribed strictly shortest edge lift. Define

    E2=s*S12+a*S25>0, E3=a*S35>0,
    h2=1/2+u/W, h3=-1/2+v/W,
    n2=c^2+W*h2^2, n3=d^2+W*h3^2.

Polarization of the preserved edge lengths gives

    ell (b dot r2) = Gamma*h2+E2,
    ell (b dot r3) = Gamma*h3+E3,
    ell^2 |b|^2 = K+Gamma^2/W.                      (3)

Consequently Cauchy--Schwarz supplies the following intrinsic-only
necessary inequalities, without division by any small cap quantity:

    E2^2+2*Gamma*h2*E2 <= K*n2+Gamma^2*c^2/W,
    E3^2+2*Gamma*h3*E3 <= K*n3+Gamma^2*d^2/W.        (4)

There is also a coupled inequality using the actual nonedge `23`.
Both lattice competitors give

    |r2-r3|^2 <= Uplus, Uminus,
    Uplus =(d-c+1/2)^2+(v-u)^2/W,
    Uminus=(d-c-1/2)^2+(v-u)^2/W.

Applying Cauchy--Schwarz to `b` and `r2-r3` in (3) yields, separately
for either value of `U`,

    [Gamma*(h2-h3)+E2-E3]^2 <= (K+Gamma^2/W)*U.     (5)

Equations (2)--(5) keep the vanishing margin and vertical tilt together.
They are necessary conditions for the full case. They do not by
themselves prove that the two long vertices lie on the same side of the
cap plane. Other vertices and actual embedding constraints cannot be
discarded.

## 4. The precise affine-sign gate being investigated

Use the strict K4 anchor `(4,5,1,6)`. There are unique coefficients

    r2=lambda5*r5+lambda1*r1+lambda6*r6,
    lambda4=1-lambda5-lambda1-lambda6.

In particular

    lambda6=[4512]/[4516].

Every coefficient is nonzero because every four-element subset of
`{1,2,4,5,6}` is a K4. The necessary strict-support and embedding
conditions permit only the following sets of negative affine
coefficients:

    {1}, {6}, {1,4}, {1,6}, {4,5}, {5,6}.           (6)

Here the index set is `{1,4,5,6}`; the coefficient of vertex 2 in the
affine dependence is fixed positive. To verify (6), strict neighbor
support excludes a singleton versus four-point Radon partition. Of the
ten two-versus-three partitions, four give a segment crossing one of
the actual faces `146`, `165`, `152`, `264`. The other six are exactly
(6). In particular, an embedded configuration must satisfy

    lambda6<0  implies  lambda4>0.                 (7)

A possible decisive metric lemma for this part of the argument would be
the opposite implication

    [all exact ray2_2 metric, nearest-lift, face, and cap conditions]
    and lambda6<0  imply  lambda4<0.               (8)

**Statement (8) is not proved here.** It is a focused proposed gate, not
an added constraint on the problem. Neither (7) nor the identities above
exclude `lambda6>0`, and proving (8) alone would still leave the other
vertices' sidedness and the remaining cap configurations to resolve.

For clarity, the exact elementary crossing criteria in these coordinates
are:

* Edge `24` crosses face `165` if all three of `lambda5,lambda1,lambda6`
  are positive and `lambda5+lambda1+lambda6>1`.
* Edge `15` crosses face `264` if `lambda5,lambda1>0`, `lambda6<0`, and
  `lambda5+lambda1+lambda6>1`.
* Edge `46` crosses face `125` if `lambda5,lambda1<0`, `lambda6>0`, and
  `lambda5+lambda1+lambda6<1`.

All inequalities are strict in these statements. Vanishing coefficients
need not be assigned to a generic sign chamber: the strict K4 premise
already excludes them for this five-vertex set. Metric counterexamples
to a sign-only conjecture must be checked against these actual crossings
before being treated as embedded candidates.

## Reproduction and status

    python3 research/type4_completion/verify_ray2_2_geometry.py

The checker verifies the polynomial identities, the dot-product and
Cauchy--Schwarz expansions, and the finite local Radon sign list by exact
arithmetic. The geometric implications of Cauchy--Schwarz, strict support,
and minimal affine circuits are given above and inherited where stated.
No numerical feasibility result is used. No full `ray2_2` case, other
marking, or Type 4 universality claim is closed by this note.
