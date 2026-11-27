# Ray 2: a uniform four-branch metric-core reconstruction

This is a necessary-and-sufficient reconstruction for the **fourteen edge
equations of the six-vertex core** `123456`, whose only missing edge is
`23`. It is valid throughout the second sharp-ray marking. It does not
assert core embeddedness or exclude either full Type 4 case. In particular,
the embedded core in [core_attack_witness.py](core_attack_witness.py) shows
that a full obstruction must use additional conditions.

The practical gain is that eight real intrinsic parameters determine at
most four core candidates. The two remaining phase equations have strictly
positive quadratic coefficients, uniformly bounded below at the elongated
target. No linear or identically-zero quadratic branch is hidden at a cap
collapse.

## 1. Anchor and the eight parameters

Fix `y >= sqrt(3)/2`, `W=y^2`, `p4=r4=0`, and write physical intrinsic
coordinates as

    p5=(-s,T/y), p1=(a,R/y), p6=(b,Z/y),
    p2=(c,y/2+u/y), p3=(d,-y/2+v/y).

The eight independent parameters for this reconstruction are
`s,T,a,R,b,Z,c,d`. Use the strict K4 anchor `(4,5,1,6)`. Its spatial Gram
matrix in basis `(r5,r1,r6)` is

    G = [s^2+T^2/W,              -sa+TR/W+a+s-1/2, -sb+TZ/W+b+s-1/2;
         -sa+TR/W+a+s-1/2,       a^2+R^2/W,       ab+RZ/W;
         -sb+TZ/W+b+s-1/2,       ab+RZ/W,          b^2+Z^2/W].

Require `G` positive definite, as supplied by the strict-anchor premise.
All quantities below are exact rational functions of the parameters and
`W`. Inverting `G` requires no uniform lower bound on its determinant.

Define

    V2=(1+T/W, 1+R/W, Z/W),
    H2=((s+c)/2-sc-T/2-1/8,
        ac+(a-c)/2-R/2-1/8,
        bc+Z/2),

    V3=(-1+T/W, R/W, -1+Z/W),
    H3=((s+d)/2-sd+T/2-1/8,
        ad-R/2,
        bd+(b-d)/2+Z/2-1/8).

Polarization of the prescribed edges gives the three anchor dot products

    g2 = H2+u V2,             g3 = H3+v V3.

Consequently, in anchor-basis coefficients,

    r2 = G^(-1) g2,           r3 = G^(-1) g3.

Here and below a displayed coordinate vector for a spatial point denotes
its coefficients in that basis; its squared norm is computed with `G`.

## 2. Exactly two scalar quadratics

The remaining radial equations are

    F2(u)=(H2+u V2)^T G^(-1)(H2+u V2)
          -c^2-W/4-u-u^2/W = 0,

    F3(v)=(H3+v V3)^T G^(-1)(H3+v V3)
          -d^2-W/4+v-v^2/W = 0.

Their leading coefficients are

    A2=V2^T G^(-1)V2-1/W,
    A3=V3^T G^(-1)V3-1/W.

For each quadratic retain both real roots, including a repeated root.
A negative discriminant rejects that anchor/`c,d` choice. Then retain
the exact shortest-lift, face-orientation, nonedge-contraction, strictness
and embedding tests required by the chosen application.

Every core metric realization supplies one of these root pairs because
four affinely independent anchors uniquely determine a point from its four
distances. Conversely, each root pair has all fourteen prescribed core
edge lengths: the three dot-product equations and the radial equation
recover its four distances to the anchor, while the anchor already has
its six prescribed edges. The edge `23` is absent and imposes no equality.

## 3. Positivity that survives all cap collapses

The global ray-2 phase estimates give

    0<s<1/2,    |T|<s/2.

Let `w2`, `w3` be the spatial derivatives of the reconstructed `r2`, `r3`
with respect to `u`, `v`, respectively. The first anchor dot-product
equations give

    r5 dot w2=1+T/W,       r5 dot w3=-1+T/W,
    |r5|^2=s^2+T^2/W.

Cauchy--Schwarz therefore proves, with the matching sign,

    A2 >= (W+2T-s^2)/(W s^2+T^2),
    A3 >= (W-2T-s^2)/(W s^2+T^2).

Both numerators are strictly greater than `W-s-s^2`. Since `s<1/2`
and `W>=3/4`, this is strictly positive. Thus both equations are genuine
quadratics on the entire sharp ray, including the hexagonal endpoint.
The proof does not depend on the position of vertex 6, the cap area, or
which of the three cap margins tends to zero.

For the elongated range `W>=1`, there is also the uniform lower bound

    A2>4/5,    A3>4/5.

An exact positive decomposition, for either sign, is

    W +/- 2T - s^2 - (4/5)(W s^2+T^2)
      = (W-1)(1-4s^2/5)
        +(1-2s)(1+s)
        +(s +/- 2T)
        +(4/5)(s^2/4-T^2) > 0.

This remains uniform when edge `45` tends to zero or the anchor volume
tends to zero through positive values. It controls these two phase
quadratics; it does not bound the conditioning of every entry of `G^-1`.

## 4. Use and scope

At most two roots for `u` and two for `v` give at most four core candidates
per eight-parameter input. This replaces a continuous search in both
phases by finite exact root choices without deleting endpoint or tangency
branches. The global phase bounds `-3/8<u<1/8`, `-1/8<v<3/8` can be applied
immediately after root isolation.

Leaves 0 and 7 still have to be added and all full-torus checks retained.
Their reconstruction produces further line/conic intersections; this
note makes no claim that every exceptional line is nonzero. A resulting
full solver must handle those exceptional strata or prove them impossible.

Replay the polynomial formulas and positive decomposition with:

    python3 research/type4_completion/ray2_attack_verify_conics.py

No Type 4 row is excluded by this reduction.
