# Type 4 ray 2: exact cap-sidedness algebra

This checkpoint concerns the active `ray2_2` family at
`tau = 1/2 + 10^6 i`. It does **not** close that family. It gives an exact
cap-sidedness test, uniform slack bounds, and an exact diagnostic showing why
an argument using only core metric equations and shortest lifts cannot prove
the proposed sign. The diagnostic has an explicitly certified self-intersection.

## A cap-sidedness test with no unknown chord or square root

Use the universal-vertex gauge `r4 = p4 = 0`. Write

    D_ij = |r_i-r_j|^2,
    G_ij = (D_4i+D_4j-D_ij)/2,
    M_ij = D_45 G_ij-G_5i G_5j.

Thus `M` is `D_45` times the Gram matrix of the components perpendicular
to `r5`. The clique `{4,5,1,6}` is strict by the existing K4 premise. Hence

    Delta = M_11 M_66-M_16^2 > 0.

For `i=2,3`, put

    N_i = M_11 M_6i-M_16 M_1i.

Project `r_i` to `r5`'s perpendicular plane, expand in the independent
projected vectors `r1,r6`, and solve the two Gram equations. The coefficient
of the second vector is `N_i/Delta`. Consequently

    [451i]/[4516] = N_i/Delta,
    sign([4512][4513]) = sign(N_2 N_3).

Every distance occurring here is a prescribed edge distance. In particular,
the missing edge `23` is not an input. The argument divides only by the
strict positive K4 Gram determinant; it imposes no uniform lower bound on a
cap area. It therefore remains exact near all collapsing cap boundaries.

## Slack bounds uniform as edge 45 collapses

Let `W=y^2` and write

    p5=(-s,T/y), p2=(c,y/2+u/y), p3=(d,-y/2+v/y),
    S_ij=G_ij-p_i dot p_j.

The ray-2 winding and strict shortest-lift bounds give

    0<s<1/2, |T|<s/2,
    S_15=p1.x+s-1/2, S_56=p6.x+s-1/2,
    S_25=u-T+(s+c)/2-1/8,
    S_35=T-v+(s+d)/2-1/8.

All four displayed `S` quantities are strictly positive. Define

    eta=T/s, alpha=S_15/s, beta=S_56/s,
    gamma=S_25/s, delta=S_35/s.

Then

    |eta|<1/2, 0<alpha,beta<1,
    0<gamma<1/2-eta, 0<delta<1/2+eta,
    gamma+delta<1.

For the last bounds use the positive radial shortest slacks

    e1=1/8-u-|c|/2, e4=1/8+v-|d|/2.

Indeed `S_25+e1=s/2-T+min(c,0)` and
`S_35+e4=s/2+T+min(d,0)`. Their sum is at most `s`, with
`e1,e4>0`. No additive error survives division by a possibly tiny `s`.

## An exact metric core with the opposite cap signs

Run:

```sh
python research/type4_completion/algebra_core_witness.py
```

The checker uses SymPy for rational polynomial algebra and rational intervals
for every strict sign. It does not use floating-point signs or a numerical
solver. Set `W=10^12`, `Y=10^6`, and choose

    p4=(0,0),                  p5=(-1/4,0),
    p1=(1/4+1/(128W),0),       p6=(9/32,Y/4),
    p2=(0,Y/2+u/Y),            p3=(3/32,-Y/2+v/Y).

The anchor spatial Gram matrix is determined by the ray-2 edge lengths.
It is positive definite. Express each of `r2,r3` in the spatial basis
`(r5,r1,r6)` using its three prescribed dot products. Its remaining radial
length equation is a rational quadratic in `u` or `v`. Choose the larger
root for `u` and the smaller root for `v`; this is an exact algebraic
specification, reproduced from the edge data by the checker.

The checker establishes:

- all 14 core edge equations and their strict shortest-lift inequalities;
- coherent strict orientation for the six present intrinsic faces;
- all 15 four-point affine determinants are nonzero;
- strict contraction for chord `23` against all nine shifts in `{-1,0,1}^2`;
- `[4512]/[4516] < 0 < [4513]/[4516]`.

For orientation only, the two ratios are approximately
`-0.0655911179773` and `0.2111456180003`.

This configuration is **not an embedded core**. If

    r2=lambda5 r5+lambda1 r1+lambda6 r6,
    lambda4=1-lambda5-lambda1-lambda6,

then the checker proves

    lambda1,lambda5>0, lambda4,lambda6<0.

The exact affine identity

    lambda1 r1+lambda5 r5 = r2-lambda4 r4-lambda6 r6

has positive coefficients on both sides and equal coefficient sums. It
certifies an intersection of the relative interiors of edge `15` and face
`264`. Thus this witness cannot extend to an embedded Type 4 realization.
It does rule out a proof of `N_2 N_3>0` from only the listed core metric,
nearest-lift, face-orientation, strict-K4, and chord-contraction conditions.

The unresolved stronger target adds the allowed Radon sign patterns of both
five-point cliques, or the equivalent actual core nonintersection conditions.
No claim about that stronger target follows from this diagnostic.
