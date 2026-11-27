# An embedded six-vertex core survives tilted C collapse

The local six-vertex exclusion proposed in Gate 2 of the Type 4 roadmap is
false if its hypotheses consist of the core metric equations, strict shortest
lifts, coherent core face orientations, strict core support, the strict K4
conditions, chord `23` contraction and all core simplex intersection tests.
The following exact witness satisfies all these conditions at `y=10^6`.
It is **not a torus realization**: vertices `0,7`, the complete intrinsic
degree-one triangulation and the remaining spatial intersections are absent.

The witness uses the previously untested combination of a tilted C collapse
and vertex `6` approaching the opposite cap. It shows why the next obstruction
must use additional hypotheses from the full torus.

## Exact data

Let `W=10^12`, `y=10^6`, and `delta=1/(4W)`. Write physical intrinsic
coordinates as `p_i=(x_i,H_i/y)`. The anchor is

| Vertex | `x_i` | `H_i` |
|---|---|---|
| 4 | `0` | `0` |
| 5 | `-1/2+delta` | `5(1/2-delta)/64` |
| 1 | `3/16` | `-1/16` |
| 6 | `29/64+3/(128W)` | `W/2-21/64` |

The other two vertices are

    p2=(-7/256+5/(64W), y/2+u/y),
    p3=( 9/128+3/(256W), -y/2+v/y).

Their phases `u,v` are defined algebraically, without using the decimal
approximations below. Let `G` be the spatial Gram matrix of the anchor basis
`(r5,r1,r6)`, obtained by polarizing the prescribed ray-2 edge lengths with
`r4=0`. For `i=2,3`, let `g_i` be its three prescribed dot products against
that basis, and set `z_i=G^{-1}g_i`. Then impose

    z_2^T G z_2 = |p2|^2,
    z_3^T G z_3 = |p3|^2.

Each equation is a quadratic in its own phase. Clear denominators, divide
out the integer content, and choose its sign to make the leading coefficient
positive. **Choose the smaller real root in both equations.** This gives

    u = -0.01210957812944415274505987531041675619...,
    v = -0.07682301364058280989085098081502369031... .

The certificate regenerates these exact quadratic polynomials from the
marked edge data and isolates their roots using rational bounds on their
discriminant square roots.

## What the exact checker proves

Run

    python3 research/type4_completion/core_attack_witness.py

The check uses rational polynomial reduction modulo the two independent
quadratics and rational interval arithmetic at 400-bit precision. It proves:

* The anchor Gram matrix is positive definite, and all fourteen core edge
  length equations hold exactly.
* Every core edge has its prescribed strictly shortest lift. The six actual
  intrinsic faces `152,134,146,165,264,356` have coherent strict orientation.
* All fifteen four-point affine determinants are nonzero.
* Chord `23` is strictly shorter than all nine tested neighboring translates.
* Every five-point affine circuit avoids a partition into disjoint core
  simplices. Its singleton partitions also avoid placing a vertex inside
  the convex hull of its core neighbors.
* In anchor coordinates `lambda4=1-lambda5-lambda1-lambda6`, both roots have
  precisely the negative set `{1}`. In particular both `lambda6` values
  are positive.

Here all four-point determinants are nonzero, so a minimal affine circuit
has five-point support. Every intersection of disjoint simplices would have
a sign-compatible circuit of at most five points. Checking the six five-point
subsets therefore excludes **all** intersections among the core simplices,
including intersections between disjoint triangles. Caratheodory's theorem
also makes the singleton-circuit tests sufficient for strict neighbor support
on this core. No genericity assumption is imposed on the original problem;
nondegeneracy is a property proved for this particular witness.

## Scope of the failed local claim

The cap margins are

    A=3/16-delta, B=5/16, C=delta,

and the vertical tilt remains present: `T=5(1/2-delta)/64`, `R=-1/16`.
Vertex `6` is at vertical distance `21/(64y)` from the opposite cap.
All coordinates are strictly inside the relevant local shortest-lift
domains. Thus discarding the tilted C regime or the far endpoint of the
vertex-6 strip would discard a genuine embedded core.

This does not refute the narrower proposed implication
`lambda6(2)<0 => lambda4(2)<0`: its antecedent is false at this witness.
It refutes excluding the whole six-vertex core from the listed hypotheses.
The full eight-vertex case and Type 4 universality remain open.

## Both vertex-0 completions necessarily cross

The core is locally embedded, but **neither of its two possible metric
completions by vertex `0` can belong to an embedded torus**. Both force the
relative interior of edge `12` through the relative interior of face `045`.
This excludes every choice of vertex `7` for this fixed core as well.

Run the additional exact certificate:

    python3 research/type4_completion/core_attack_leaf.py

Here is the exhaustive reduction used by the checker. Write the unknown
spatial position as `z` in the anchor basis and the unknown intrinsic position
as `(x,H/y)`. Vertex `0` is adjacent to `1,2,3,4,5`. For `j=1,2,3,5`, let
`s_j=p_j+shift(0,j)`. Subtract the equation for edge `04` from the equation
for edge `0j`. The result is linear in the four unknowns `(z,H)`:

    (G r_j).z - (s_j.y/y) H
       = s_j.x*x + (|p_j|^2-|s_j|^2)/2.

Let `M` be this four-by-four matrix and `D=det M`. The checker proves
`D!=0` by exact rational intervals. Cramer's rule gives polynomial vectors
`P,T` with

    M P=D*rhs, M T=D*direction,
    (z,H)=(P+xT)/D.

Both matrix identities are checked exactly modulo the two independent
quadratics defining `u,v`. The remaining equation for edge `04` becomes

    a*x^2+b*x+c=0,

where, with `P_z,T_z` denoting the first three coordinates,

    a=T_z^T G T_z-T_H^2/W-D^2,
    b=2(P_z^T G T_z-P_H*T_H/W),
    c=P_z^T G P_z-P_H^2/W.

The checker proves `a!=0` and `b^2-4ac>0`, isolates both roots with rational
intervals and tests both. Therefore every metric completion of vertex `0`
is included; no heuristic root choice or additional inequality is needed.

For each root, the five-point affine dependence on `{0,1,2,4,5}` has strict
sign parts `{1,2}` and `{0,4,5}`. To avoid division in this test, multiply
the homogeneous row for vertex `0` by `D` and apply the same factor to the
cofactor that omits that row. Every resulting cofactor is affine in `x`,
with coefficients in `Q[u,v]`. Rational intervals certify the five strict
signs. Their affine balance supplies positive barycentric coordinates for
an intersection in both relative interiors.

Thus this fixed core is a certified example of a **global extension
obstruction that the six-vertex tests cannot see**. A full `ray2_2` theorem
would have to establish an obstruction such as this uniformly across its
entire core parameter domain; this certificate does not do so.
