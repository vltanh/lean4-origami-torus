# Exhaustive noncollinear-cap shape classification

**Conclusion.** Every sequence of actual canonical ray-3 realizations
with `y→∞` has, in each convergent transverse subsequence, at least one
cap lying entirely on a line. This strengthens the earlier conclusion
that one cap has a collinear triple. The proof combines the finite
classification below with the closed-base trapezoid extension in
`cap_limit.md`.

This remains an asymptotic research reduction. It supplies neither a
finite-height bound nor a full ray-3 exclusion. Entirely collinear caps,
including all their vertex coincidences, remain for further analysis.

## 1. A complete finite list of noncollinear cap types

Four labelled planar points that do not all lie on one line have exactly
one of the following forms:

1. **Q:** all four triples are noncollinear;
2. **F:** exactly one triple is collinear, and its three vertices are
   distinct;
3. **C:** exactly one pair of vertices coincides, and the other two
   vertices together with this point are noncollinear.

For the third type, a cyclically adjacent pair gives a triangle with
one collapsed ring edge; an opposite pair gives two distinct segments,
each traversed out and back. There are one Q type, four choices of the
flat triple F, and six choices of coincident pair C: eleven labelled
classes per cap and **121 class pairs** in total.

The list is exhaustive. With four distinct points, two collinear triples
share two distinct points and therefore force all four points onto one
line. With only three distinct points, exactly one pair coincides; with
at most two distinct points the cap is entirely collinear.

## 2. Retain a direction even for a collapsed edge

For every short ring edge, its transverse vector divided by its positive
intrinsic horizontal length has a nonzero limiting vector. This follows
from the uniform relative norm and axial bounds in
`relative_cap_bounds.md`. Thus there are always eight nonzero limiting
edge directions, even if some unnormalized ring edges vanish.

All sixteen cross-cap directional cross products and eight consecutive
within-cap cross products have the prescribed generic-completion signs
weakly. Their determinant errors, divided by the **product of their own
edge lengths**, tend to zero. The comparison is strict whenever the
corresponding limiting cap triangle is noncollinear. This is the reason
the finite direction check must retain a virtual direction for a
collapsed edge instead of deleting that edge.

A nonzero cap triangle also fixes the sign of each corresponding 3+1
bracket independently of the opposite vertex. The coincident-pair types
impose the additional relative signs of their two nonzero triangle
areas. These conditions filter the complete **1,888** necessary generic
orientation/linking models from `solver_chambers.py`.

Represent every direction by a positive multiple of a signed line
direction in one half-open interval of length pi. There are only 128
relative sign choices after global reversal. A prescribed determinant
sign becomes an order comparison between the two line directions.
Take the transitive closure of those weak comparisons. A strict
comparison cannot lie in a strongly connected component; every component
forces all its line directions to coincide.

For an F cap, the two nonzero edges through its flat triple must have
the same line direction, with either relative sign. For a C cap, every
nonzero ring-edge pair has the exact direction relation of the triangle
or two-segment shape. These are further strict comparisons or signed
line equalities. The collapsed edge's virtual direction is left free.

The complete result is:

| Class-pair outcome | Number of labelled class pairs | Weak direction cells |
|---|---:|---:|
| No possible weak direction order | 102 | 0 |
| Common parallel bases, opposite directions within each cap | 17 | 816 |
| Two noncollinear out-and-back caps | 2 | 96 |
| **Total** | **121** | **912** |

Every class involving an F cap is eliminated. Except for the last two
cases, the surviving models are exactly the sixteen cap models used in
`cap_limit.md`. A common component forces either all even or all odd
ring edges onto the same line, with opposite signs for the two bases in
each cap. The caps have positive leg heights because they are assumed
noncollinear. A triangle is a trapezoid with one base of length zero.
No noncollinear cap can have both its bases zero.

## 3. The common-base cases contradict the stress identity

The 17 class pairs are the previous nondegenerate trapezoids and their
triangle boundaries. The normalized virtual base directions preserve
exactly the boundary signs needed in the separation inequalities of
`cap_limit.md`; its normalized-minor boundary argument covers the zero
base lengths. The exact cone inequality already includes these closed
boundaries.

Both caps still have positive leg heights. Consequently the product of
the two total leg-length excesses over their horizontal projections is
strictly positive, even if a base in either cap has length zero. The
stress expression is therefore strictly positive, contradicting the
exact mask identity. This excludes all 17 class pairs.

## 4. The two out-and-back cases also contradict the stress identity

The only remaining labelled coincidence pairs are

```
A: 0=4, B: 3=7;             A: 1=5, B: 2=6.
```
The marked symmetry `(1,0,7,6,5,4,3,2)` exchanges them. The verifier
checks it through `marked_symmetries()`, including its lattice isometry
and vertex gauge. It is enough to treat the first pair.

Write its cyclic edge vectors and positive lengths as

```
A: (a,-a,p,-p),  lengths (α,α,u,u),
B: (c,d,-d,-c),  lengths (χ,δ,δ,χ).
```
The A arms `a,p` are nonparallel; likewise the B arms `c,d`. Write
`a=α â`, `p=u p̂`, with unit directions `â,p̂`, and set
`k=â·p̂<1`. All four lengths are strictly positive in this limiting
shape. The perimeter constraints are `2(α+u)=2(χ+δ)=1`.

All 48 weak direction cells for this labelled pair force exactly one
of these two alignments:

```
I:   c=-χ â,   d=δ p̂;
II:  c=-χ p̂,  d=δ â.
```
The stress mask identity reduces exactly to

```
(p-a)·(c+d)=(α-u)(χ-δ).                         (1)
```
In alignment I, the left side minus the right side of (1) is

```
(uχ+αδ)(1-k)>0.
```
In alignment II it is

```
-(uδ+αχ)(1-k)<0.
```
Both contradict (1). These identities are checked symbolically. Thus
the last two class pairs are impossible, completing the classification.

### Stronger point-sign alternative

The [V/V point-sign proof](exhaustive_vv_geometry.md) now excludes both
alignments directly. Only 32 fixed mixed brackets are needed, and the
two formulas are contradictory by unit propagation. This alternative
uses no metric stress, so it also applies to anisotropically stretched
limits whose physical length cost becomes a seminorm. The stress
identities above remain valid independent checks.

## Verification

```sh
python3 research/type7_completion/exhaustive_cap_shapes.py
```

The verifier freshly generates the 1,888 generic sign models using the
verified marked symmetries, checks every one of the 121 class pairs and
all 128 relative line signs, and checks the exact V/V stress identities.
It takes about eight seconds in the current environment. It reads no
cached model manifest or exploratory scratch script.

Completeness of the underlying model enumeration has the independent
RUP coverage certificate documented in `solver_compilation.md` and
replayed by `solver_verify.py`. The additional shape and weak-order
checks are finite integer computations; they use no nonlinear solver or
floating-point test.
