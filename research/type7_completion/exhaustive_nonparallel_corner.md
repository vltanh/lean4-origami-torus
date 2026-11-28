# Ray 3: the complete nonparallel two-stick corner is impossible

## The theorem

There is no sequence of actual canonical ray-3 realizations with `y→∞`
such that, in the transverse coordinates of `relative_cap_bounds.md`,

- `P1,P4→P0=0` and `P3,P6→P2=0`;
- `P5→p` and `P7→q`, with `p,q` linearly independent.

**No comparability assumption on the four collapsing edges is needed.**
This strengthens Section 5 of the earlier relative-bounds note. The proof
uses three small necessary Boolean formulas and one uniform metric sign.
It does not divide by a missing-edge displacement or impose a common
scale on the two caps.

This is an asymptotic computer-assisted research theorem, using the
geometric necessity lemmas in `geometric_audit.md`. It is not yet a Lean
theorem, supplies no numerical height threshold, and does not close the
full ray-3 marking. The labels are part of the statement; applications
to other labels require a checked marked symmetry.

## 1. Directions without a common collapse scale

Put `t=1/y²`. Let the short edges `01,14,23,36` have intrinsic horizontal
lengths `α,β,χ,δ`, and write their physical spatial vectors as `a,b,c,d`.
All four lengths tend to zero. The other two edges in each cap tend to
length `1/2`, so the limiting physical vectors `p=r5-r0`, `q=r7-r2`
satisfy `|p|=|q|=1/2`. Write `z=p·q`; nonparallelity gives `|z|<1/4`.

Use the moving affine frame from `relative_cap_bounds.md` to fix the
four actual anchors at every member of the sequence:

```
0=(0,0,0), 2=(0,0,1), 5=(1,0,0), 7=(0,1,1).
```
This transformation is bounded with bounded inverse in normalized axial
coordinates; its axial shear coefficients are `O(t)`. Every short edge
has axial increment `O(t h_e)` and a transverse norm comparable to its
own positive length. Normalize each of `a,b,c,d` separately. Their
limiting transverse directions are nonzero, irrespective of their
relative lengths.

The nine constant and 42 linear bracket links in the earlier corner
verifier remain necessary. For a singleton coefficient, the exact
bracket has the named short edge as a factor. Its remainder divided by
that edge's own length tends to zero. The two coordinates of `a+b` are
instead divided by `max(α,β)`; those of `c+d` are divided by
`max(χ,δ)`. A zero limiting coefficient leaves the bracket sign free.

We **remove both addition rules for the B coordinates**. These sum
coordinates are independent ternary signs in a necessary relaxation.
Consequently there is no assumption at all about `χ/δ`, or about the
scale of the B edges relative to the A edges.

There are only three possibilities for `α/β`, after a subsequence:

- If the ratio has a finite positive limit, the A coordinate sums obey
  the ordinary ternary addition table. The necessary formula is UNSAT:
  **433 variables, 8,515 clauses**.
- If `β/α→0`, the A sum coordinates have the directional signs of `a`.
  The formula forces `a/α→2p` and `b/β→2q`: in the fixed frame their
  transverse directions are `+E` and `+F`. Blocking precisely these four
  coordinate signs is UNSAT: **433 variables, 8,496 clauses**.
- The case `α/β→0` is equivalent to the second case by the marked
  symmetry `(0 4)(2 6)` together with intrinsic horizontal reflection.

The symmetry preserves the 16 faces. Its horizontal correction gauge is
`(0,-1/2,0,-1/2,0,-1/2,0,-1/2)`, and its vertical cocycle is unchanged.
The verifier checks all 24 edges exactly. It exchanges the two A-edge
roles and preserves the limiting nonparallel anchors.

Thus it remains to exclude `β/α→0` with `a/α→2p`, `b/β→2q`.

## 2. An axial sign uniform in every collapse rate

Write `γ_e` for the vertical correction of a short edge, and

```
R(e,f)=h_e h_f+tγ_eγ_f-E_e·E_f.
```
Let `x2,γ2` denote the canonical vertex correction variables and put

```
C0=-x2+1/4+2γ2=2R(01,67)+2R(01,72).
```
The exact special stress identity is

```
γ_a=α/2-R(01,36).
```
Since the B edge `36` tends to zero, the uniform relative norm and gamma
bounds imply `R(01,36)=o(α)`. The two other B edges have combined length
tending to one and combined physical vector `-(c+d)→0`. Therefore

```
γ_a/α→1/2,                 C0/α→2.              (1)
```
Neither estimate compares `α` with `β,χ,δ`, or `t`.

The limiting intrinsic corrections are

```
x=(0,0,0,0,1/2,0,1/2,0),
γ=(0,0,-1/8,-1/8,0,-z,-1/8,1/8).
```
The short-ring windings determine the horizontal list up to `x2`; the
nearest horizontal inequalities on edges `12` and `16` force `x2→0`.
The small-edge gamma bounds, `C0→0`, and the special stress entries then
give the displayed gamma values. The verifier checks the resulting
sixteen-entry stress matrix exactly.

Before the final affine shear, let `H_i` be normalized axial coordinates
and let `L=|r2-r0|`. Then `2L²t→1/2`. Exact distance subtraction gives

```
2L² H1=-C0+(1-2x2)α+γ_a+2tγ2γ_a.
```
Together with (1), this yields `H1/(tα)→-1`. The same subtraction for
vertex 5 gives `H5/t→1-2z`.

If `M` is the inverse matrix with columns `P5,P7`, the moving-frame axial
coordinate is

```
Z=H-H5*(MP)_x+(1-H7)*(MP)_y.
```
The frame transverse coordinates of `a`, divided by `α`, tend to `(2,0)`;
those of `b`, divided by `β`, tend to `(0,2)`. Also `1-H7=O(t)`. Hence

```
a_z/(tα)→4z-3<0,   a_y/α→0,   b_y/β→2,
|b_z|=O(tβ).                                    (2)
```
All estimates are relative to the named individual edge length.

## 3. A positive cap determinant contradicts the necessary signs

In the fixed frame, the short tip vector is exactly `p=(1,0,0)`.
The all-A cap determinant factors as

```
[0145]=det(a,a+b,p)=det(a,b,p)=a_y b_z-a_z b_y.
```
Using (2),

```
[0145]/(tαβ)→6-8z>0.
```
Thus the actual bracket `[0145]` is eventually strictly positive. This
argument is valid even if `β` is arbitrarily smaller than `α`, either
edge is arbitrarily smaller than `t`, or the B edges have any other
collapse rates.

Add this positive-bracket unit to the dominant-A necessary formula.
It is UNSAT: **433 variables, 8,496 clauses**. The formula retains every
zero leading coefficient as a free generic-completion sign. It uses no
quadratic directional determinant variables and no nonlinear SMT.
This finishes the remaining case and proves the theorem.

## Verification

```sh
python3 research/type7_completion/exhaustive_nonparallel_corner.py /tmp/type7-exhaustive-corner
g++ -O3 -std=c++17 research/orientation_checkpoint/check_unsat.cpp -o /tmp/type7-corner-checker
```

Independently replay the three emitted CNFs with the C++ checker,
requiring explicit `UNSAT nodes ...` output. A zero exit status alone is
not a SAT/UNSAT discriminator for that checker. The generator also
checks the marked symmetry, the exact stress reconstruction and distance
identities, the limiting stress values, and the cap determinant formula.
It depends only on repository inputs, SymPy, and shared libz3.

This direct positive-cap argument replaces the longer seven-formula
proof in the preceding revision. The old missing-`26` estimates were
valid but are unnecessary for this theorem.
