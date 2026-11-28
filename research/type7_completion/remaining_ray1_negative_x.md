# Excluding the negative-X endpoint regime

This note excludes the negative-X case of
`remaining_ray1_endpoint.md`. The other two cases are excluded by the
[nonedge15](remaining_ray1_nonedge.md) and
[positive-axial](remaining_ray1_positive_z.md) companion proofs.
All conclusions below concern an actual unbounded sequence in the
canonical marking-1 mask-04 endpoint, after passing to a subsequence.

Write `t=1/y²`, `h=h1`, and `di=1/2-hi` for `i≠1`. Thus
`h=sum(di)`, all deficits are positive, and every deficit is at most `h`.
The negative-X case has

\[
 d_0/h\to0,\qquad d_2/h\to0,\qquad b_1/h\to0.
\]

Use the axis-01 coordinates, with the transverse direction to vertex3
positive and its transverse normal zero. Let `δ` be the maximum absolute
transverse normal coordinate. The independently replayed virtual12
consequences give

\[
 (Z_5,Z_6,Z_7)/\delta\longrightarrow(1,0,1),\qquad
 Z_2/(\delta h)\longrightarrow0.
\]

The incidence coordinates used in every sign calculation are
`(P_x,Z/δ,2ζ)`, where `ζ` is the spatial axial coordinate divided by `y`.
The factor2 makes the limiting cap levels0 and1. In particular,
the normalized edge12 tends to `(-1,0,0)` when divided by `h`.

## 1. Two upper edges have one common virtual direction

The fifteen surviving generic sign words all contain

\[
 +0134,\ -0145,\ +0147,\ +1345,\ -1347.
\]

Divide edge14 by its own norm in the stretched incidence coordinates,
and write its limiting direction `(X,Y,Z)`. The corresponding five
nonnegative determinant rows are

\[
 Y/2,\qquad Y/2-X,\qquad X-Y/2,
 \qquad -(Y+Z)/2,\qquad (Y+Z)/2.
\]

They force `Y=2X`, `Z=-2X`, and `X≥0`. A normalized direction is
nonzero, so `X>0`. The five analogous signs obtained by replacing1
with2 give exactly the same conclusion for edge24. These assertions
retain every possible relative scale of the two edges.

Consequently both edges are asymptotic to the same positive ray
`(1,2,-2)`. Their difference is edge12, whose direction is `(-1,0,0)`.
If their common scale were bounded by a multiple of `h`, dividing the
vector identity `14-24=12` by `h` would express `(-1,0,0)` as a multiple
of `(1,2,-2)`. Therefore their scale is larger than `h` by an unbounded
factor.

In particular, `M=P4x` is eventually positive and can be used as the
scale. Writing `z=ζ4-ζ1`, we have

\[
 h/M\to0,\qquad Z_4/(\delta M)\to2,\qquad z/M\to-1.       \tag{1}
\]

The final limit is `-1`, because the sign coordinates use `2ζ`.

## 2. Exact polarization fixes two vertical rates

Put

\[
 s=b_1+b_2,\quad c=1-h-h_2,\quad
 p=1-h_2-h_3=d_2+d_3,\quad q=h-p.
\]

Here `0≤p,q≤h`. The intrinsic displacement14 is `(-q,L14)`, where
`L14=s+b3`. The positively oriented actual face214 has double area

\[
 h(b_2+b_3)+p b_1>0.
\]

Because `b1=o(h)`, this gives `L14≥-o(h)`. The exact edge14 equation is

\[
 t(M^2+Z_4^2)+z^2=tq^2+L14^2.
\]

Together with(1), it implies `L14/M→1`; the negative square root is
excluded by the face area. No lower bound on `q` is used.

Write the actual displacement13 as `(L,0,s+t a)`. The bounded axis
height constants give `L→1/2` and `a→-1/2`. Polarizing triangle134 gives
the exact identity

\[
 LM+a z+cq=\frac{s}{t}(L14-z).                            \tag{2}
\]

After division by `M`, the left side tends to1 and `(L14-z)/M→2`.
Thus

\[
 \frac{b_1+b_2}{t}\to\frac12,\qquad
 \boxed{\frac{b_1}{t}\to\frac14}.                       \tag{3}
\]

The second conclusion uses the independently checked endpoint rate
`b2/t→1/4`. Since `b1/h→0`, equation(3) also proves `t/h→0`.
It follows that `b3/M→1` and `v4-1/2=M+o(M)`.

## 3. The second face polarization gives a contradiction

Write the actual displacement12 in the axis gauge as
`(P2x,Z2,b1+t λ)`. Exact polarization against edge01 gives

\[
 \lambda=\frac{d_0-(1/2+d_0)h-H_1b_1}{\ell},
 \qquad H_1=\frac{\ell-v_1}{t},\qquad
 \ell^2=v_1^2+t h_0^2.
\]

The endpoint bounds give `H1→1/4`, `ell→1/2`, and `b1=o(h)`.
Consequently `λ=O(h)→0`. This estimate divides no small edge.

Now polarize the actual face214. Its intrinsic vectors12 and14 are
`(-h,b1)` and `(-q,L14)`, so

\[
 P_{2x}M+Z_2Z_4+\lambda z
 =hq+\frac{b_1}{t}(L14-z).                              \tag{4}
\]

Divide(4) by `M`. The left side tends to zero: `P2x→0`,
`Z4/M=(2+o(1))δ`, `Z2→0`, and `λ→0`, while `z/M→-1`.
Also `hq/M→0` because `q≤h=o(M)`.
Since `(L14-z)/M→2`, equation(4) forces `b1/t→0`.
This contradicts equation(3).

Equivalently, subtracting(4) from(2) gives the single exact identity

\[
 (L-P_{2x})M-Z_2Z_4+(a-\lambda)z+(c+h)q
 =\frac{b_2}{t}(L14-z).                                 \tag{5}
\]

After division by `M`, its left side tends to
`1/2+(-1/2)(-1)=1`, whereas its right side tends to
`(1/4)(1-(-1))=1/2`. This formulation uses only the previously
proved rate `b2/t→1/4`; it eliminates `b1/t` altogether.

The contradiction retains arbitrary rates for `t`, the first transverse
width, every horizontal deficit, and the additional small upper edges.
No global metric parametrization or regularity of the other cap is used.

## Replay and scope

Run

```bash
python research/type7_completion/remaining_ray1_negative_x.py
```

The program first replays the published426 virtual12 certificates and
17 consequence certificates against the freshly enumerated331 primary
words. It then binds the fifteen negative-X survivors, reconstructs the
upper virtual determinant rows, and checks both exact face polarizations
and their difference symbolically. It also retains a few independently
checked local identities for further endpoint work.

All fifteen negative-X survivors are excluded. The companion proofs
complete the [two-block limit exclusion](ray1_two_block_exclusion.md).
