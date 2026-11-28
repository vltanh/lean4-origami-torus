# A C0 collinear-cap boundary extension

For ray 1 and `0<v<=u<1/2`, the following C0 limits are impossible:

- The upper cap 123 is collinear with vertex 1 strictly between 2
  and 3, and the lower cap 067 is noncollinear.
- The lower cap 067 is collinear with vertex 7 strictly between 0
  and 6, and the upper cap 123 is noncollinear.

In deficit notation these are respectively `d2=0<d1` with a regular
lower cap, and `d6=0<d7` with a regular upper cap. The result combines
six new independently checked Boolean certificates with the existing
metric turning and height-order arguments. It does not close every
collinear-cap boundary.

## 1. A zero-safe source for a collinear upper cap

First let the upper cap be collinear and the lower cap regular.
The ray-1 budget gives `d1+d2<1/2`, so its possible orders are

| Deficits | Upper order |
|---|---|
| `d1=0<d2` | 3 strictly between 1 and 2 |
| `d2=0<d1` | 1 strictly between 2 and 3 |
| `d1=d2=0` | 1 equals 3, with 2 distinct |

For all three orders `P2` and `E=P3-P2` are nonzero; in the strict
orders `P3` is nonzero as well. The lower vectors `P6,P7` are
linearly independent. Thus neither pair

\[
([0126],[0127]),\qquad([0236],[0237])
\]

can vanish simultaneously. In either strict order the same is true
of `([0136],[0137])`. Each follows from

\[
\operatorname{cross}(V,P_6)P_7-
\operatorname{cross}(V,P_7)P_6+
\operatorname{cross}(P_6,P_7)V=0
\]

for `V=P2,E,P3`. The companion checks every determinant factor and
this vector identity exactly. The rank clauses allow either sign for
the nonzero bracket; they exclude only simultaneous zeros.

As in the C1 boundary package, every actual bracket has positive and
negative trit bits, with neither bit meaning zero. Nonzero actual
brackets constrain the associated generic signs; zeros leave them
free. The source retains all necessary topology and linking clauses,
both strict axial separation cuts, affine cocycles, exact positive
interpolation at the collinear point, and weak Grassmann–Pluecker
relations. The five ordered lower-cap brackets are strictly positive
or strictly negative according to the case being considered.

## 2. Forty-nine uniform height relations

In the C0 gauge `P0=P1=0`, every actual bracket is a linear
combination of the fifteen anchor brackets `[01ij]`, because
`2[01ij]=cross(Pi,Pj)`. Its coefficients are affine functions of
`u,v`. The companion checks all 70 identities by direct determinant
expansion.

It omits the fifteen tautological anchor identities and the six
identities with a coefficient whose sign changes inside the height
square. The remaining 49 identities have coefficient signs fixed
throughout `0<u,v<1/2`. This is checked exactly at the four corners:
a nonzero affine function with one weak sign at all corners has that
strict sign at every interior point. No comparison between `u` and
`v` is needed.

Each resulting relation is encoded only by the necessary signed-sum
condition: either every term is zero or there are terms of both signs.
All magnitudes remain free. This is a relaxation of the exact
coordinate identities, and therefore safe for an UNSAT proof.

## 3. Six independently checked implications

The exported obligations are:

| Cases | Conclusion |
|---|---|
| All three upper orders; positive lower cap | Actual `[0127]<=0` and `[3456]<=0` |
| Either strict upper order; negative lower cap | Impossible |
| 1 strictly between 2 and 3; positive lower cap; actual `[2367]>0`, `[1267]<0`, `[0237]>=0` | Actual `[2345]<=0` and `[4567]<=0` |

There are three CNFs in the first row, two in the second, and one in
the last. Negations of conjunctions use actual positive trit bits,
so every claimed nonpositive sign includes zero. The final row keeps
`[0237]>=0` weak and does not require a positive upper cap area.

## 4. The metric turn when the upper angle is zero

For a positive lower cap the first row supplies the core sign used in
the [strict C0 turn proof](exhaustive_c0_turning.md). Its upper tip
angle is now `A=0`; the lower angle `B` remains in `(0,pi)`.
The half-angle argument still gives

\[
0<\gamma=B+\phi<\pi.
\]

The strict denominator comparison remains positive because
`d6,d7>0`; it does not need `d1,d2` both positive. The separate
zero-slack branch has `phi=0` and also gives `B<pi`.

The resulting exact determinant signs are

\[
[2367]>0,\qquad [1267]<0,\qquad [0237]\ge0.
\]

The third may vanish when `d0=0`, which is why the last Boolean
obligation uses a weak sign there.

For the order `d2=0<d1`, the final Boolean implication now gives both
mixed brackets nonpositive. Apply the
[metric height-order proof](remaining_c0_height_order.md). Its
positive coefficient inequality requires `b*=d0+d1+d7>0`, which
still holds. All norm and cosine-range factorizations allow `d2=0`;
the lower regular cap preserves the other positive denominators.
The clockwise three-angle path therefore contradicts `0<gamma<pi`
exactly as before. This excludes the positive lower-cap orientation.
The negative orientation was already excluded in Section 3.

## 5. Swapping the endpoint caps

The marked reflection `p(i)=1-i (mod 8)` exchanges the endpoint caps.
After intrinsic inversion and its exact integer vertex gauge,

\[
u'=1/2-v,\qquad v'=1/2-u,\qquad h'_i=h_{-i}.
\]

The companion checks both original marked cocycles, every horizontal
edge displacement, and the transformed intrinsic and spatial levels.
The new axis is old edge 10, whose limiting length is `1/2`.
Reanchoring is bounded and preserves collinearity and strict line
order within each equal-height cap.

The reflection preserves `u>=v`, and sends an old lower cap with
`d6=0<d7` to the already excluded upper order
`d2'=0<d1'`. A spatial reflection may be needed to restore the
finite anchor normalization. This is harmless because Section 4
excludes both orientations of the regular other cap; no sign of a
vanishing anchor is presumed.

## Reproduction and remaining cases

```sh
python research/type7_completion/exhaustive_c0_collinear.py /tmp/c0-collinear
python research/type7_completion/solver_cnf_certificates.py /tmp/c0-collinear-rup \
  --checker /tmp/type7-rup-check /tmp/c0-collinear
python research/type7_completion/solver_cnf_certificates.py /tmp/c0-collinear-rup \
  --checker /tmp/type7-rup-check --replay-only
python research/type7_completion/remaining_c0_height_order.py
```

The other strict collinear orders, coincident cap vertices, both
collinear caps, the `v>u` region, and height endpoints are not claimed
excluded here. The uniform positive-cap and negative-cap implications
in Section 3 remain available for those further analyses.
