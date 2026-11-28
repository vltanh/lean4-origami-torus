# Ray 1: complete exclusion of the two-block limit

There is no unbounded sequence of marking-1 realizations whose cyclic
vertical steps converge, up to the verified marked symmetries, to

\[
(b_0,\ldots,b_7)=(1/2,0,0,0,1/2,0,0).
\]

The proof covers every horizontal degeneration and every relative rate
of the height parameter, transverse width, and collapsed edges. It is a
research theorem on this asymptotic limit, with no explicit numerical
threshold. Other ray-1 limits and ray 2 remain open; this theorem alone
does not close the finite `y=10^6` mask ledger or provide a Lean proof.

## Complete reduction and the three final contradictions

The [common-line theorem](remaining_ray1_mask04.md) first puts all eight
projected vertices on one common line. It includes both noncollinear
caps, a collinear triple, one flat cap, two nonparallel flat caps, and
all chain endpoints. Its 52 Boolean obligations have independent RUP
proofs.

The [first transverse stretch](remaining_ray1_mask04_blowup.md) covers
all 24 closed horizontal-order cases, preserving zero horizontal
edges. Twenty are excluded. The other four have one of
`h1,h3,h5,h7` tending to zero and every other horizontal weight tending
to `1/2`. The checked marked symmetries reduce them to `h=h1->0`.

At that endpoint, the [uniform anchor identities](remaining_ray1_endpoint.md)
and a four-edge polarization prove `b1=O(h)`. The exact virtual-direction
cover then leaves three normalized deficit regimes. Each is now excluded:

| Regime | Final obstruction |
|---|---|
| `d0/h,d2/h -> 0` | The [negative-X proof](remaining_ray1_negative_x.md) forces virtual edges14 and24 onto the same positive ray. Their common scale dominates `h`. Subtracting two exact face polarizations then makes the same quantity tend to both `1` and `1/2`. |
| `d2/h -> 1` | The [nonedge15 cut](remaining_ray1_nonedge.md) gives `b1>=-o(h)`, contradicting `b1/h->-1`. Its error is relative to `h`, with no independent `t` remainder. |
| `d0/h -> 1` | The [positive-axial proof](remaining_ray1_positive_z.md) gives `S=h-d0=o(delta^2*h)`. Its exact profile lemma forces normal profile `(-1,0,-1)`. A rank-one metric identity on clique3456 gives `delta^2<=128*S`, a contradiction. |

The nonedge15 cut also excludes every intermediate negative limit of
`b1/h`. The earlier interval-polynomial certificates remain valid, but
that additional geometric cut supplies a direct exclusion of their
negative-axial range.

## Why the last estimate is uniform

In the actual face027 plane, the squared normal distance of vertex1
factors exactly as `d0*(h-d0)` times a coefficient tending uniformly to
four. The factorization keeps the ratio `d7/(h-d0)` in its entire closed
unit interval. No additive small-height error survives when the
deficits become extremely small.

The last metric identity uses coefficients `(A,B,-A,-B)` on3456, where
`A=v4-v6-1` and `B=-(v3-v5-1)`. Their sum and weighted intrinsic
vertical lift both vanish. Consequently the squared norm of their
weighted spatial sum is exactly a horizontal polynomial of size
`O(d3+d4+d5)`. The forced profile gives that same spatial sum a normal
component asymptotic to `-delta/2`. This is a contradiction for every
relative collapse rate, without a nearby-solution parametrization.

## Verification and remaining scope

The endpoint's complete 331-sign source and six first-width obligations
passed fresh independent replay in 2.445 seconds; proof-only replay took
0.435 seconds. The virtual package checks 426 exact Farkas certificates,
including 102 certificates uniform on an open parameter interval.
Seventeen further implication identities refine its surviving cones,
and fifteen more prove the final positive-axial profile. All are exact
rational identities whose source signs are bound to the independently
checked finite cover.

The final metric identities are independently reproducible with

```sh
python research/type7_completion/remaining_ray1_negative_x.py
python research/type7_completion/remaining_ray1_nonedge.py
python research/type7_completion/remaining_ray1_positive_z.py
```

The positive-axial command replays the original virtual certificates and
both implication packages before checking the final metric stress.
The earlier common-line and first-stretch proof maps give their separate
producer and independent replay commands.

By the usual sequential contradiction argument, the excluded phase has
some neighborhood and some finite height beyond which no realization
occurs in that neighborhood. Neither constant is numerical here. This
does not identify the neighborhood with one of the finite-target masks.
