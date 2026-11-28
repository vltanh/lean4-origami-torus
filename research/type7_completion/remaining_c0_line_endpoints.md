# Closing the last endpoint-deficit line limits of C0

No unbounded embedded ray-1 sequence has an interior C0 common-line
limit with `h1=0` or `h7=0`. Together with the preceding
[normal-stretch exclusion](solver_remaining_c0_flat_stretch.md), this
closes all four closed endpoint-deficit families, including every
zero-edge endpoint.

The proof uses a relative metric estimate for the short edge and
three independently replayable CNFs. No ratio of its length, the
normal width, or inverse height is assumed.

## 1. The endpoint and its nontrivial normal stretch

Consider `h=h1 -> 0`. The classification gives

\[
P_0=P_1=P_2=P_4=P_6=0,\qquad
P_3=P_5=P_7=e/2,
\]
\[
z=(0,1/2,1/2,1/2,u,v,0,0),\qquad 0<u,v<1/2.
\]

Rotate each actual transverse plane so that `P7` is on the positive
horizontal axis. Write `P_i=(X_i,Y_i)` and
`delta=max_i |Y_i|`. Finite K4 nondegeneracy gives `delta>0`; the
common-line limit gives `delta -> 0`. Apply the positive affine map

\[
(X,Y,\zeta)\longmapsto(2X,Y/\delta,2\zeta).
\]

The resulting bounded limit has coordinates

\[
\begin{aligned}
r_0&=(0,0,0),&r_1=r_2&=(0,0,1),\\
r_3&=(1,N_3,1),&r_4&=(0,N_4,2u),\\
r_5&=(1,N_5,2v),&r_6&=(0,0,0),&r_7&=(1,0,0).
\end{aligned}
\tag{1}
\]

The facts `N2=N6=0` are conclusions of the published normal cover;
the first new CNF independently proves exactly their joint implication.
Moreover `max(|N3|,|N4|,|N5|)=1`, because the normal stretch is
nontrivial. Its source retains all actual zero determinants.

## 2. Only two short-edge directions remain after stretching

The [relative short-edge lemma](remaining_c0_short_edges.md) gives

\[
|P_2|/h\longrightarrow1,\qquad
\zeta_2-\zeta_1=O(th),\qquad t=1/y^2.
\tag{2}
\]

Its exact core and cap polarizations also show that every limiting
unit vector `w=lim P2/h` has `w_x<=0`. Indeed
`d0/h,d2/h -> (1+w_x)/2` and `d0+d2<=h`.

In the stretched coordinates, use the actual positive scale

\[
\rho=\max(2h,|Y_2|/\delta).
\]

Pass to a subsequence. If `rho/h -> infinity`, divide the actual
edge 12 by `rho`. Its horizontal coordinate tends to zero; its
normal coordinate tends to `+1` or `-1`. Its axial coordinate is
`O(th/rho) -> 0`. The virtual direction is therefore

\[
(0,Y,0),\qquad Y\ne0.
\tag{3}
\]

Otherwise `rho/h` is bounded. Divide edge 12 by `2h`. Its normal
coordinate remains bounded, so `Y2/h=O(delta) -> 0`. By (2), the
physical unit direction is parallel to the horizontal axis. The
inequality `w_x<=0` selects `w_x=-1`. Its axial coordinate again
tends to zero, giving the second possibility

\[
(-1,Y,0),\qquad Y\in\mathbb R.
\tag{4}
\]

These two cases exhaust every subsequential scale behavior. In
particular no axial error has been divided by `delta`.

## 3. Both virtual directions contradict the same generic source

For every four-point bracket containing vertices 1 and 2, factor
the actual edge 12 before dividing by its chosen positive scale.
The other three columns converge to (1), so its limit is obtained
by replacing that short column with (3) or (4).

All fifteen normalized determinants are linear in
`N3,N4,N5,Y`. Their coefficients are multiaffine in `2u,2v`.
The checker expands each determinant directly and verifies every
coefficient sign by exact corner interpolation on the open unit
square. No relation is omitted.

Each normalized determinant has its own actual positive/negative
trit, linked to the same original generic completion as the unscaled
bracket. A zero normalized determinant leaves that generic sign
free. The original normal-stretch source retains its exact macro
relations and projected identities; no affine cocycle is imposed
between differently normalized determinants.

For (3), add only the nonzero condition `Y != 0`. For (4), the
horizontal coordinate already makes the direction nonzero. Both
resulting finite formulas are UNSAT, with independently replayable
RUP certificates. This excludes every possible actual sequence at
the `h1=0` endpoint.

## 4. Reflection and remaining scope

The checked marked reflection `p(i)=1-i mod 8` exchanges `h1` and
`h7`, preserves the open C0 height square, and carries the remaining
endpoint to the one proved above. Normalize the ambient orientation
as usual after reflection. Thus `h7=0` is excluded too.

The two earlier zero-edge endpoints `h2=0,h6=0` and all four open
endpoint-deficit intervals were already excluded. After the
[nonflat circle exclusion](exhaustive_c0_circle.md), the only common-line
cap families still requiring an argument are the four middle-deficit
line families and the two diagonal line directions.

```sh
python research/type7_completion/remaining_c0_line_endpoints.py /tmp/c0-line-endpoints
python research/type7_completion/solver_cnf_certificates.py /tmp/c0-line-endpoints-rup \
  --checker /tmp/type7-rup-check /tmp/c0-line-endpoints
```

All three CNFs require independent replay. The source checker also
replays the relative metric identities, the exact endpoint cap/core
identities, the original twelve closed stresses, and the marked
reflection.
