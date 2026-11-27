# Every unbounded ray-3 sequence has a degenerate projected cap limit

**Theorem.** Let an actual canonical ray-3 realization exist along a
sequence `y -> infinity`. Normalize the longitudinal axis to `02` as in
[relative_cap_bounds.md](relative_cap_bounds.md). In every convergent
subsequence of the bounded transverse vertex coordinates, at least one
of the caps `0145`, `2367` has a collinear triple.

This covers all limiting shapes with two nondegenerate caps, not merely
a prescribed construction. It does **not** exclude a degenerate cap,
give a finite-height threshold, or close `ray3_phase0`. The geometric
necessity premises are those in [geometric_audit.md](geometric_audit.md).

## 1. A scalar identity from all cross distances

Let `e_i`, `f_j` be the cyclic spatial short-edge vectors of the two
caps. Write their positive intrinsic horizontal lengths as `h_i`, `k_j`,
and their rescaled vertical displacements as `gamma_i`, `delta_j`.
Put `t=1/y^2`. Four-point polarization of the sixteen cross distances
gives the exact stress matrix

\[
R_{ij}=h_i k_j+t\gamma_i\delta_j-e_i\cdot f_j.
\]

All sixteen entries are affine in the fourteen intrinsic coordinates:
their quadratic terms cancel. The archived cocycle gives

\[
\sum_{ij}M_{ij}R_{ij}=\tfrac12,\qquad
\sum_{ij}R_{ij}=1,\qquad
M=\begin{pmatrix}1&0&1&1\\1&0&0&0\\1&1&1&0\\0&0&1&0\end{pmatrix}.
\]

The relative bounds give `|gamma_i| < (1/2+t)h_i`, and likewise for the
other cap. Spatial axial components tend to zero. Therefore in a
transverse limit, `|e_i|=h_i`, `|f_j|=k_j`, both perimeters are one, and

\[
2\sum M_{ij}\bigl(|e_i||f_j|-e_i\cdot f_j\bigr)=1. \tag{1}
\]

No division by a cap edge is used in taking this limit.

## 2. The only possible nondegenerate shapes are aligned trapezoids

Suppose all four triples of each limiting cap are noncollinear. All
eight edges are then nonzero. A determinant containing three vertices
of one cap and one of the other has a fixed nonzero limiting sign,
independent of the opposite vertex. Pass to a subsequence on which the
generic orientation completion is fixed. It belongs to the same
**sixteen models** used in the exact two-cap theorem.

The eight consecutive-edge planar cross products have their strict
prescribed signs. The sixteen cross products between caps have their
prescribed signs weakly: a zero limiting cross product is allowed.
Write each direction as a signed positive multiple of a line direction
in a common half-open interval of length pi. Every prescribed sign
becomes a weak order comparison of line angles. Consecutive-edge
comparisons are strict.

Exhaustively checking the sixteen models and 128 direction-sign
choices leaves **112 weak order patterns**. In each, a strongly
connected component forces either edges `0,2,4,6` or edges `1,3,5,7`
to have the same line direction. The two edges in either cap have
opposite signs along this line. All four cyclic turns in each cap,
and in both caps together, have the same sign. Thus both caps are
strictly convex trapezoids with their two bases parallel to one common
line.

The exact marked symmetry `(0,5,2,7,4,1,6,3)` exchanges the two parity
choices. Its lattice map is `(m,n) -> (-m-n,n)`, with vertex gauge
`g_4=(1,0)` and all other gauges zero. Reversing both cap edge orders
replaces `M` by `1-M`, so equation (1) is preserved.

Choose the odd edges as bases. Rotate and, if necessary, reflect the
transverse plane. Independently scale the two caps by positive numbers
so their leg heights become one. Equation (1), written homogeneously
with the product of the two perimeters on its right side, is invariant
under these independent scalings. The edge vectors become

\[
\begin{aligned}
e&=((X,-1),(L,0),(A-L-X,1),(-A,0)),\\
f&=\sigma((U,-1),(M,0),(C-M-U,1),(-C,0)),
\end{aligned}
\]

where `A,L,C,M>0` and `sigma` is `+1` or `-1`.
The sign conditions are also invariant under these scalings: a 3+1
bracket scales by the square of the relevant cap scale, and a 2+2
bracket by the product of the scales.

The full weak signs of all seventy brackets now force

\[
U-X\le -A-M\quad(\sigma=1),\qquad
U-X\ge C+L\quad(\sigma=-1). \tag{2}
\]

This last finite check is linear. A common horizontal shear used only
for evaluating signs makes `X=0` and replaces `U` by `U-X`.
Including both global orientations, four of the sixteen original models
survive for each value of `sigma`. Every remaining bracket inequality
is the indicated inequality (2) plus a nonnegative sum of base lengths,
or is already a positive base length.

## 3. The stress inequality is strictly incompatible with these signs

Let `P_A=sum |e_i|`, `P_B=sum |f_j|`, and set

\[
F=2\sum M_{ij}(|e_i||f_j|-e_i\cdot f_j)-P_A P_B.
\]

The metric identity requires `F=0`. The vertical contributions to the
masked dot-product sum cancel, so only horizontal components enter
that sum. Replace the four leg lengths by their absolute horizontal
components, obtaining a quadratic expression `F_0`.

**Exact finite inequality:** `F_0>=0` whenever the positive bases and
(2) hold. The verifier checks this as follows. Introduce `g>=0` and
substitute `U=X-A-M-g` or `U=X+C+L+g`, respectively. Choose all sixteen
signs of `X`, `A-L-X`, `U`, `C-M-U`. Each choice makes `F_0` an exact
quadratic polynomial on a rational polyhedral cone in
`(A,L,C,M,X,g)`. Including both orientations gives 32 cones.

Each cone is pointed: its nine inequality rows have rank six, so its
lineality space is zero. Every extreme ray therefore has five linearly
independent active inequalities. The verifier enumerates every such
five-row subset, retains both signs of its one-dimensional kernel when
feasible, and removes duplicates. This covers even lower-dimensional
cones; a cone without rays is `{0}`. Each cone has at most eight rays.
For its symmetric quadratic matrix `Q`, the verifier checks exactly
that `r^T Q s>=0` for every pair of its rational extreme rays. Every
point of a pointed polyhedral cone is a nonnegative combination of its
extreme rays, proving the inequality on the whole cone, including its
boundary.

Finally let `dh,dj,dk,dl` be the positive excesses of the actual four
leg lengths over those horizontal projections. Expanding `F-F_0`
gives four linear terms with nonnegative coefficients, plus

\[
(dh+dj)(dk+dl)>0.
\]

The coefficients are nonnegative because
`|X|+|A-L-X|>=|A-L|` and
`|U|+|C-M-U|>=|C-M|`. The excesses are strictly positive because the
leg heights are one. Consequently `F>F_0>=0`, contradicting `F=0`.
This proves the theorem.

## Reproduction and scope

```sh
python3 research/type7_completion/verify_cap_limit.py /tmp/type7-cap-limit.cnf
g++ -O3 -std=c++17 research/orientation_checkpoint/check_unsat.cpp -o /tmp/type7-cap-check
/tmp/type7-cap-check < /tmp/type7-cap-limit.cnf
```

The symbolic stress identity, weak-order enumeration, trapezoid signs,
and rational cone inequalities use no floating-point arithmetic.
The separate C++ exhaustive replay certifies completeness of the
sixteen sign models; require its explicit `UNSAT` output.

This removes all two-nondegenerate-cap limits from an unbounded
ray-3 sequence. Collinear triples, coincident limiting vertices,
unequal collapse rates, and finite-height realizations remain.
There is still no exclusion among the fifteen full ray-1/2/3 systems.
