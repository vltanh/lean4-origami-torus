# Excluding all four scalar EB/ED families

The [common-line reduction](remaining_c1_single_zero_common.md) leaves
exactly four scalar families for the two remaining single-zero C1
orders. Two admit no nontrivial normal stretch directly. For the
other two, a separate normalization of the shrinking edge 23 gives
the contradiction. Thus **both complete interior EB and ED orbits
are excluded**, including all relative collapse rates.

## 1. Complete scalar classification

Orient the common line so that the lower unit direction is positive.
Write `P_i` for the scalar transverse coordinate and use
`a=alpha`, `b=beta`, with both strictly between zero and one.
Every family has

\[
P_0=P_1=0,\quad P_2=P_3=p,\quad P_4=p+\epsilon/2,
\qquad h_1=h_3=1/2,\quad h_2=0.
\]

For EB, `0<ell<1/2`, `P6=1/2-ell`, `P7=1/2`, and
`(h6,h7)=(ell,1/2)`. For ED, `0<k<1/2`, `P6=1/2`,
`P7=k`, and `(h6,h7)=(1/2-k,k)`.

| Family | `h0` | `epsilon` | `h4` | `h5` | `p` | `P5` |
|---|---|---|---|---|---|---|
| EB | `0` | `+1` | `1/2` | `1/2-ell` | `1/2` | `b/2` |
| ED positive anchor | `1/2-k` | `-1` | `1/2` | `k` | `[1/2-(1-a)k]/a` | `bp+(1-b)(1/2+k)` |
| ED negative anchor, opposite direction | `1/2` | `-1` | `0` | `1/2` | `-1/(2a)` | `b(p-1/2)` |
| ED negative anchor, same direction | `1/2` | `+1` | `(1-b)(1/2-k)` | `1/2-(1-b)(1/2-k)` | `-1/(2a)` | `bp+1/2+(1-b)k` |

Here is the finite completeness argument. The common-line theorem
already supplies the three possible first-circle anchor cases.
Apply the exact four-case scalar table from
[the positive-edge proof](remaining_c1_flat_positive_stretch.md#1-four-scalar-possibilities-for-a-linked-pair)
to the second linked pair, whose upper edge is `h3=1/2` and whose
lower edge is `0<h6<1/2`. Neither its exceptional half/half case
nor its zero-radius case is possible. This gives four choices per
anchor, twelve in total.

The ray-2 weight budget requires `h4+h5` to equal respectively
`1-ell`, `1/2+k`, or `1/2` in the three anchor cases.
Eight choices have a uniformly strict nonzero budget difference;
exact substitution leaves precisely the four displayed rows.
The companion records all twelve choices and their exact budget
differences. Every surviving row additionally satisfies all twelve
closed projected stresses from the original 29-row system.

The cap-order endpoints are not omitted from the overall zero-edge
cover: `k,ell=0,1/2` have one of the already listed C, E, or F
orders. This package treats the strict B and D orders only.

## 2. Nontrivial normal stretch

Each displayed p is nonzero. Rotate each finite transverse plane
so that P3 lies on the scalar axis, with the sign of p. If its
normal width is

\[
\delta=\max_{i\in\{2,4,5,6,7\}}|Y_i|,
\]

finite K4 nondegeneracy gives `delta>0`. The common-line limit gives
`delta ->0`. After a subsequence, divide the normal coordinate by
delta to obtain

\[
N_0=N_1=N_3=0,\qquad
\max_{i\in\{2,4,5,6,7\}}|N_i|=1.
\]

The axial coordinate is normalized by height, independently of
delta, exactly as in the earlier normal-stretch proofs. No axial
error is divided by the normal width.

An additional positive-determinant shear removes the a denominators.
If `p=c/a+d`, its transformed scalar coordinate is
`x_i=2P_i-2c z_i/a`, where
`z=(0,a,1,1,1,b,0,0)`. The map from physical normalized coordinates
has determinant four. For the two excluded rows the horizontal lists
are

\[
\begin{aligned}
\text{ED positive: }&
(0,2k-1,2k,2k,2k-1,-b+2k+1,1,2k),\\
\text{ED negative same: }&
(0,1,0,0,1,1+2(1-b)k,1,2k).
\end{aligned}
\]

The checker derives these lists from the scalar source rather than
treating them as independent input.

## 3. Two exact sign contradictions

The companion expands all seventy four-point determinants in the
five normal variables and all 560 projected Pluecker identities.
It checks every coefficient sign by exact multilinear interpolation
in `a,b,k`. Each actual nonzero determinant binds to its original
generic completion; actual zeros leave that sign free. The source
retains both strict axial cuts and the complete embedding/linking
formula. At least one normal trit is nonzero.

The resulting formulas are UNSAT for both displayed ED rows. The
positive-anchor formula omits no relation; the negative-same formula
omits 113 relations whose coefficients do not have uniform signs.
Omitting a relation weakens the necessary system, so the checked
contradiction remains valid throughout the whole parameter interval.
Both CNFs require independent RUP replay.

The conclusion excludes these two entire scalar families at every
interior height and every relative collapse rate. It does not merely
exclude selected values of k or nonzero limiting orientation minors.

## 4. Relative normalization closes the other two families

The two families requiring the relative step are

\[
\begin{aligned}
\text{EB: }&P=(0,0,1/2,1/2,1,b/2,1/2-\ell,1/2),\\
\text{ED opposite: }&
P=(0,0,p,p,p-1/2,b(p-1/2),1/2,k),\quad p=-1/(2a).
\end{aligned}
\]

For each, an independently replayed macro-normal implication forces
`N2=0`. Consequently vertices 2 and 3 coincide in the stretched
limit, while at least one of the other normal coordinates is nonzero.
The [relative short-edge lemma](remaining_c1_short_edges.md) gives

\[
|P_2-P_3|/h_2\longrightarrow1,\qquad
\zeta_2-\zeta_3=O(t h_2),\quad t=1/y^2.
\]

The shear in Section 2 changes the first normalized edge coordinate
by only `O(t h2)`, and leaves its normal coordinate unchanged.
In the stretched chart put

\[
\rho=\max(2h_2,|Y_2|/\delta).
\]

If `rho/h2` tends to infinity, divide edge 32 by rho. Its horizontal
and axial coordinates tend to zero, while its normal coordinate
tends to `+1` or `-1`. Its virtual direction has form `(0,Y,0)`
with `Y!=0`.

Otherwise `rho/h2` is bounded. Divide by `2h2`. The normal coordinate
stays bounded, and the original physical normal edge component
divided by h2 tends to zero because delta tends to zero. The unit
norm therefore makes the horizontal coordinate tend to `+1` or
`-1`. The normalized axial coordinate is `O(t)`. These two virtual
directions have form `(1,Y,0)` or `(-1,Y,0)`, with arbitrary bounded Y.
After taking subsequences these three possibilities cover every scale
behavior. No ratio involving delta, h2, or t is prescribed.

For each virtual direction, the checker inserts an independent formal
edge column at vertex 2 relative to vertex 3, including a formal
vanishing axial error. It factors this edge before dividing each of
the fifteen determinants containing 23. Their limiting forms are
linear in the five macro normals and Y, with exactly checked uniform
coefficient signs. **No virtual relation is omitted.** Each nonzero
normalized determinant binds to the same generic sign as its original
unscaled determinant. No affine cocycle is added between the two scales.

All six virtual-direction formulas are UNSAT. Together with the two
macro implications `N2=0` and the two direct exclusions, this gives
ten independently replayable CNFs and excludes all four scalar families.
The other zero-edge orbits and height boundaries retain their separate
status; this proof closes the entire EB and ED interior strata only.

```sh
python research/type7_completion/remaining_c1_single_zero_scalar.py /tmp/type7-c1-single-scalar
python research/type7_completion/solver_cnf_certificates.py /tmp/type7-c1-single-scalar-rup \
  --checker /tmp/type7-rup-check /tmp/type7-c1-single-scalar
```
