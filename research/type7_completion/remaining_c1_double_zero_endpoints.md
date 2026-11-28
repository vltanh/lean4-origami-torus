# Three double-zero scalar C1 exclusions

For interior ray-2 C1, the following complete scalar families cannot
occur as limits of unbounded embedded sequences:

* EF with `eta=-1, epsilon=+1` in the
  [double-zero scalar classification](remaining_c1_zero_common.md);
* EE with `h0=0` and its two nonzero cap directions equal;
* EE with `h0=1/2` and its two nonzero cap directions equal.

All height parameters stay strictly between zero and one. The other
scalar EF and EE families remain separate. Five independently replayed
CNFs and the checked marked cap swap prove these exclusions without
comparing any degeneration rates.

## 1. Exact scalar source and normal stretch

Write `a=alpha`, `b=beta`, and use the scalar transverse coordinates
of the preceding classification. The EF family has

\[
\begin{aligned}
h&=(1/2,1/2,0,1/2,(1-b)/2,b/2,1/2,0),\\
P&=(0,0,p,p,p+1/2,bp+1/2,1/2,0),\qquad p=-1/(2a).
\end{aligned}
\]

The EE family at `h0=0` has

\[
h=(0,1/2,0,1/2,1/2,1/2,0,1/2),\qquad
P=(0,0,1/2,1/2,1,b/2,1/2,1/2).
\]

The companion imports these coordinates from the original scalar
classifier, which checks all twelve closed projected stresses from
the original 29-row system. In each family P3 is nonzero. Rotate the
finite transverse plane so that P3 lies on the scalar axis, with its
specified sign. If `delta=max_i |Yi|`, actual K4 nondegeneracy gives
`delta>0`, while the common-line limit gives `delta ->0`.

After dividing the normal coordinate by delta, the limiting normals
satisfy

\[
N_0=N_1=N_3=0,\qquad
\max(|N_2|,|N_4|,|N_5|,|N_6|,|N_7|)=1.
\]

Use the positive-determinant shear from the
[single-zero scalar proof](remaining_c1_single_zero_scalar.md) to
remove the denominator a. The transformed horizontal lists are

\[
\begin{aligned}
\mathrm{EF}:&(0,1,0,0,1,1,1,0),\\
\mathrm{EE}:&(0,0,1,1,2,b,1,1),
\end{aligned}
\]

and the axial levels are `(0,a,1,1,1,b,0,0)` in both cases.
No axial coordinate or error is divided by delta.

The source expands all seventy determinants and all 560 projected
Pluecker relations exactly. Uniform coefficient signs follow from
exact multilinear interpolation. Each nonzero actual determinant
fixes its original generic completion sign; zeros impose no sign.
Both strict height cuts and the entire embedding/linking source are
retained.

The EF normal-stretch formula is UNSAT, excluding that entire family.
For EE the first formula proves `N2=0`; the next step resolves its
shrinking edge at its own scale.

## 2. Every relative edge32 direction is impossible for EE

The relative short-edge theorem gives

\[
|P_2-P_3|/h_2\longrightarrow1,\qquad
\zeta_2-\zeta_3=O(t h_2),\qquad t=1/y^2.
\]

Set `rho=max(2h2,|Y2|/delta)`. If `rho/h2 -> infinity`, division of
the stretched edge32 by rho gives a virtual direction `(0,Y,0)`
with `Y!=0`. If that ratio stays bounded, division by `2h2` gives
`(1,Y,0)` or `(-1,Y,0)`: bounded stretched normal component implies
that the original physical normal component divided by h2 tends
to zero, so the unit-length limit fixes the horizontal component.
The axial component tends to zero in every case.

This exhaustive subsequential split compares no rates in advance.
The macro implication `N2=0` ensures that the two endpoints coincide
in the normal-stretched limit. Factor the actual edge column before
dividing each determinant that contains 23 by its chosen positive
scale. The companion checks all fifteen normalized forms in every
virtual direction, including a formal vanishing axial error.
Every coefficient has a uniform exact sign; none of these relations
is omitted. Each normalized bracket binds to the same original
generic sign, with zeros still free. No affine cocycle is imposed
between determinants normalized at different scales.

All three resulting formulas are UNSAT. They exclude the complete
EE left-endpoint family, even when h2 and delta vanish at unrelated
rates. The other short edge67 needs no normalization in this proof.

## 3. The marked cap swap covers the other EE endpoint

For EE at `h0=1/2` with equal cap directions, put

\[
p=-1/(2a),\qquad
P=(0,0,p,p,p+1/2,bp+(1-b)/2+1/2,1/2,1/2).
\]

Apply the checked marked permutation `i -> i+4 mod8`. It changes
the height parameters to `a'=1-b`, `b'=1-a`. Reanchoring its long
edge01, which is the old edge45, changes the limiting transverse
coordinates by the finite axial shear

\[
\lambda=\frac{P_5-P_4}{z_5-z_4}=-\frac{1+a}{a}.
\]

Reverse the scalar axis to orient the new lower cap positively.
The new scalar coordinates are exactly

\[
P'_i=-P_{i+4}+P_4+\lambda(z_{i+4}-z_4)
=(0,0,1/2,1/2,1,b'/2,1/2,1/2)_i.
\]

The weights become the EE `h0=0` weights. The companion verifies
all eight coordinate, height, and weight identities and the marked
symmetry against the original cocycle source. The new axis has a
nonzero limiting normalized length because `b<1`, so the reanchored
bounded chart is valid. Apply the preceding exclusion in that chart.
Its normal width is chosen anew; no comparison with the old width
is required.

## Reproduction and scope

```sh
python research/type7_completion/remaining_c1_double_zero_endpoints.py /tmp/type7-c1-double-endpoints
python research/type7_completion/solver_cnf_certificates.py /tmp/type7-c1-double-endpoints-rup \
  --checker /tmp/type7-rup-check /tmp/type7-c1-double-endpoints
```

All five CNFs require independent RUP replay. This proof excludes
the three named scalar families only. The opposite-direction EE
endpoints, the other EF scalar families, EA/EC, ray-2 C0, and
height boundaries retain their separate status.
