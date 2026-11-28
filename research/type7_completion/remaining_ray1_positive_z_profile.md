# The first-width profile in the positive-axial endpoint

This is the profile lemma used by `remaining_ray1_positive_z.md`.
It proves that its positive-axial regime has

\[
 (Z_5,Z_6,Z_7)/\delta\longrightarrow(-1,0,-1).             \tag{1}
\]

The hypotheses already established by the relative face027 Gram
factorization are

\[
 S=h-d_0=o(\delta^2h),\qquad W_1=o(\delta h),
\]

where `h=h1`, `S=sum(d2,...,d7)`, and `W1` is distance to the actual
face027 plane. The planar projection of vertex1 in that gauge is

\[
 (h_0+\sigma,\ y(v_1+tq)),\qquad \sigma,q=O(hS).
\]

The published virtual12 consequence `aY=0` and the exact Gram
factorization justify these estimates uniformly in every collapsing
edge and phase. This lemma assumes them explicitly and adds no rate
comparison.

## 1. The plane change preserves the first normal scale

In the original axis-01 coordinates, a normal to actual face027 has
the linear numerator

\[
 Z-aP_x-b\zeta,
\quad
 a=\frac{Z_7\zeta_2-Z_2\zeta_7}{P_{7x}\zeta_2-P_{2x}\zeta_7},
\quad
 b=\frac{P_{7x}Z_2-P_{2x}Z_7}{P_{7x}\zeta_2-P_{2x}\zeta_7}.
\]

The denominator tends to `1/4`. The positive-axial estimates
`P2x=o(h)` and `Z2=o(δh)` give `a=O(δ)` and `b=o(δh)`.
The unit-normal factor is `sqrt(1+a²+t b²)=1+o(1)`.
All planar coordinates remain bounded, so every new normal `Wi` is
`O(δ)`. Since `P6x,ζ6→0`, the normal of vertex6 satisfies

\[
 W_6/\delta-Z_6/\delta\longrightarrow0.                  \tag{2}
\]

## 2. Two uniformly independent polarizations bound vertex6

Put `u=v6` and `r=d6+d7≤S`. In face027 coordinates write vertex6 as

\[
 (U_6,\ y(u+t\lambda_6),\ W_6).
\]

This is a definition of `λ6`, not an assumption that it is bounded.
Polarizing the original metric triangles016 and067 gives exactly

\[
 (h_0+\sigma)U_6+(v_1+tq)\lambda_6
   =h_0r-qu-W_1W_6,                                    \tag{3}
\]

\[
 h_7U_6+v_7\lambda_6
   =\frac{r^2+h_7^2-h_6^2}{2}.                         \tag{4}
\]

Their coefficient determinant tends to `-1/4`. The second right side
is `O(S)`; the first is `O(S+|W1 W6|)`, because `q=O(hS)` and `u`
is bounded. Since `W6=O(δ)` from the plane change,

\[
 U_6,\lambda_6
 =O(S+|W_1W_6|)=o(\delta^2h).                          \tag{5}
\]

This establishes the axial bound from a nonsingular exact linear
system, so it remains valid even if a folded correction initially
appeared unbounded.

The restored norm equation06 is

\[
 W_6^2=r^2-U_6^2-2u\lambda_6-t\lambda_6^2.
\]

Using `r≤S`, `u→0`, and(5), its nonnegative left side is
`o(δ²)`. Hence `W6=o(δ)`; equation(2) proves `d=Z6/δ→0`.

## 3. Exact finite cone implications finish the profile

The published virtual12 packet leaves172 positive-axial primary sign
words in five distinct linear cones. In each cone the companion adds
the two nonnegative rows `d` and `-d`, expressing the metric conclusion
`d=0`, and certifies all three implications

\[
 c-e\ge0,\qquad e-c\ge0,\qquad -c\ge0.
\]

The fifteen certificates are nonnegative rational combinations of the
reconstructed cone rows. Each replay checks every coefficient exactly;
an LP is used only by the optional producer. Thus `c=e≤0` follows for
every surviving word, including every cone boundary.

The first-width normalization is `max(|c|,|d|,|e|)=1`. With `d=0`, it
forces `c=e=-1`, proving(1). The exact nonzero macro and virtual signs
of this fixed profile leave100 primary words. No separate enumeration
is needed for the metric stress argument using(1).

## Replay

```bash
python research/type7_completion/remaining_ray1_positive_z_profile.py
```

The replay first binds the freshly enumerated331 endpoint words and
rechecks all426 original virtual12 certificates and17 prior consequence
certificates. It then checks the fifteen new profile implications and
the exact geometric identities(2)--(4). The optional reproducible
certificate producer is

```bash
python research/type7_completion/remaining_ray1_positive_z_profile.py \
  --produce /tmp/positive_z_profile.json
```
