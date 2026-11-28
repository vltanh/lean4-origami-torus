# The nonedge15 cut excludes the negative-axial endpoint

At the canonical marking-1 mask-04 endpoint, the existing nonedge15
distance bound implies

\[
 \boxed{b_1\ge-o(h_1)}.                                  \tag{1}
\]

Consequently the negative-axial regime `d2/h1→1`, for which
`b1/h1→-1`, is impossible. This argument uses no oriented-matroid case
enumeration. It also excludes every subsequential limit
`b1/h1→-r` with `r>0`.

## Exact identity

Write `h=h1`, `di=1/2-hi` for `i≠1`, and

\[
 R=d_0+d_5+d_6+d_7,\qquad 0\le R\le h.
\]

The intrinsic horizontal coordinates are

\[
 x_1=-1/2+d_0,\quad x_2=1/2+d_0-h,\quad
 x_5=1/2-d_5-d_6-d_7.
\]

Use the already-required nonedge15 translate `(-1,1)`, and denote its
components by `X15,V15`. Edge25 has the same translate. Thus

\[
 X15=1/2-R,\quad X25=-1/2+h-R,\quad
 V15=v_5-v_1+1,\quad V25=V15-b_1.                       \tag{2}
\]

In axis-01 coordinates let the actual displacement12 be

\[
 (P_{2x},Z_2,b_1+t\lambda),
\]

where the last coordinate is spatial axial distance divided by `y`.
The exact anchor polarization from `remaining_ray1_endpoint.md` gives
`λ=O(h)` after its already-proved bound `b1=O(h)`.
Let `E15` be actual squared distance15 divided by `y²`, minus the
squared length of the translate in(2). The required nonedge inequality
is `E15≤0`.

Subtracting the exact metric equations for12 and25 gives

\[
\begin{aligned}
 E15={}&t\{h^2-(1-h)(h-2R)\}+2b_1^2-2V15\,b_1\\
 &+2t\{(P_{5x}-P_{2x})P_{2x}+(Z_5-Z_2)Z_2\}\\
 &+2(\zeta_5-\zeta_2)(b_1+t\lambda).                    \tag{3}
\end{aligned}
\]

The program checks(3) as a polynomial identity. It also checks the
archived edge25 translate and the exact horizontal expressions(2).

## Uniform endpoint limit

The bounded axis compactification and the endpoint anchor estimates give

\[
 P_{2x},Z_2=O(h),\quad b_1=O(h),\quad\lambda=O(h),
 \qquad V15\to1/2,\quad\zeta_5-\zeta_2\to-1/2.
\]

The coordinates of vertex5 stay bounded. Since `0≤R≤h`, the first
term in(3) is `O(th)`. The transverse dot term is also `O(th)`, and
the remaining quadratic or axial-correction errors are
`O(h²)+O(th)`. Therefore(3) has the uniform form

\[
 E15=-2b_1+o(h).                                        \tag{4}
\]

In particular there is no error independent of `h`, even if `t/h` or
the transverse-width ratio is unbounded. Combining `E15≤0` with(4)
proves(1). In the negative-axial regime, equation(4) gives
`E15/h→2`, directly contradicting the nonedge bound.

The nonedge inequality was already part of the necessary embedding
system: Euclidean chord length is at most the intrinsic flat-torus
distance, and hence at most the length of any chosen lattice translate.
This proof does not introduce a stronger geometric assumption.

## Replay and remaining scope

```bash
python research/type7_completion/remaining_ray1_nonedge.py
```

The replay uses exact rational symbolic arithmetic and needs no SAT,
linear-programming, or nonlinear solver. Together with
`remaining_ray1_negative_x.md`, this excludes two of the three endpoint
regimes. The [positive-axial proof](remaining_ray1_positive_z.md)
excludes the last regime `d0/h1→1` and completes this two-block limit.
