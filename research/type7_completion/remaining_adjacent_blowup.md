# Ray 3: one collapsed edge in the collinear blown-up cap

## Result and exact coverage

In a common-line ray-3 limit, consider a first normal blow-up with one
collinear cap A and one noncollinear cap B. There is no such sequence
with exactly one zero limiting A weight and all four limiting B weights
positive. The proof allows arbitrary relative rates of the collapsed
edge, the normal width, and `t=1/y²`.

The complete degenerate-norm cover contains 64 cells with one adjacent
A pair coincident. Exactly 48 have no zero B weight. The verifier
`remaining_adjacent_blowup.py` maps all 48 by checked marked symmetries
and coordinate reflections to

```
A=(0,0), (r,0), (r,0), (1/2,0),
B=(0,0), (-chi,0), (0,0), (-sigma,1),
0<r<1/2, chi>0, sigma>0, chi+sigma=1/2.
```

The cyclic labels are `A=(0,1,4,5)` and `B=(2,3,6,7)`. The collapsed
edge is 14. The other 16 cells have two zero B weights; their canonical
boundary has `sigma=0`, so B7 is vertical in the blown-up picture.
Those 16 cells are recorded separately and are **not excluded here**.

This is an asymptotic research theorem under the existing geometric
necessity audit. It is not a fixed-modulus exclusion or a Lean theorem.

## 1. Four necessary weak signs

The nonzero mixed brackets of the displayed limiting picture imply,
through the complete orientation and linking formula,

\[
 [0124]\leq0,\qquad [1247]\geq0,\qquad
 [1467]\geq0,\qquad [0145]\leq0.                \tag{1}
\]

The verifier fixes only those nonzero limiting brackets and leaves
all others free. It allows either global orientation. The CNF stating
that at least one of (1) fails is UNSAT. Thus (1) holds for every
necessary generic completion, including zero actual brackets.

## 2. Normalize the collapsed edge at its own stretched scale

Let `b=r4-r1` and let `beta=h14>0` be its intrinsic horizontal length.
Let delta be the positive normal coordinate of B7 in the normalized
profile, so delta tends to zero. The other blown-up normal coordinates
converge to zero. Write the stretched transverse coordinates as
`(X,Y/delta)`.

For precision, these may be obtained from the face-023 incidence chart
`(U,Y,H)`, `H_i=c_i-2t*zeta_i`, by the genuine affine shear and scaling

\[
 X_i=U_i-\frac{x_2}{H_2}H_i,\qquad
 \widetilde H_i=H_i/H_2.
\]

Here `H2→1`; the transverse coordinates of anchors 0 and 2 are zero.
The uniform short-edge bounds give

\[
 |\Delta\zeta_{14}|=O(\beta),\quad
 \Delta H_{14}=O(t\beta),\quad
 (\Delta X_{14})^2+(\Delta Y_{14})^2
       =\beta^2(1+O(t)),                         \tag{2}
\]

with constants independent of beta. The last identity follows from the
exact edge metric, the relative gamma/zeta bounds, and
`Delta X-Delta U=O(t beta)`.

Normalize b by

\[
 m=\max(|\Delta X_{14}|,|\Delta Y_{14}|/\delta).
\]

Equation (2) gives `m≥c beta` for one fixed positive c along the
sequence. Pass to a subsequence where its stretched transverse
direction tends to `(v_x,v_y)`, with maximum absolute coordinate one.
Its normalized axial coordinate is `O(t beta/m)→0`. This virtual
direction is nonzero without any comparison of beta and delta.

Every bracket used next contains the actual edge 14. Subtracting its
endpoints factors that edge as a determinant row. After division by m
in the stretched chart, the three leading forms are exactly

\[
 [0124]/m\to-rv_y,\qquad
 [1247]/m\to v_x+\sigma v_y,\qquad
 [1467]/m\to-v_x-\sigma v_y.                    \tag{3}
\]

The common positive factor from stretching is implicit in (3) and
does not affect signs. The verifier checks all three determinant
identities symbolically. The other rows merely converge to their
bounded anchors; their errors are little-o of m after the edge is
factored. They need not converge faster than beta or delta.

Combining (1) and (3) gives

\[
 v_y\geq0,\qquad v_x+\sigma v_y=0.
\]

Because the virtual direction is nonzero and sigma is positive,
`v_y>0` and `v_x<0`. Returning to (2),

\[
 \beta/m\longrightarrow |v_x|>0,
 \qquad
 \Delta X_{14}/\beta\to-1,
 \qquad
 \Delta Y_{14}/(\delta\beta)\to1/\sigma.        \tag{4}
\]

Thus the needed comparison of stretched and physical edge scales has
been proved from the signs; it has not been assumed.

## 3. The intrinsic and height limits are uniquely forced

Put

\[
 b_0=2\chi r+\chi-r,\qquad
 g_0=-\chi r+\chi/2+r/2-1/8.
\]

The limiting short weights are

```
A: (r,0,1/2-r,1/2),   B: (chi,chi,sigma,sigma).
```

The sixteen limiting cross stresses, together with these eight
horizontal-weight equations, give a `24×14` affine system in all
fourteen intrinsic x/gamma variables. The verifier checks rank 14 and
substitution of its unique solution

\[
\begin{aligned}
 x&=(0,-r,b_0,b_0-\chi,\tfrac12-r,0,
                         b_0+\tfrac12-2\chi,b_0-\chi),\\
 \gamma&=(0,r/2,g_0,g_0+\chi/2,r/2,\tfrac14,g_0,g_0+\sigma/2).
\end{aligned}                                                   \tag{5}
\]

In the face chart the limiting U coordinates are the displayed
horizontal positions on A, and those on B plus `b0`. The fourteen
non-anchor cross-edge equations have rank five in the five free zeta
coordinates. In particular they uniquely force

\[
 \zeta_1=\zeta_4=r/2-8r^2\sigma,
 \qquad \zeta_5=\tfrac14-2\sigma.               \tag{6}
\]

The verifier checks the full five-coordinate solution, not just (6).
These are necessary limits; an exact planar metric solution at finite
t is not assumed.

## 4. A moving-frame height has a strict sign

Fix the actual moving affine frame of vertices `0,2,5,7`:

```
0=(0,0,0), 2=(0,0,1), 5=(1,0,0), 7=(0,1,1).
```

Its orientation agrees with the stretched chart, since its limiting
transverse determinant is positive. It is uniformly well conditioned
after stretching the normal coordinate; no physical lower bound on
delta is required.

Write vertex 1 in this frame as `a=(a_x,a_y,a_z)` and edge 14 as b.
The limiting profile gives `a_x→2r`, `a_y→0`. Equation (4) gives

\[
 b_x/\beta\to0,\qquad b_y/\beta\to1/\sigma.    \tag{7}
\]

The original cap heights and their differences are `O(t)`; the
relative bound on edge 14 is `O(t beta)`. Since the two transverse
coefficients in (7) are bounded after division by beta, the moving
affine shear preserves the relative bound

\[
 b_z=O(t\beta).                                 \tag{8}
\]

More explicitly, if `E_i,F_i` are a point's two transverse coefficients
in this moving basis, its new axial coordinate is

\[
 \frac{H_i-E_iH_5-F_i(H_7-H_2)}{H_2}.
\]

For vertex 1, divide by t and use `E1→2r`, `F1→0`, `H2→1`, and (6).
The result is

\[
 a_z/t\longrightarrow -2\zeta_1+4r\zeta_5
       =-16r(\tfrac12-r)\sigma<0.               \tag{9}
\]

This calculation only needs convergence of the transverse
coefficients; it imposes no rate relative to t.

## 5. The same-cap bracket contradicts its required sign

In the moving frame there is the exact identity

\[
 [0145]=\det(a,a+b,(1,0,0))=a_yb_z-a_zb_y.
\]

Equations (7)–(9) and `a_y→0` therefore imply

\[
 \frac{[0145]}{t\beta}
       \longrightarrow 16r(\tfrac12-r)>0.
\]

The actual bracket is strictly positive eventually, contradicting the
last necessary weak sign in (1). This excludes all 48 interior cells.

When sigma is zero, the virtual-direction equations only force
`v_x=0`; they do not compare m with beta, and (9) loses its strict
coefficient. Those are precisely the 16 recorded boundary cells.

## Reproduction

```sh
python3 research/type7_completion/remaining_adjacent_blowup.py /tmp/type7-adjacent-blowup
g++ -O3 -std=c++17 research/orientation_checkpoint/check_unsat.cpp -o /tmp/type7-adjacent-checker
/tmp/type7-adjacent-checker < /tmp/type7-adjacent-blowup/adjacent_blowup_required_signs.cnf
/tmp/type7-adjacent-checker < /tmp/type7-adjacent-blowup/adjacent_blowup_model_coverage.cnf
```

Require explicit `UNSAT nodes ...` output. The JSON output records all
48 checked canonical mappings and all 16 unexcluded boundary cells.
The symbolic checks verify the two necessity ranks, the three factored
direction brackets, and the signed height and same-cap determinant.
