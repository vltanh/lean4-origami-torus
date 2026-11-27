# A triple cluster cannot face a positive-weight collinear cap after blow-up

**Result.** Consider a common-line ray-3 limit and a bounded transverse
blow-up whose two caps are collinear on different lines. If one physical
cap has a triple cluster and a tip, and all four weights of the other
cap have positive limits, the sequence is impossible. Both collapsing
edges may have arbitrary rates relative to each other, the transverse
width, and `t=1/y²`.

The complete zero-stress two-line cover has 288 such order pairs.
The checker maps all of them to thirteen marked forms, representing
nine normalized orders on the second line. Twenty-eight necessary sign
CNFs and one relative-height calculation exclude every case. This is
an asymptotic research theorem, with no fixed-height threshold.

## 1. A complete directional cover

Use verified phase symmetries and a common horizontal reflection to
put the physical cluster at `0,1,4`, with tip 5 at distance `1/2`.
Vertices 0 and 2 are the longitudinal anchors. In a moving affine
frame, the limiting cap points are

\[
 A_0=A_1=A_4=0,\quad A_5=E=(1,0),\qquad
 B_2=0,\quad B_3=\lambda F,\quad B_6=\nu F,\quad B_7=F=(0,1),
\]

at axial levels zero and one respectively. The frame is uniformly
conditioned after the normal stretch. Since the partner's four physical
weights are positive, `lambda!=0`, `nu!=lambda`, and `nu!=1`.
Opposite vertices may coincide.

Normalize each collapsing A edge, `a=01` and `b=14`, by its own
stretched transverse norm. Their directions have nonzero subsequential
limits. The relative axial bounds give an axial component `O(t)`
after these normalizations. Every necessary determinant used below
contains one of these edges or the exact pair `(a,b)` as factored rows.
Errors therefore remain relative to the appropriate edge or edge
product, without assuming a minimum edge length.

The checker introduces signs for the two direction components of each
edge, the components of `a+b`, and `det(a,b)`. It retains every sign
combination consistent with component addition and the determinant
identity. It covers all three ratios of their stretched norms: a
dominates, they are comparable, or b dominates. In a dominant case,
the leading sum direction is the dominant edge's direction.

The raw symbolic point determinants have scalar coefficients only of
the form `s-r`, where `r,s` are distinct members of `{0,lambda,nu,1}`.
Their signs are fixed throughout a weak-order cell. Thus one rational
representative certifies the entire cell, including its specified
opposite-vertex coincidences; no numerical sampling assumption enters.

All cells and norm ratios contradict the necessary orientation and
linking formula except

\[
 \nu<\lambda<0,\qquad |b|_{\mathrm{stretched}}/|a|_{\mathrm{stretched}}\to0.
\]

Two further CNFs show that this survivor forces

\[
 a\text{ in direction }+E,\qquad b\text{ in direction }+F,
 \qquad [0145]\le0.                            \tag{1}
\]

The signs of every zero limiting determinant remain free unless the
directional calculation forces a nonzero leading term.

## 2. The surviving physical configuration

Write its physical common-line coordinates as

\[
 A=(0,0,0,1/2),\qquad B=(0,u,v,-w),
 \quad 0<u<v<1/2,\quad w=1/2-v>0.
\]

Then `lambda=-u/w`, `nu=-v/w`. Let `alpha=h01`, `beta=h14` be the actual
positive intrinsic short weights. Direction E has nonzero physical X
component `1/2`, and direction F has component `-w`. Equation (1) and
the exact edge metric therefore compare each stretched edge scale with
its physical weight. In the moving frame,

\[
 a_x/\alpha\to2,\quad a_y/\alpha\to0,\quad
 b_x/\beta\to0,\quad b_y/\beta\to1/w,
 \quad \beta/\alpha\to0.                       \tag{2}
\]

These scale comparisons follow from the forced directions. They are
not extra assumptions on the collapse rates.

## 3. A relative stress identity determines the small height

Let `R_ij` be the exact cross-ring stress, with ring edges indexed
cyclically in `A=(0,1,4,5)` and `B=(2,3,6,7)`. Put

\[
 c_0=-x_2+1/4+2\gamma_2.
\]

The exact identities checked in the script are

\[
 c_0=2(R_{02}+R_{03}),\qquad
 \gamma_{01}=\alpha/2-R_{01}.                    \tag{3}
\]

Here the first index of R is the A-edge index, so all three stresses
in (3) involve the actual edge 01. Divide them by alpha before taking
limits. Its physical unit direction is positive horizontal, while the
four B edges have physical steps

\[
 (u,v-u,-1/2,w),\qquad
 (h_{B,j})=(u,v-u,1/2,w).
\]

The relative gamma and axial bounds make their extra metric terms
vanish after division by alpha. Consequently

\[
 (R_{0j}/\alpha)_{j=0}^3\to(0,0,1,0),\quad
 c_0/\alpha\to2,\quad \gamma_{01}/\alpha\to1/2. \tag{4}
\]

The rank-fourteen intrinsic reconstruction, valid at the endpoint
`r=0` of `remaining_two_line_blowup.py`, gives
`x2->v`, `gamma2->v/2-1/8`, `x5->0`, `gamma5->1/4`.

For squared spatial distances `D_ij`, define

\[
 \rho_1=D_{01}-D_{12}+D_{02},\qquad
 \rho_5=D_{05}-D_{25}+D_{02}.
\]

Their exact intrinsic expressions are

\[
\begin{aligned}
 \rho_1&=-c_0+(1-2x_2)\alpha+\gamma_{01}
                         +2t\gamma_2\gamma_{01},\\
 \rho_5&=x_5+1/4+2x_5x_2+\gamma_5-2\gamma_2
                         +2t\gamma_5\gamma_2.
\end{aligned}
\]

Thus (4) yields

\[
 \rho_1/\alpha\to-1/2-2v,\qquad \rho_5\to3/4-v. \tag{5}
\]

In coordinates along the actual axis 02, put `L=|02|`. The normalized
axial correction is `rho/(2L²)` and `1/(2L²t)->2`. Changing to the
moving frame `0,2,5,7`, equation (2) therefore gives

\[
 \frac{a_z}{t\alpha}
 \longrightarrow2\bigl((-1/2-2v)-2(3/4-v)\bigr)=-4. \tag{6}
\]

The coefficient of the other transverse basis vector divided by alpha
tends to zero, and that anchor's axial correction divided by t is
bounded. This controls its contribution even if alpha is much smaller
than t. The same relative argument gives `b_z=O(t beta)`.

## 4. Final volume contradiction

In the moving frame,

\[
 [0145]=a_yb_z-a_zb_y.
\]

Equations (2) and (6) imply

\[
 \frac{[0145]}{t\alpha\beta}\longrightarrow\frac4w>0,
\]

contradicting (1). Together with the other sign certificates, this
excludes all 288 order pairs.

## Reproduction

```sh
python3 research/type7_completion/remaining_two_line_triple.py /tmp/type7-two-line-triple
g++ -O3 -std=c++17 research/orientation_checkpoint/check_unsat.cpp -o /tmp/type7-sign-check
```

Replay each of the twenty-eight directional CNFs and the model-coverage
CNF with the independent checker, requiring explicit `UNSAT nodes ...`
output. The coverage formula is the previously certified complete
1,888-model formula. The JSON output records every checked marked
mapping; the symbolic verifier checks the stress, distance, and
relative-height identities exactly.
