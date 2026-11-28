# Interior C1: unit directions at shrinking cap edges

For either remaining marking, every shrinking cap edge in an interior
C1 sequence has a well-defined unit transverse direction after passing
to a subsequence. Its normalized spatial axial difference and intrinsic
vertical difference are both bounded by a constant times `t` times
the edge's horizontal length, where `t=1/y²`.

This relative estimate remains valid however quickly the edge shrinks.
It supplies the missing justification for dividing determinants by a
vanishing cap edge, or simultaneously by two such edges. It is not an
exclusion of the remaining zero-edge cases.

## 1. Exact finite equations at edge 23

Work in the bounded axis chart with `P0=P1=0`. Write

\[
\ell=\zeta_1,\qquad b=v_1,\qquad h=h_2>0,
\qquad r=\frac{1/2-h_1}{h}.
\]

Here `zeta` is the actual normalized spatial axial coordinate, while
`v` is the intrinsic vertical coordinate. Strict nearest lifts imply
`0<r<1`; its limit may be either endpoint. Define the finite quantities

\[
w=\frac{P_3-P_2}{h},\qquad
a=\frac{\zeta_3-\zeta_2}{th},\qquad
g=\frac{v_3-v_2}{th},\qquad k=h_0-r.
\]

These definitions alone give no bounds on `a,g,w`. The exact edge
equations on 01,02,03,12,13,23 give

\[
\ell^2=b^2+t h_0^2,\qquad
\ell a-bg=k,\qquad |w|^2+t a^2=1+t g^2.           \tag{1}
\]

For the middle equation, subtract the difference of the 12 and 13
equations from the difference of the 02 and 03 equations. The four
horizontal lifts are

\[
\begin{aligned}
X_{02}&=1-h_0-h_1,&X_{03}&=1-h_0-h_1-h,\\
X_{12}&=-h_1,&X_{13}&=1-h_1-h.
\end{aligned}
\]

Their squared differences reduce exactly to
`2h(h0-r)`. The companion checks this polarization as a polynomial
identity before taking any limit.

Put `Q=P5-P2`, `theta=zeta5-zeta2`, `V=V25`, and `X=X25`.
Triangle 235 has zero cocycle period in both markings; its horizontal
lifts obey `X35=X25+h`, and both long edges have vertical cocycle one.
Polarizing its three metric equations gives

\[
w\cdot Q+a\theta=-X+gV.                          \tag{2}
\]

Eliminating `a` using (1) gives the exact identity

\[
\left(\frac{b\theta}{\ell}-V\right)g
=-X-w\cdot Q-\frac{k\theta}{\ell}.                \tag{3}
\]

In the interior C1 limit,

\[
\ell,b\longrightarrow\alpha/2>0,\quad
\theta\longrightarrow-(1-\beta)/2,\quad
V\longrightarrow(1-\beta)/2.
\]

Therefore the coefficient of `g` in (3) tends to `-(1-beta)`, which
is strictly negative. All other quantities on the right except `w`
remain bounded. Thus

\[
|g|\le C(1+|w|).                                 \tag{4}
\]

## 2. Absorption at the edge's own scale

The three equations in (1) also give the exact norm identity

\[
\ell^2|w|^2
=\ell^2+t^2h_0^2g^2-2tbkg-tk^2.                 \tag{5}
\]

The companion verifies (5) as a polynomial combination of the original
metric equations and the first polarization. Since `k` is bounded and
`ell` stays positive, (5) implies

\[
|w|\le C_1(1+t|g|).
\]

Combining this with (4) and absorbing the resulting multiple of
`t|g|` for sufficiently small `t` proves that `g`, `w`, and then `a`
are bounded. Returning to the last equation in (1) gives

\[
\boxed{\quad |w|\longrightarrow1,\qquad
v_3-v_2=O(th_2),\qquad
\zeta_3-\zeta_2=O(th_2).\quad}                    \tag{6}
\]

There was no comparison between `h2` and `t`, a deficit, a cap area,
or another shrinking edge. In particular the argument covers edges
much smaller than `t`. Along a subsequence `w` converges to a unit
vector even when `P2=P3` in the unscaled limit.

The checked marked reflection `i -> 6-i` and cap swap `i -> i+4`
send edge 23 to the four edges 23,34,67,07. Their transformed height
parameters remain interior. Applying the same argument in the
corresponding bounded axis charts proves the assertion for every cap
edge.

These relative estimates also transfer back to the original bounded
chart. The two long axes differ by physical angle `O(1/y)`. Their
normalized axial coordinates consequently differ by a bounded
`O(t)` linear form in the transverse coordinates, plus an `O(t)`
multiple of the old axial coordinate. Across a cap edge, the resulting
change is `O(th)` by (6). The limiting transverse directions differ
only by the limiting rotation of the transverse plane.

## 3. Valid single and double determinant normalizations

For any four-point determinant containing 2 and 3, divide by the
positive finite number `h2`. Subtract its column at vertex 2 from
the column at vertex 3. That column becomes

\[
\left(\frac{P_3-P_2}{h_2},
       \frac{\zeta_3-\zeta_2}{h_2}\right)
=(w,ta)\longrightarrow(w_\infty,0).               \tag{7}
\]

The other columns remain bounded. Hence all fifteen divided
determinants converge to the forms obtained by replacing that edge
with the horizontal unit vector `(w_infinity,0)`. A nonzero limit fixes
the original generic completion sign; a zero limit leaves it free.
The companion expands all fifteen forms and verifies that the omitted
axial term carries a factor `t`.

For two simultaneous zero edges 23 and 07, write

\[
\frac{P_3-P_2}{h_2}\to w,\qquad
\frac{P_7-P_0}{h_7}\to v.
\]

Subtracting both short-edge columns gives the exact divided formula

\[
\frac{[0237]}{h_2h_7}
=\det\left((P_2,\zeta_2),\ (w_n,t a_n),\ (v_n,t c_n)\right)
\longrightarrow\tfrac12\,\operatorname{cross}(w,v). \tag{8}
\]

The checker verifies (8) symbolically with independent edge lengths.
No ratio `h2/h7` enters. Analogous formulas follow by the same marked
symmetries. Determinants divided by different factors must be linked
to the same generic source; ordinary affine cocycles cannot be mixed
between unrelated normalizations without first checking their scale
factors.

## 4. Complete remaining zero-edge order cover

The cap-order labels are those of the
[two-collinear-cap reduction](remaining_c1_flat_reduction.md). The
reflection exchanges A/B and E/F, fixes C/D, and acts on both caps.
The cap swap exchanges the two order labels. Their six disjoint
orbits cover every order pair with at least one zero cap edge:

| Representative | Full orbit |
|---|---|
| EA | EA, AE, FB, BF |
| EB | EB, BE, FA, AF |
| EC | EC, CE, FC, CF |
| ED | ED, DE, FD, DF |
| EE | EE, FF |
| EF | EF, FE |

The companion checks the cover of all twenty order pairs and the
marked edge maps exactly. The earlier reduction already makes all
transverse points collinear in EA and EC: its explicit formulas put
`P3,P6,P7` on the lower line, and its parallel-direction conclusion
then puts `P4,P5` there as well. This statement alone does not exclude
those orbits. The other four orbits and all height endpoints still
require further arguments. Ray-2 C0 is a separate component.

Run the exact source replay with:

```sh
python research/type7_completion/remaining_c1_short_edges.py /tmp/type7-c1-short-edges
```

The replay checks the two finite polarizations, the relative norm
identity, both marked cocycles, all fifteen single-edge determinant
normalizations, the independent two-edge normalization, and the
complete six-orbit cover. It makes no zero-edge exclusion claim.
