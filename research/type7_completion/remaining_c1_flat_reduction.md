# Ray-2 C1: reducing the two-collinear-cap boundary

Assume `0<alpha,beta<1` and both endpoint caps 234 and 067 are
collinear. If all four cap edges `h2,h3,h6,h7` are positive, then
**every transverse point lies on one common line through the origin**.
Two additional zero-edge order orbits have parallel cap directions.
This is a reduction, not an exclusion of the entire boundary.

The companion `remaining_c1_flat_reduction.py` exports fifteen CNFs.
Every CNF requires independent RUP replay. Actual zero brackets retain
both possible generic completion signs. The argument uses no
comparison between collapse rates.

## 1. Orders, source identities, and symmetry

Use the closed C1 circle identities and nearest-lift inequalities.
The ray-2 weights satisfy `0<=hi<=1/2`, `sum hi=5/2`, and
`hi+h(i+1)>=1/2`. Write `di=1/2-hi`.

The complete weak order lists are:

| Label | Upper cap 234 | Lower cap 067 |
|---|---|---|
| A | 4 strictly between 2 and 3 | 0 strictly between 6 and 7 |
| B | 2 strictly between 3 and 4 | 6 strictly between 0 and 7 |
| C | `2=4`, 3 distinct | `0=6`, 7 distinct |
| D | 3 strictly between 2 and 4 | 7 strictly between 0 and 6 |
| E | `2=3`, 4 distinct | `6=7`, 0 distinct |
| F | `3=4`, 2 distinct | `0=7`, 6 distinct |

The positive-edge stratum consists precisely of A,B,C,D on each cap.
The two cap segments have length `1/2`; fully coincident caps cannot
have perimeter one. Orders A,B,C have parallel, equally directed tip
vectors `E2,E3` above and `P7,F` below. Order D reverses the respective
pair of tip directions.

The generic source is the original embedding/linking formula with
only its freely chosen ambient-orientation unit removed. Both strict
axial cuts remain. Actual trits add affine cocycles, weak
Grassmann-Pluecker relations, the specified positive point
interpolations or coincidences, and zero brackets for both cap triples.

The checker expands all 55 nontrivial height identities

\[
\alpha[ijkl]=\sum c_{ab}[01ab]
\]

in arbitrary transverse coordinates. It retains the 45 whose
coefficients have a uniform strict sign on the entire open height
square: their magnitudes are among `1,alpha,beta,1-alpha,1-beta`.
The ten identities with a coefficient `alpha-beta` are omitted in
their entirety. No height-order case or sign assumption is needed.

The checked marked reflection `i -> 6-i` exchanges A and B on each
cap and fixes C,D. The cap swap `i -> i+4` exchanges the two labels.
These generate a four-element symmetry cover. Both transformations
change the relative direction of `E2` and `P7` precisely when exactly
one cap has type D. The checker enumerates all 16 positive-edge order
pairs and all 32 order/direction pairs and records the selected proof
case. Axis reanchoring is an affine shear; on either cap it is a
common translation, so these direction statements are preserved.

The pair slacks `h0+h1-1/2`, `h2+h3-1/2`, `h4+h5-1/2`,
`h6+h7-1/2` sum to `1/2`. Consequently CC is impossible: its two cap
slacks already sum to one.

## 2. Nonparallel cap directions are impossible with positive edges

Five CNFs exclude nonparallel cap directions for canonical order
pairs BA, BB, BC, BD, and CD. Nonparallelism is represented by the
disjunction of the actual nonzero trits for all nine brackets with
two upper and two lower vertices. This introduces no chosen nonzero
edge or division. The marked symmetry cover leaves only DD and the
already impossible CC case.

### The DD case

Write

\[
E_2=h u,\quad E_3=-j u,\quad
P_7=k v,\quad F=-\ell v,
\qquad j=\tfrac12-h,\quad\ell=\tfrac12-k,
\]

where `u,v` are unit vectors and `0<h,k<1/2`. Assume their directions
are independent, and choose the ambient orientation so that
`cross(u,v)>0`. Equivalently, `[2367]>0`.

Both linked vectors `Y0,Y5` are nonzero: the closed norm identity
from the section proof would force respectively `h7=1/2` or `h6=1/2`
if one vanished. Because `u,v` are independent, neither corresponding
pair of anchor brackets can be simultaneously zero.

One exact CNF then leaves only these two actual patterns:

\[
([0123],[0127],[3456],[4567])
\in\{(-,0,0,-),\ (0,+,-,0)\}.                       \tag{1}
\]

The marked reflection sends the second pattern to the first and
preserves `[2367]>0`: it sends that bracket to `-[0347]`, which is
positive in the displayed DD geometry. Thus assume the first pattern.
Its zero brackets and strict companion signs give

\[
Y_0=-n v,\qquad Y_5=-m u,
\qquad n,m>0.                                      \tag{2}
\]

In particular, `Y5` points in the same direction as `E3`.

The following closed Cauchy-saturation fact is useful. For one circle
pair with parameter `a`, upper edge `h<1/2`, adjacent deficits `p,q`
with `p+q<=1/2`, suppose its linked vector is a positive multiple
`n>0` of the upper unit direction. If `q>0`, the first dot identity
and the collinearity of `R=aE-Y` imply

\[
q=2h(ah-n).
\]

Substitution into the radius definition gives the exact identity

\[
p+q-\tfrac12
=\frac{(1-2h)\,[a(1-2h)+2n]}{2(1-a)}>0,             \tag{3}
\]

contrary to nearest lifts. Hence `q=0`. The checker expands (3)
exactly; it requires no strict deficit assumption in the conclusion.

Apply (3) to the second pair, with upper edge `j`, to obtain
`d4=0`, so `h4=1/2`. Its first dot equality now makes `R5` opposite
to `E3`. Put `lambda=n/alpha`. In the positively oriented basis
`u,v`, the relevant transverse points are

\[
\begin{aligned}
P_2&=-\lambda v,& P_4&=-\tfrac12u-\lambda v,\\
P_6&=\tfrac12v,& P_7&=kv,\\
P_5&=(1-\beta)h_5u+
       ((1-\beta)/2-\beta\lambda)v.
\end{aligned}
\]

Here `h5>=1/2-h6=k>0`, and
`m=beta/2+(1-beta)h5>0`. The four exact determinants are

\[
\begin{aligned}
[1467]&=\alpha\ell\,\operatorname{cross}(u,v)/4>0,\\
[1567]&=-\alpha(1-\beta)h_5\ell\,
             \operatorname{cross}(u,v)/2<0,\\
[2457]&=(1-\beta)\ell\,\operatorname{cross}(u,v)/4>0,\\
[4567]&=-m\ell\,\operatorname{cross}(u,v)/2<0.
\end{aligned}                                       \tag{4}
\]

A separate four-unit CNF proves these strict signs incompatible with
the original generic source. Therefore DD also has parallel cap
directions.

## 3. Parallel cap directions force a common transverse line

Let `u` be the unit direction of `E2`. Write `P7` as a nonzero
multiple of `u`; all four cap edges are still positive.

First consider an opposite pair of directions. If `P7` points
opposite to `E2` and `[0123]` is nonzero, then `[0127]` has the same
sign. An ambient reflection makes both positive. The parallel-anchor
CNF excludes this, so both actual brackets vanish. Applying the same
argument after the marked annulus reflection proves the corresponding
statement for `E3,F` and anchors `[3456],[4567]`.

For equally directed `E2,P7`, impose the positive affine dependency

\[
r_2-r_3=\kappa(r_7-r_0),\qquad\kappa>0.
\tag{5}
\]

All coefficient sums vanish. Every triple applied to (5) gives the
actual trit relations used in five further CNFs. For canonical pairs
AA, AD, BD, CD, and DD, they force **all four** anchor brackets to
vanish. The finite symmetry cover transports these statements to
every order/direction combination except AB, AC, and CC, or cases
where both pairs of directions are opposite and were handled above.

CC was excluded by its slack budget. For equally directed AB or AC,
the first pair has `h2=h7=1/2`. Since its two unit directions agree,
their projections of `Y0` agree, and the exact projection identity is

\[
\frac{d_1}{h_2}+\frac{d_0}{h_7}=1.
\]

Thus `d0+d1=1/2`. The second pair also has equally directed tip
vectors, so

\[
\frac{d_4}{h_3}+\frac{d_5}{h_6}=1.                  \tag{6}
\]

The ray-2 total weight, with `h2=h7=1/2`, instead gives
`d4+d5=h3+h6`. Nearest lifts give `d4<=h3` and `d5<=h6`, so equality
forces both bounds to be equalities. The left side of (6) would be
two. Both denominators are positive, so this is a contradiction.

The surviving cases therefore have all four actual anchors zero.
Since `E2` and `P7` are nonzero and parallel, `[0123]=0` puts `P3`
on their common line through 0, hence also `P2,P4`. The lower cap
already lies on that line. Finally, `[3456]=0` and `E3!=0` put `R5`
and therefore `P5` on it. This proves the positive-edge reduction.

## 4. Two zero-edge order orbits

Suppose the upper order is E, so `P2=P3`, `h2=0`, and
`h1=h3=1/2`. In lower order A or C, write `h6=1/2`, `h7=k`,
where respectively `0<k<1/2` or `k=1/2`. The ray-2 slack budget
and `h0+h7>=1/2` force

\[
h_0=\tfrac12-k,\qquad h_4+h_5=\tfrac12.
\]

Take `P7=kv` with `|v|=1`. The first circle pair is saturated and gives

\[
P_3=\frac{1/2-(1-\alpha)k}{\alpha}v,
\quad P_6=(k-1/2)v.
\]

Write `E3=(1/2)e`. The second pair gives `R5=h5 e` and
`Y5=(h4-(1-beta)/2)e`. Its lower dot identity is exactly

\[
\tfrac12(h_4-(1-\beta)/2)(e\cdot v-1)=0.
\]

If the cap directions are nonparallel, `Y5=0`. The limiting spatial
points then satisfy the two positive affine dependencies

\[
r_5=\beta r_4+(1-\beta)r_6,
\qquad
r_1+\alpha r_7=\alpha r_3+r_6.                     \tag{7}
\]

The two final CNFs combine (7) with the exact weak cap orders and
exclude nonparallel directions. This also covers the marked symmetry
orbits of EA and EC. It does not claim that these zero-edge cases
already lie on one common transverse line.

## 5. Replay and remaining scope

```sh
python research/type7_completion/remaining_c1_flat_reduction.py /tmp/type7-c1-flat-reduction
python research/type7_completion/solver_cnf_certificates.py /tmp/type7-c1-flat-reduction-rup \
  --checker /path/to/solver-check-rup /tmp/type7-c1-flat-reduction
```

The checker binds the height expansions, Cauchy-saturation identity,
four strict DD minors, DD pattern reflection, all positive-edge
symmetry cases, and the two zero-edge dependencies. The fifteen source
CNFs must independently replay. The positive-edge common-line scalar
families still need classification and exclusion. The other zero-edge
orbits, arbitrary relative rates, and height endpoints remain separate
tasks; no complete two-collinear-cap exclusion is asserted here.
