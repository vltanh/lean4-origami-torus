# Marking 1, mask 04: every bounded transverse limit is a common line

This note proves a limit reduction, **not an exclusion of mask 04**.
Consider an unbounded sequence for marking 1 whose only nonzero limiting
cyclic vertical steps are `b0=b4=1/2`. Put `t=1/y²`. Use the bounded
axis-01 compactification of `exhaustive_remaining_axis.md`, and pass to
a subsequence on which its bounded variables and generic sign model
converge.

Write `h_i` for the limiting positive horizontal step lengths. Thus

\[
0\le h_i\le\tfrac12,\qquad \sum_{i=0}^7h_i=\tfrac72.
\]

Let `P_i` be the two-dimensional transverse limits. The axis gauge gives
`P0=P1=0`. The upper cap is `1234`, and the lower cap is `0567`.

**Result.** All eight transverse points lie on one line. There is a unit
vector `E` such that

\[
\begin{aligned}
P_2&=-h_1E,&P_3&=(h_2-h_1)E,&P_4&=(h_2-h_1-h_3)E,\\
P_7&=h_7E,&P_6&=(h_7-h_6)E,&P_5&=(h_5+h_7-h_6)E.
\end{aligned}
\tag{1}
\]

Moreover

\[
h_0=h_4=\tfrac12,\qquad
\bigl(h_2=\tfrac12\ \text{or}\ h_1=h_3=\tfrac12\bigr),\qquad
\bigl(h_6=\tfrac12\ \text{or}\ h_5=h_7=\tfrac12\bigr).
\tag{2}
\]

These statements retain arbitrary relative rates of all vanishing
vertical steps. In particular, neither `b1*b3/t` nor `b5*b7/t` is
assumed to vanish. A further analysis of the common-line boundary in
(1)–(2) remains necessary. The subsequent
[first transverse stretch](remaining_ray1_mask04_blowup.md) excludes
20 of its 24 closed weak-order cases and reduces it to four symmetric
single-edge endpoints, which remain open.

## 1. Four exact focal triangles and two stresses

The bounded product identities in `exhaustive_remaining_axis.py` give

\[
tq_{25}=4b_2(v_3-v_5-1),\qquad
tq_{47}=(2v_3-2v_4+1)(-2b_6-2tw).
\]

Their displayed non-small factors tend respectively to `-1/2` and `1`.
The variables `q25,q47,w` are uniformly bounded, so `b2,b6=O(t)`.
Consequently `q24=-4*b2*b3/t` and the analogous `q57` tend to zero.
The other outer product scales remain unrestricted.

The limit metric equations now give four perimeter-one triangles:

| Triangle | Three side lengths |
|---|---|
| `123` | `h1,h2,1-h1-h2` |
| `234` | `h2,h3,1-h2-h3` |
| `567` | `h5,h6,1-h5-h6` |
| `670` | `h6,h7,1-h6-h7` |

Thus the two upper apices `P1,P4` lie on the same focal ellipse with
foci `P2,P3`, and the two lower apices `P0,P5` lie on the ellipse with
foci `P6,P7`. A focal distance `a` gives semiaxes
`(1-a)/2` and `sqrt(1-2a)/2`. These ellipses may degenerate.

Define the two chain sums

\[
H_A=h_1+h_2+h_3,\qquad H_B=h_5+h_6+h_7.
\]

The marking-1 total and the individual upper bounds imply

\[
H_A,H_B\ge1,\qquad H_A+H_B\ge\tfrac52.
\tag{3}
\]

The cross-edge equations also give

\[
\begin{aligned}
h_0&=\tfrac12-h_1h_7-P_2\cdot P_7,\\
h_4&=\tfrac12-h_3h_5+(P_4-P_3)\cdot(P_6-P_5).
\end{aligned}
\tag{4}
\]

For an explicit check of the first identity, write `H_i` for the bounded
axial corrections. The equations on `01,02,17` give

\[
H_1=h_0^2,\quad H_2=(1-h_0-h_1)^2-h_1^2,\quad
H_7=H_1+h_7^2-(h_0+h_7-1)^2.
\]

The `27` equation then reduces exactly to
`1-2*h0-2*h1*h7-2*P2.dot(P7)=0`. Rotating the labels by four gives the
second identity. Changing the long axis from `01` to `45` changes the
limiting within-cap edge projections by zero: the axes differ by
`O(1/y)`, while each within-cap axial displacement is `o(y)`.

For a nonzero focal vector `f=P3-P2`, equal focal sums give

\[
H_A-1=-\frac{(P_4-P_1)\cdot f}{1-h_2}.
\tag{5}
\]

The lower identity is

\[
H_B-1=\frac{(P_5-P_0)\cdot(P_7-P_6)}{1-h_6}.
\tag{6}
\]

No orientation of an intrinsic face is used anywhere in this note.

## 2. The finite weak-sign cover

The cover uses all 18,080 generic models of
`solver_remaining_chambers.base_formula()`. It does not use a
mask-specific gap-separation filter. A nonzero limiting bracket fixes
the corresponding generic sign; a zero bracket imposes no condition.

For the upper cap use the ordered quadruple `(1,2,3,4)`, and for the
lower cap use `(0,6,7,5)`. Each order places the two apices first and
last. Suppose a cap is noncollinear and its chain sum is greater than
one. Its focal length lies strictly between zero and `1/2`, and its
two apices are distinct. The foci are strictly inside a genuine convex
ellipse. Therefore neither apex belongs to the convex hull of the
other three points. There is at most one collinear triple.

For the four triangle signs `(d012,d013,d023,d123)`, the affine circuit
has signs `(-d123,d023,-d013,d012)`. Requiring both signs in the circuit,
at most one zero, and excluding an apex from the other three points'
convex hull leaves exactly 22 possible sign types. This is a necessary
superset; no metric realizability assumption is made about a retained
type.

For every nonzero cap triangle, all four brackets with an opposite-cap
vertex have its prescribed sign. Filtering the complete model set by
these necessary conditions gives:

| Cover | Exact result |
|---|---:|
| Two noncollinear cap types | 21 pairs, 52 generic completions |
| Both caps in the central type family | 9 pairs, 4 completions |
| At least one collinear focal-apex triple | 12 pairs |
| One collinear cap: five line orders, 74 other-cap height orders, 22 triangle types | 10 cells |
| Two collinear caps on nonparallel lines | 0 of 50 cases |

The code writes the complete retained cells. It also checks the exact
mixed-sign implications used below. The two triple-endpoint symmetries
`i -> 5-i` and `i -> i+4`, together with their composition, preserve the
two chain sums up to exchange and map any collinear focal-apex triple
to `123`. They preserve the marked metric by the exact dihedral gauge
identities in [the complete limit cover](exhaustive_remaining_locus.md),
including intrinsic inversion for a reversed cyclic order. The complete
generic sign set is also invariant under their normalized action.
Independent cap translations leave every mixed bracket
unchanged, so the new long-axis gauge causes no additional sign choice.

## 3. Two noncollinear caps cannot satisfy (3)

First suppose `H_A,H_B>1`. The endpoint case where one chain equals one
is treated in Section 5.

### 3.1. Central types

For the nine central type pairs put

\[
f=P_3-P_2,\quad g=P_7-P_6,\quad R=P_4-P_1,\quad S=P_5-P_0.
\]

The finite cover forces

\[
[f,g]\ge0,\quad [R,g]\ge0,\quad [f,S]\le0,\quad[R,S]\le0,
\tag{7}
\]

where brackets here denote planar cross products. Rotate so that `f`
points to the right. The two nonzero upper focal-apex triangle signs
give `R_y<0`. Equation (5) gives `R_x<0`.
The first two inequalities in (7) now force `g_x>0`: `g_y>=0`, and a
nonpositive `g_x` would make `[R,g]<0`. Equation (6), together with
`S_y<=0`, forces `S_x>0`. But then `[R,S]>0`, contradicting (7).
This argument permits every mixed cross product in (7) to vanish.

### 3.2. A collinear focal-apex triple

Use the checked symmetries to make the collinear triple `123`. Since
the upper cap remains noncollinear and `H_A>1`, necessarily

\[
h_1=\tfrac12,\quad 0<a:=h_2<\tfrac12,\quad
P_2=-\tfrac12E,\quad P_3=(a-\tfrac12)E,
\]

where `E` is the unit vector to the right. Put `T=P4-P3` and `c=|T|=h3`.
The exact sign cover gives `T_y>0`. Thus the angle `theta` from `E` to
`T` satisfies `0<theta<pi`, and

\[
0<s:=\sin(\theta/2)<1.
\]

The upper triangle equations give the exact identity

\[
\varepsilon:=H_A-1=a+c-\tfrac12
 =ac(1-\cos\theta)=2ac s^2\le\tfrac12s^2.
\tag{8}
\]

Write `v=P6`, `w=P7`, `S=P5`. The twelve possible generic completions
all force the four vectors

\[
U=v,\quad V=-w,\quad W=S-v,\quad D=S-w=U+V+W
\]

to lie in the closed cone

\[
\mathcal C=\{X:X_y\ge0,\ [T,X]\ge0\}.
\]

Its boundary rays are `T` and `-E`, so its angle is `pi-theta`.
Projection on its unit bisector is at least `s|X|` for every
`X in C`. Put `b=h6`, `k=h5`, `l=h7`, and

\[
m=|U|=1-b-l,\qquad n=|D|=1-b-k,\qquad
\eta:=H_B-1=k-m=l-n.
\]

Projecting `D=U+V+W` gives

\[
l-\eta=n\ge s(m+l+k)=s(2m+l+\eta).
\]

Since `m>=0` and `l<=1/2`,

\[
\eta\le\frac{1-s}{2(1+s)}.
\]

Together with (8), this contradicts (3), because

\[
\frac12-\left(\frac{s^2}{2}+\frac{1-s}{2(1+s)}\right)
 =\frac{s(1-s)(s+2)}{2(1+s)}>0.
\tag{9}
\]

The endpoints `s=0,1` are absent precisely because this cap is
noncollinear. They are covered by the collinear-cap cases below.

## 4. Exactly one noncollinear cap is impossible

Continue to assume both chain sums exceed one. By exchanging the caps,
make the upper cap collinear. Its focal length is positive. A genuine
ellipse has only two points on its focal line, so the two distinct
upper apices must be those endpoints. A degenerate ellipse permits the
other listed orders. These give exactly five possibilities:

| Name | Horizontal order of `(P1,P2,P3,P4)` | Weight condition |
|---|---|---|
| I | `P4<P2<P3<P1` | `h1=h3=1/2`, `0<h2<1/2` |
| II | `P2<P4<P1<P3` | `h2=1/2`, `h1,h3<1/2` |
| II_left | `P2<P4<P1=P3` | `h1=h2=1/2`, `h3<1/2` |
| II_right | `P2=P4<P1<P3` | `h2=h3=1/2`, `h1<1/2` |
| II_both | `P2=P4<P1=P3` | `h1=h2=h3=1/2` |

The positive direction `E` is from `P2` to `P3`; the upper outer edges
are `P2-P1=-h1*E` and `P4-P3=-h3*E`.

Enumerate every weak order of the four lower heights perpendicular to
`E`, excluding the all-equal order because the lower cap is
noncollinear. There are 74 such orders. Together with the 22 lower
triangle types, the full generic-model filter leaves only the following
height patterns, with coordinates ordered `(P0,P6,P7,P5)`:

| Upper order | Possible lower height patterns |
|---|---|
| I | `(0,1,0,1)` |
| II | none |
| II_left | `(0,1,1,1)` |
| II_right | `(0,0,0,1)` |
| II_both | all three displayed patterns |

For `(0,1,0,1)`, the retained lower triangle signs imply
`P6-P5=+h5*E` and `-P7=+h7*E`. In both upper orders where this occurs,
`h1=h3=1/2`. Thus (4) gives

\[
h_0=\tfrac12-h_7,\qquad h_4=\tfrac12-h_5,
\qquad \sum h_i=2+h_2+h_6\le3,
\]

contrary to marking 1.

For `(0,1,1,1)`, the three points `P6,P7,P5` lie on one horizontal line.
The retained signs and `H_B>1` force `h5=1/2` and
`P6-P5=+E/2`. The upper orders have `h1=h2=1/2`, so
`h4=1/2-h3`. Consequently

\[
\sum h_i=2+h_0+h_6+h_7\le\tfrac72.
\]

Equality would require `h6=h7=1/2`, making the lower focal ellipse
degenerate and the lower cap collinear. This contradicts the case
assumption. The pattern `(0,0,0,1)` is the reversed argument: it forces
`h7=1/2`, `-P7=+E/2`, and `h0=1/2-h1`; equality in
`sum h_i=2+h4+h5+h6<=7/2` again makes the lower cap collinear.

## 5. A chain sum equal to one

If one chain sum is one, (3) and the individual bounds force, after
exchanging caps if necessary,

\[
H_A=1,\quad h_5=h_6=h_7=\tfrac12,\quad h_0=h_4=\tfrac12.
\]

The lower cap has `P6=0`, `P5=P7=E/2` for a unit `E`. Equality in both
Cauchy inequalities in (4) gives

\[
P_2=-h_1E,\qquad P_4=P_3-h_3E.
\]

Writing `Q=P3`, the focal triangles give
`|Q|=h3` and `|Q+(h1-h3)E|=h1`. Subtraction yields

\[
(h_1-h_3)(Q\cdot E-h_3)=0.
\]

If `h1!=h3`, then `Q=h3*E` and the upper cap is collinear on the same
line. If `h1=h3=a` and the upper cap were noncollinear, its points would
have the form

\[
P_1=0,\quad P_2=-aE,\quad P_3=Q,\quad P_4=Q-aE,
\]

while the lower cap has the two coincident pairs just displayed. The
32 nonzero mixed brackets of this rhombus configuration have signs
independent of its horizontal shape and of `a>0`. Neither orientation
admits any of the 18,080 generic completions. The producer writes both
direct CNFs. Thus this endpoint also has one common transverse line.

## 6. Two collinear caps have the same oriented line

For `H_A,H_B>1`, both caps have one of the five line orders in Section 4,
with the analogous lower-cap orders. If their lines are nonparallel,
every nonzero mixed bracket is the product of the signed upper scalar
step, the signed lower scalar step, and the nonzero cross product of
the two line directions. All 25 order pairs in both orientations are
incompatible with the complete generic model set. This is the exact
50-case cover; coincident vertices impose no sign condition and no
relative rate assumption.

Let `E,F` be the upper and lower positive focal directions. The outer
edge vectors are `-h1*E,-h3*E,-h5*F,-h7*F`. They are parallel, so
`E.dot(F)=+1` or `-1`. If they were opposite, (4) would give

\[
\sum h_i=1+h_2+h_6+
(h_1+h_7-2h_1h_7)+(h_3+h_5-2h_3h_5)\le3.
\]

Here each parenthesis is at most `1/2`, since for `0<=u,v<=1/2`,

\[
\tfrac12-(u+v-2uv)=2(\tfrac12-u)(\tfrac12-v)\ge0.
\]

Therefore `E=F`, and (4) gives `h0=h4=1/2`. The endpoint analysis in
Section 5 already gives the same direction when one chain equals one.
This proves (1). The two upper focal equations now reduce to

\[
(1-2h_1)(1-2h_2)=0,\qquad
(1-2h_2)(1-2h_3)=0,
\]

and similarly below, proving (2).

Equivalently, the remaining closed weight families have both middle
weights equal to `1/2`, both outer pairs equal to `1/2`, or one of each.
They retain all their endpoints. This note makes no assertion that
these common-line limits are realizable or excluded at finite `y`.

## 7. Replay

Run

```sh
python research/type7_completion/remaining_ray1_mask04.py OUTPUT
```

This freshly enumerates the shared model set with the finite-domain
backend. Alternatively, `--models MANIFEST` accepts the independently
verified `remaining_chambers.json` produced by the shared compiler.
The code checks every stated finite count and implication, the stress
polarization, the focal excess identity, the exact positive gap (9),
the endpoint metric subtraction, and the final line factors. It writes
52 direct CNFs for independent UNSAT replay, plus `coverage.json` for
the exhaustive weak-type and weak-order records. Model completeness is
the already independently checked shared Boolean coverage theorem.
The fresh producer and all 52 independent RUP replays passed; the
certificate-production and replay batch took 3.066 seconds in the
shared workspace. This timing is not a hardware-controlled benchmark.
