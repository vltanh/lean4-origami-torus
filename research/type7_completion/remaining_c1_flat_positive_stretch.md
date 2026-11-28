# Ray-2 C1: excluding the two-collinear-cap stratum with positive cap edges

There is no unbounded embedded ray-2 sequence with an interior C1 limit
in which both endpoint caps are collinear and

\[
h_2,h_3,h_6,h_7>0,\qquad 0<\alpha,\beta<1.
\]

The [common-line reduction](remaining_c1_flat_reduction.md) first puts
all transverse vertices on one line. The exact scalar classification
below leaves twenty families. A nontrivial normal stretch is impossible
for each family, as certified by twenty independently replayed CNFs.
Zero cap edges and height endpoints remain separate cases. There is no
assumption on relative collapse rates.

## 1. Four scalar possibilities for a linked pair

Orient the common transverse line so that `E2=P2-P3` is positive.
Consider one of the two linked pairs from the
[closed circle identities](solver_remaining_c1_geometry.md). Write its
upper and lower edge lengths as `h,k>0`, its height parameter as
`0<a<1`, and its two remaining weights as `H0,H1`. Set

\[
p=\tfrac12-H_0,\quad q=\tfrac12-H_1,\quad
\rho=\tfrac12-ah+aq-(1-a)p,\quad \sigma=1-ah-\rho.
\]

Relative to the positive upper-edge direction, write the radius vector
as `R=eta*rho` and the lower edge as `epsilon*k`, where the two signs
belong to `{−1,+1}`. The scalar circle and dot equations include

\[
q=h\rho(1+\eta),\qquad
p=k\bigl(\sigma+\epsilon(ah-\eta\rho)\bigr).       \tag{1}
\]

Define the pair's budget contribution as `C=h+k-p-q`. Solving (1)
together with the radius formula gives:

| Type | `eta` | `epsilon` | `H0` | `H1` | `rho` | `C` |
|---|---|---|---|---|---|---|
| 0 | − | + | `1/2-k` | `1/2` | `a(1/2-h)+(1-a)(1/2-k)` | `h` |
| 1 | − | − | `1/2` | `1/2` | `1/2-ah` | `h+k` |
| 2 | + | + | `1/2` | `1/2-h` | `1/2` | `k` |
| 3 | + | − | `1/2-k+2ahk` | `1/2-h+2(1-a)hk` | `1/2-(1-a)k` | `2hk` |

Here is the completeness argument, including the exceptional boundary.
For `eta=-1`, the first equation gives `q=0`. With `epsilon=+1`, the
second gives `p=k`. With `epsilon=-1`, it gives
`p(1-2(1-a)k)=0`; its second factor is at least `a>0`, so `p=0`.
For `eta=+1,epsilon=-1`, the second equation gives
`p=k(1-2ah)`, yielding type 3. For `eta=epsilon=+1`, elimination gives

\[
p\,[1-2ah-2(1-a)k]=0.                            \tag{2}
\]

The bracket is `a(1-2h)+(1-a)(1-2k)`. It is positive unless
`h=k=1/2`. Outside that exceptional case, (2) gives type 2. At
`h=k=1/2`, equations (1) instead give `p+q=1/2`, hence `C=1/2`.

A zero radius is covered as well. Its defining nonnegative sum
`a(1-H1-h)+(1-a)H0` forces `H0=0,H1=h=1/2`. The second equation
forces `k=1/2` and the positive relative direction, again giving
`C=1/2`. Every ordinary pair in the table has strictly positive cost,
and every exceptional pair has cost `1/2`.

For the first pair use

\[
(H_0,H_1,h,k,a)=(h_0,h_1,h_2,h_7,\alpha);
\]

for the second use

\[
(H_0,H_1,h,k,a)=(h_5,h_4,h_3,h_6,\beta).
\]

The ray-2 identity `sum hi=5/2` is exactly

\[
C_{\rm first}+C_{\rm second}=\tfrac12.           \tag{3}
\]

Both pairs have positive cap edges. Thus the exceptional case or zero
radius in either pair is impossible by (3). In particular both radius
signs used in the classification are defined, and `P3` is nonzero.
The companion checks all four substituted circle, dot, radius, and cost
identities exactly, as well as the exceptional factorization (2).

## 2. The complete twenty-family cover

Use the order labels A,B,C,D from the common-line reduction. With
`0<x,y<1/2`, their edge data and direction signs are:

| Order | Upper `(h2,h3,su)` | Lower `(h7,h6,sl)` |
|---|---|---|
| A | `(1/2,x,+1)` | `(y,1/2,+1)` |
| B | `(x,1/2,+1)` | `(1/2,y,+1)` |
| C | `(1/2,1/2,+1)` | `(1/2,1/2,+1)` |
| D | `(x,1/2-x,-1)` | `(y,1/2-y,-1)` |

Thus `E3=su*h3`, `P7=epsilon*h7`, and
`F=epsilon*sl*h6`. Let `eta` be the radius sign for the first pair,
and let `theta` be the second radius sign relative to `E3`.
The relative lower-edge sign for the second pair is
`epsilon*su*sl`.

The checker enumerates all `4*4*2*2*2=128` choices. Their budget
polynomials are multilinear in `x,y`. Exact interpolation from the four
corners of `[0,1/2]^2` gives a uniform strict nonzero sign for 108 of
them, excluding those cases by (3). The remaining twenty are listed
below. A zero condition means that (3) is identically satisfied.

| Index | Orders | `epsilon` | `eta` | `theta` | Pair types | Budget condition |
|---|---|---|---|---|---|---|
| 00 | AA | − | + | + | 3,3 | `x+y=1/2` |
| 01 | AA | + | + | − | 2,0 | `x+y=1/2` |
| 02 | AD | − | + | − | 3,0 | `x+y=1/2` |
| 03 | AD | − | + | + | 3,2 | 0 |
| 04 | BB | − | + | + | 3,3 | `x+y=1/2` |
| 05 | BB | + | − | + | 0,2 | `x+y=1/2` |
| 06 | BD | + | − | + | 0,3 | `x=y` |
| 07 | BD | + | + | + | 2,3 | 0 |
| 08 | CD | − | + | + | 3,2 | 0 |
| 09 | CD | + | + | + | 2,3 | 0 |
| 10 | DA | + | − | + | 0,3 | 0 |
| 11 | DA | + | + | + | 2,3 | `x=y` |
| 12 | DB | − | + | − | 3,0 | 0 |
| 13 | DB | − | + | + | 3,2 | `x+y=1/2` |
| 14 | DC | − | + | − | 3,0 | 0 |
| 15 | DC | + | − | + | 0,3 | 0 |
| 16 | DD | + | − | − | 0,0 | 0 |
| 17 | DD | + | − | + | 0,2 | `x=y` |
| 18 | DD | + | + | − | 2,0 | `x=y` |
| 19 | DD | + | + | + | 2,2 | 0 |

In each case the transverse scalar coordinates are

\[
\begin{aligned}
P_0=P_1&=0,&P_3&=-\eta\rho_1/\alpha,\\
P_2&=P_3+h_2,&P_4&=P_3+s_u h_3,\\
P_7&=\epsilon h_7,&P_6&=\epsilon(h_7-s_l h_6),\\
P_5&=\beta P_3+(1-\beta)P_6+\theta s_u\rho_5.
\end{aligned}                                                     \tag{4}
\]

As a further exact source check, every family satisfies all twelve
closed C1 projected stresses reconstructed from the original 29-row
metric system. This check includes the product-scale syzygies; it is
not a replacement for the necessary scalar classification above.

## 3. A bounded normal stretch with no rate assumption

For each finite realization retain the bounded axis gauge `P0=P1=0`
and rotate the transverse plane so that `P3` lies on the scalar axis
with the sign in (4). This is nonsingular because its limit is nonzero.
Write the finite transverse points as `(Xi,Yi)` and put

\[
\delta=\max_{i\in\{2,4,5,6,7\}}|Y_i|.
\]

Every finite realization has `delta>0`, by the established necessary
nondegeneracy of its K4 tetrahedra. The common-line limit gives
`delta -> 0`. After a subsequence the normal coordinates converge:

\[
N_i=\lim Y_i/\delta,\qquad N_0=N_1=N_3=0,
\qquad \max_{i\in\{2,4,5,6,7\}}|N_i|=1.          \tag{5}
\]

Dividing the normal coordinate by `delta` and the physical axial
coordinate by the elongation parameter has positive determinant.
The resulting points are bounded and converge to `(Pi,Ni,zi)`, where
`z=(0,alpha/2,1/2,1/2,1/2,beta/2,0,0)`. No axial error is divided by
`delta`. Thus every nonzero stretched determinant has the same sign
as the original finite determinant eventually, for all possible
relative rates. A zero limiting determinant leaves the generic sign
completion unrestricted.

Reflection of the normal coordinate permits the source's ambient
orientation unit to be retained while leaving the positive scalar
direction `E2` unchanged.

## 4. Exact polynomial sign relaxation

Apply the further positive-determinant affine map

\[
(X,N,z)\longmapsto(2X+2s z,\ N,\ 2z),             \tag{6}
\]

where, according to the first pair's type,

\[
s=\begin{cases}
-(1-2h_7)/\alpha,&\text{type 0},\\
1/\alpha,&\text{type 2},\\
(1-2h_7)/\alpha,&\text{type 3}.
\end{cases}
\]

The determinant of (6) is four. After the table's budget substitution,
all transformed scalar coordinates are polynomial and independent of
`alpha`. The axial coordinates are `(0,alpha,1,1,1,beta,0,0)`.
The companion checks these statements exactly for every family.

Each of the seventy four-point determinants is linear in the five
normal coordinates in (5):

\[
B_{ijkl}=\sum_{v\in\{2,4,5,6,7\}}c_{ijkl,v}N_v.  \tag{7}
\]

Let `Aijk` denote the signed double area of the projected points
`(xi,zi)`. The companion also expands all 560 indexed identities

\[
B_{ijab}A_{ijc}-B_{ijac}A_{ijb}+B_{ijbc}A_{ija}=0, \tag{8}
\]

checking each in all five independent normal coordinates. Ordered
indices retain their permutation parity. Affine five-point determinant
cocycles are included as well.

Every coefficient in (7) or (8) is multilinear in
`alpha,beta,x,y`. The checker verifies the individual degree bounds
and reconstructs each polynomial coefficientwise from its sixteen
exact corner values on `[0,1]^2*[0,1/2]^2`. All interpolation weights
are positive inside the open parameter box. Consequently weakly
positive corner values with at least one positive value give a strict
positive coefficient everywhere; the negative case is identical.
All-zero corner values give an identically zero coefficient. A
parameter absent from a family is simply a harmless dummy variable.

If any coefficient in a relation lacks a uniform sign, the entire
relation is omitted. This only weakens the necessary system. Between
zero and 154 relations are omitted per family. A retained zero-sum
identity requires either all its signed terms to vanish or terms of
both signs. It places no condition on their positive magnitudes.

## 5. Boolean source, replay, and scope

The CNFs retain the full necessary generic embedding and linking
formula, including its orientation unit, and the two strict axial
cuts separating 234 and 067 from the remaining vertices. Each actual
determinant and normal coordinate has positive and negative trit bits;
neither bit means zero. An actual nonzero determinant fixes its generic
completion sign, while an actual zero does not. The last necessary
condition is that at least one normal trit is nonzero, by (5).

All twenty resulting formulas are UNSAT. The independent checker
accepted twenty distinct RUP proofs. The exact producer took 23.83
seconds and independent replay took 1.94 seconds in this workspace.
The producer also records all 108 strict budget exclusions, every
family's coordinate formula, and its omitted-relation count.

```sh
python research/type7_completion/remaining_c1_flat_positive_stretch.py /tmp/type7-c1-flat-positive
python research/type7_completion/solver_cnf_certificates.py /tmp/type7-c1-flat-positive-rup --checker /path/to/solver-check-rup-watched /tmp/type7-c1-flat-positive
```

The [regular-cap section theorem](remaining_c1_sections.md), its
[one-collinear extension](remaining_c1_one_collinear.md), and this
result leave only two-collinear-cap limits having at least one zero
cap edge within interior ray-2 C1. This package does not exclude those
zero-edge strata, any height endpoint, or ray-2 C0.
