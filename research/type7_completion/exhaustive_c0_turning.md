# A strict metric turn in the regular ray-1 C0 limit

For a regular ray-1 C0 limit, the projected metric and the common
topological sign $[0127]\le0$ imply

$$
 [2367]>0,\qquad [0237]>0,\qquad [1267]<0.                 \tag{1}
$$

These strict signs reduce the complete 669-model C0 cover to 202
models. In addition, if the limiting intermediate heights agree,
$u=v$, then the combination

$$
 [2345]\le0,\qquad [4567]\le0                            \tag{2}
$$

is impossible. This removes 152 of the 202 models on the diagonal,
leaving 50. Neither statement excludes all C0 limits.

The companion verifies the exact metric and determinant identities
used below and exports complete finite covers after both reductions.
The angle argument is an analytic proof; no numerical angle test or
nonlinear solver result is used.

## 1. Deficits and the two tip angles

Write

$$
 d_i=1/2-h_i,\qquad s_i=2d_i.
$$

The ray-1 length sum gives $s_i\ge0$ and $\sum_i s_i=1$.
The endpoint triangles have sides

$$
 (h_1,h_2,L),\qquad (h_6,h_7,M),\qquad
 L=d_1+d_2,\quad M=d_6+d_7.
$$

Both triangles have perimeter one. Their noncollinearity is
equivalent, under the deficit sum, to
$s_1s_2s_6s_7>0$. In particular all four side lengths used below
are positive, and both $1-s_1-s_2$ and $1-s_6-s_7$ are positive.

Let $A$ be the interior angle at vertex 2 of triangle 123 and let
$B$ be the interior angle at vertex 7 of triangle 067. The half-angle
formula gives

$$
 A/2=F(s_1,s_2),\qquad B/2=F(s_6,s_7),\qquad
 F(a,b)=\arctan\sqrt{\frac{ab}{1-a-b}}.                   \tag{3}
$$

The core C0 stress is exactly

$$
 d_0=h_1h_7+P_2\mathbin{\cdot}P_7.                       \tag{4}
$$

Define the edge vectors

$$
 E_1=P_2,\quad E_2=P_3-P_2,\quad
 E_6=P_7-P_6,\quad E_7=-P_7.
$$

The certified sign $[0127]\le0$ says
$\operatorname{cross}(E_1,E_7)\ge0$. Let $\phi$ be the
counterclockwise angle from $E_1$ to $E_7$, initially in $[0,\pi]$.
Equation (4) yields

$$
 \tan^2(\phi/2)=\frac{s_0}{D},\qquad
 D=s_2+s_3+s_4+s_5+s_6+s_1s_7>0.                        \tag{5}
$$

The positive denominator rules out $\phi=\pi$, so the formula is
valid also when $s_0=0$ and $\phi=0$.

## 2. Merging the two half-angles

The following elementary inequality is also used in the C1 turning
argument:

$$
 F(a,b)+F(c,d)\le F(a+c,b+d)
 \quad\text{if }a,b,c,d\ge0,\quad a+b+c+d<1.             \tag{6}
$$

Here is a proof that keeps track of the tangent branch. Put

$$
 \alpha=\sqrt{ab},\quad\beta=\sqrt{cd},\quad
 P=\sqrt{1-a-b},\quad Q=\sqrt{1-c-d},\quad
 R=\sqrt{1-a-b-c-d}.
$$

We have $Q\ge\alpha$, $P\ge\beta$, and $P+R,Q+R\le2$.
Consequently

$$
 Q(P-R)=\frac{Q(c+d)}{P+R}\ge\alpha\beta,
 \qquad P(Q-R)\ge\alpha\beta.
$$

Thus $PQ-\alpha\beta\ge R\max(P,Q)>0$. The sum of the two
arctangents is below $\pi/2$, and its tangent is at most

$$
 \frac{\alpha Q+\beta P}{R\max(P,Q)}
 \le\frac{\alpha+\beta}{R}
 \le\frac{\sqrt{(a+c)(b+d)}}{R}.
$$

The last step is Cauchy–Schwarz. This proves (6).

For (3), set

$$
 U=s_1+s_6,\qquad V=s_2+s_7,\qquad
 W=1-U-V=s_0+s_3+s_4+s_5.
$$

The decisive strict inequality is

$$
 D-UV
 =s_2(1-s_1-s_6)+s_6(1-s_7)+s_3+s_4+s_5>0.             \tag{7}
$$

All terms are nonnegative, and regularity makes the first two
strictly positive. If $W>0$, equations (5)–(7) and $W\ge s_0$
give

$$
 \tan F(U,V)\tan(\phi/2)
 =\sqrt{\frac{UVs_0}{WD}}<1.
$$

Together with (6), this proves

$$
 0<A+B+\phi<\pi.                                       \tag{8}
$$

The boundary $W=0$ requires a separate sentence, not division by
$W$. It has $s_0=0$ and $\phi=0$. Put
$S_1=s_1+s_2$ and $S_2=s_6+s_7$, so $S_1+S_2=1$.
The product of the tangents in (3) has square

$$
 \frac{s_1s_2s_6s_7}{S_1S_2}<1,
$$

because $s_1s_2<S_1$ and $s_6s_7<S_2$. Hence (8) holds
on this boundary too.

## 3. The strict bracket signs

Both endpoint triangles have positive projected orientation.
The counterclockwise turn from $E_1$ to $E_2$ is $\pi-A$;
the counterclockwise turn from $E_6$ to $E_7$ is $\pi-B$.
Therefore the oriented angle from $E_2$ to $E_6$, modulo $2\pi$,
is $A+B+\phi$. Equation (8) gives

$$
 \operatorname{cross}(E_2,E_6)>0.
$$

It also gives
$\operatorname{cross}(E_2,P_7)>0$ and
$\operatorname{cross}(P_2,E_6)<0$, using respectively the
angles $A+\phi$ and $B+\phi-\pi$.

Direct determinant expansion in the C0 height chart gives

$$
 2[2367]=\operatorname{cross}(E_2,E_6),\quad
 2[0237]=\operatorname{cross}(E_2,P_7),\quad
 2[1267]=\operatorname{cross}(P_2,E_6).
$$

This proves (1). All three determinants have nonzero limits, so
their generic signs are fixed for sufficiently late members of an
original sequence. The filter therefore retains 202 of the complete
669 generic models. Cell 15 has no surviving model.

## 4. A further contradiction when the heights agree

Now suppose $u=v\in(0,1/2)$ and set $Y=P_5-P_4$. The middle
metric equation and the two cross stresses reduce exactly to

$$
 |Y|=h_4,\qquad
 E_2\mathbin{\cdot}Y=h_2h_4-d_3,\qquad
 E_6\mathbin{\cdot}Y=h_6h_4-d_5.                        \tag{9}
$$

Regularity implies $h_4>0$: otherwise $d_4=1/2$ would force
all four positive cap deficits to vanish.

The deficit budget gives the strict estimate

$$
 \frac{d_3}{h_2}+\frac{d_5}{h_6}<2h_4.                 \tag{10}
$$

An explicit nonnegative decomposition of its gap is

$$
 2h_4-\frac{d_3}{h_2}-\frac{d_5}{h_6}
 =2(d_0+d_1+d_7)
  +2d_2\left(1-\frac{d_3}{h_2}\right)
  +2d_6\left(1-\frac{d_5}{h_6}\right)>0.
$$

The two parenthesized factors are nonnegative since
$d_2+d_3\le1/2$ and $d_5+d_6\le1/2$, and $d_1,d_7>0$.

Assume (2). The exact bracket formulas

$$
 [2345]=\frac{1-2u}{2}\operatorname{cross}(E_2,Y),
 \qquad [4567]=u\operatorname{cross}(Y,E_6)
$$

make both cross products nonpositive. Let $\psi,\theta\in[0,\pi]$
be the clockwise turns $E_2\to Y$ and $Y\to E_6$.
Equations (9)–(10) imply

$$
 \cos\psi+\cos\theta
 =2-\frac{d_3/h_2+d_5/h_6}{h_4}>0.
$$

For two angles in $[0,\pi]$, this forces $\psi+\theta<\pi$.
The total clockwise turn then gives
$\operatorname{cross}(E_2,E_6)\le0$, contradicting (1).
This proof includes zero cross products in (2); it does not replace
weak signs by strict signs.

Thus an actual regular diagonal limit has $[2345]>0$ or
$[4567]>0$. Exactly 50 of the 202 generic models can satisfy this
disjunction. The argument concerns equal limiting heights and does
not assume exact equality at every finite member of the sequence.

## Reproduction and scope

    python research/type7_completion/exhaustive_c0_turning.py

    python research/type7_completion/exhaustive_c0_turning.py /tmp/type7-c0-turning --cells /tmp/type7-c0-cells/c0_full_cells.json

The optional export contains 18 complete uniform covers and
18 complete diagonal covers, to be replayed with
solver_cnf_certificates.py and the independent RUP checker.
The algebraic verifier checks the deficit factorizations, half-angle
identities, core and diagonal metric identities, and all determinant
orientation factors.

The [diagonal certificate package](exhaustive_c0_diagonal.md) now
excludes all 50 diagonal models while retaining the actual strict
disjunction. The off-diagonal 202-model problem and degenerate-cap or
height-endpoint limits require additional arguments. The strict turn
theorem uses ray 1's deficit sum and makes no corresponding claim for
ray 2.
