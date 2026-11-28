# Uniform quartic certificates for regular C0

Fourteen exact identities exclude all twenty-six regular ray-1 C0 generic
completions left after the middle-wedge argument, uniformly on the open
height region `0<u<v<1/2`. The hypotheses are the ray-1 C0 metric equations,
nonnegative deficits summing to `1/2`, and the weak actual signs supplied by
one of the remaining generic completions. Actual zero brackets are allowed.

The certificate data contain integer identities. Their verifier expands
every term in independent coordinates and checks exact cancellation. Neither
floating-point feasibility, a numerical rank, nor an optimizer status is an
accepted proof. The final finite source cover is a separate CNF obligation
that requires independent RUP replay.

## 1. Twelve equations in planar coordinates

Set `P0=P1=0`, `h_i=1/2-d_i`, and

\[
\begin{gathered}
L=d_1+d_2,\quad M=d_6+d_7,\quad D=d_0+L+M,\\
E=P_3-P_2,\quad F=P_7-P_6,\qquad
\ell_u=1-2u,\quad\ell_v=1-2v,\\
Q_4=P_4-2uP_3-\ell_uP_6,\qquad
Q_5=P_5-2vP_3-\ell_vP_6,\\
r=h_3-\ell_uD,\quad s=h_5-2vD,\\
S=\ell_vQ_4-\ell_uQ_5,\qquad W=vQ_4-uQ_5.
\end{gathered}
\]

The seven cap and core equations are

\[
\begin{gathered}
|P_2|^2=h_1^2,\quad |E|^2=h_2^2,\quad |P_3|^2=L^2,\\
|P_7|^2=h_7^2,\quad |F|^2=h_6^2,\quad |P_6|^2=M^2,\\
P_2\cdot P_7=d_0-h_1h_7.
\end{gathered}
\tag{1}
\]

The five middle equations are

\[
\begin{gathered}
|Q_4|^2=r^2,\quad |Q_5|^2=s^2,\quad
Q_4\cdot Q_5=-rs+d_4,\\
E\cdot S=h_2(\ell_vr+\ell_us)-\ell_v(h_2-d_3),\\
F\cdot W=h_6(vr+us)-u(h_6-d_5).
\end{gathered}
\tag{2}
\]

The companion independently checks the six cap rows and the core row
`T01-T02-T17+T27` against the original twenty-nine-row system. It calls
the existing [full metric binding](remaining_c0_height_order.md) for (2),
then checks all homogenization factors below. These equations are necessary
also on closed deficit faces; no pivot division is made here.

## 2. Nonnegative quadratic factors

The factors used in a positive certificate term are:

- `d_i*d_j`, for `i<=j`;
- squared norms `|P_i-P_j|^2`;
- optionally, squared norms `|P_i+P_j|^2`;
- the four quadratic expressions

\[
\begin{gathered}
D^2-|P_6-P_3|^2,\qquad h_3^2-|P_4-P_3|^2,\\
h_4^2-|P_5-P_4|^2,\qquad h_5^2-|P_6-P_5|^2.
\end{gathered}
\tag{3}
\]

The first factor in (3) is nonnegative by
`|P6-P3|<=L+M<=D`. The remaining three follow from the exact
[section identities](solver_remaining_c0_sections.md), as follows. For the
bilinear form `((t,x),(s,y)) -> t*s-x·y`, let

\[
T=(D,P_6-P_3),\quad a=(r,Q_4),\quad b=(s,-Q_5).
\]

Here `T` is future causal, `a,b` are future null, and
`<a,b>=d4>=0`. The radii are nonnegative because

\[
r=d_4+d_5+2uD,\qquad s=d_3+d_4+\ell_vD.
\]

Thus `a+lu*T=(h3,P4-P3)` and
`b+2v*T=(h5,P6-P5)` are future causal. Moreover, for `K=v-u>0`,

\[
c=a+b+2KT=(1/2+d_4,P_4-P_5),\qquad
\langle c,c\rangle
=2d_4+4K\langle T,a+b\rangle+4K^2\langle T,T\rangle\ge2d_4.
\]

Consequently the third expression in (3) is
`<c,c>-2d4>=0`. This weak argument also holds when a cap is collinear;
it does not rely on extending a strict regular-cap claim by assertion.
For two regular positive caps the existing strict core inequality makes
all four expressions in (3) strictly positive.

## 3. Uniform height coefficients and raw brackets

There are twenty-three formal variables: the twelve coordinates of
`P2,...,P7`, the eight deficits, and three height variables

\[
a=2u>0,\qquad b=2(v-u)>0,\qquad c=1-2v>0.
\]

Write `H=a+b+c` and `T=2*sum(d_i)`. For the actual normalized geometry,
`H=T=1`. To retain homogeneous exact polynomials, the verifier uses
`h_i=sum(d)-d_i` and replaces each occurrence of a scalar linear
constant in (1)–(2) by the appropriate power of `T`. It uses

\[
\begin{aligned}
\overline Q_4&=HP_4-aP_3-(b+c)P_6,&
\overline r&=Hh_3-(b+c)D,\\
\overline Q_5&=HP_5-(a+b)P_3-cP_6,&
\overline s&=Hh_5-(a+b)D.
\end{aligned}
\]

The upper middle dot equation has the added term
`c*H*T*(h2-d3)`; the lower one has `a*H*T*(h6-d5)` and is twice
the normalized lower equation. The verifier checks these five identities
exactly after `a=2u,b=2(v-u),c=1-2v,sum(d)=1/2`.

The formal raw brackets are determinants of the eight points

\[
(P_i,\overline z_i),\qquad
\overline z=(0,H,H,H,a,a+b,0,0).
\]

They are `2H` times the normalized physical raw brackets. This common
factor is positive. All seventy determinant bindings are expanded exactly;
no differently scaled minor magnitudes are mixed. A generic sign `s_q`
supplies precisely `s_q*overline B_q>=0`.

## 4. The exact contradiction

Let `A_ij=cross(P_i,P_j)`, `2<=i<j<=7`. Each stored identity has the form

\[
\sum_k w_k E_k A_{i_kj_k}m_k(a,b,c)
+\sum_l v_l\,s_{q_l}\overline B_{q_l}\,
      G_l(P,d)\,t_l=0.
\tag{4}
\]

Here `E_k` is one of the twelve equations, `w_k` is any integer,
`v_l` is a positive integer, `G_l` is a quadratic factor from Section 2,
and `t_l` is one of `a,b,c`. The cap equations have degree-two height
multipliers `m_k`; the five middle equations already have height degree
two. Every term therefore has degree four in planar coordinates and
deficits and degree two in height variables.

The first sum vanishes on every metric solution. Every term in the second
sum is nonnegative. The checker also requires at least one strictly
positive term. For regular caps, a bracket containing all of `123` or
all of `067` is nonzero, because the fourth point has a different axial
height. Products of `d1,d2,d6,d7` are strictly positive, as are the six
cap side norms. The three previously proved turning brackets and (3)
provide additional valid strict factors.

Thus (4) is a contradiction. This reasoning does not replace any generic
sign by a strict actual sign. Only a factor with a separately proved
nonvanishing property is used for strictness.

For each certificate the replay output additionally lists all terms that
are already strict using only the upper regular cap, and all terms strict
using only the lower regular cap. Since the other factors remain
nonnegative on closed cap faces, these are reusable boundary implications
under the certificate's complete required weak sign set. They do not by
themselves prove that a degenerate cap has the regular finite sign cover.

## 5. Finite coverage and reflection

The [opposite-cone proof](solver_remaining_c0_opposite_cones.md) leaves
forty-two generic completions. The
[middle-wedge proof](solver_remaining_c0_middle_wedge.md) excludes sixteen
of them, leaving twenty-six. The producer regenerates this exact source
and all twenty-six words. It tests each word against every required
certificate sign, both directly and after the marked reflection
`p(i)=1-i mod 8`.

This reflection has been checked against both marked cocycles. Reversing
one transverse coordinate and the axial coordinate preserves spatial
orientation. It sends `(u,v)` to `(1/2-v,1/2-u)`, preserving the open
height triangle, and swaps the endpoint caps. Its source and geometric
checks are replayed again by this producer.

Every claimed covered word records its exact certificate and reflection
choice. Blocking the complete twenty-six-word source produces a separate
CNF; independent RUP replay binds the finite cover to the original
topological, circuit and linking constraints. The manifest reports any
uncovered words explicitly and asserts whole regular-interior exclusion
only when that list is empty.

```sh
# Exact identities and their source bindings, with no LP search:
python research/type7_completion/solver_remaining_c0_quartic.py

# Also regenerate the finite coverage obligation:
python research/type7_completion/solver_remaining_c0_quartic.py OUTPUT

python research/type7_completion/solver_cnf_certificates.py PROOFS \
  --checker CHECKER OUTPUT
```

The conclusion concerns regular ray-1 C0 limiting configurations. Height
boundaries, collinear caps, the compactness bridge, and finite-height Lean
statements retain their separate proof obligations.

## 6. Reproducible discovery and performance

The optional `solver_remaining_c0_quartic_discover.py` constructs the
same polynomial cone directly from the replay source. Planar quartics of
the form `dot*cross` span a 210-dimensional space. An exact rational
row reduction chooses coordinate monomials that determine such a
polynomial. The products of a planar area and two deficits contribute
another `15*36=540` coordinates. Six degree-two height monomials give
`(210+540)*6=4500` coefficient rows; one more row normalizes the sum
of strict residual coefficients.

The original cone has 705 free equation multipliers and 12,810
nonnegative multipliers. A zero-objective HiGHS interior-point feasibility
solve is bounded by a supplied time limit. It found the thirteen ordinary
reflection representatives in roughly 8–12 seconds each. Adding the
fifteen squares `|Pi+Pj|^2` gives 3,150 additional nonnegative columns;
this changed formulation found the last representative in 11.42 seconds.
Merely raising the height multiplier degree had not produced that result
within a separate 45-second diagnostic bound.

Numerical output only suggests a support. A floating-point pivot choice
selects a candidate square integer subsystem. FLINT solves that subsystem
over the rationals; the producer rejects any negative required weight.
It clears denominators and invokes the independent full-coordinate
verifier on the resulting integer identity. In particular, all monomial
rows omitted by the discovery projection are restored for acceptance.

Optional producer dependencies are `numpy`, `scipy`, `highspy`, `sympy`
and `python-flint`. They are unnecessary for polynomial replay. A source
JSON must contain the exact `remaining_words` list, so an index is always
bound to a full seventy-sign word in the output packet.

```sh
python research/type7_completion/solver_remaining_c0_quartic_discover.py \
  c0_opposite_cones.json 0 word0.json --seconds 30

python research/type7_completion/solver_remaining_c0_quartic_discover.py \
  c0_opposite_cones.json 32 word32.json --seconds 30 --extra-squares
```
