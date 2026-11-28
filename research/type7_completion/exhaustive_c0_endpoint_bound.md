# Excluding the positive mixed branches of regular ray-1 C0

Every regular ray-1 C0 limit satisfies

\[
[2345]\le0,\qquad [4567]\le0.
\tag{1}
\]

The [conditional cone reduction](exhaustive_c0_positive_cones.md) reduces either positive branch to an endpoint inequality. This note proves that inequality uniformly. It leaves the branch in which both actual brackets are nonpositive, including their zero cases.

The proof uses the exact endpoint metric and core identities, the strict turning lemma, and the independently certified conditional signs. No numerical optimization or root search is part of the proof.

## 1. The endpoint inequality

Use the regular ray-1 C0 notation

\[
\begin{gathered}
E=P_3-P_2,\quad F=P_7-P_6,\quad L=d_1+d_2=|P_3|,\quad M=d_6+d_7=|P_6|,\\
h_i=1/2-d_i,\qquad D=d_0+L+M\le1/2,\qquad d_0=h_1h_7+P_2\cdot P_7.
\end{gathered}
\tag{2}
\]

Both endpoint triangles have perimeter one, positive orientation, and positive cap deficits `d1,d2,d6,d7`. Thus `0<L,M<1/2`. The strict turning lemma gives `cross(E,F)>0`.

Suppose `C36=cross(P3,P6)<0` and `c=cross(E,P6)>0`. We prove

\[
R:=\frac{h_2(-C_{36})}{c}<D.
\tag{3}
\]

Rotate the plane preserving orientation so that

\[
E=(H,0),\quad P_3=(x,-y),\quad P_2=(x-H,-y),\quad H=h_2,\quad y>0.
\]

Then

\[
x=\frac{L^2+H^2-h_1^2}{2H},\quad x^2+y^2=L^2,\quad h_1+H+L=1.
\]

The definition of `R` gives

\[
P_6=M\nu,\qquad \nu=\frac{(-(R+x),y)}{n},\qquad n=\sqrt{R^2+2Rx+L^2}.
\tag{4}
\]

For counterclockwise right-angle rotation `J`, direct calculation yields

\[
q(R):=P_2\cdot\nu=\frac{(H-x)R+Hx-L^2}{n},\qquad
P_2\cdot J\nu=\frac{y(H+R)}n>0.
\tag{5}
\]

## 2. A support bound for one triangle

For every `R>=0`, the upper triangle alone implies

\[
\mathcal F(R):=L+\frac{h_1+q(R)}2>\min(R,1/2).
\tag{6}
\]

First, `q(R)>-h1`, because the second expression in (5) is positive. Hence `F(R)>L`, proving (6) for `R<=L`. Differentiation gives

\[
q'(R)=\frac{y^2(R+H)}{n^3}>0,\qquad
q''(R)=\frac{y^2}{n^5}\left(-2R^2-(x+3H)R+L^2-3Hx\right).
\tag{7}
\]

At `R=L`, the parenthesis is `-(L+x)(L+3H)<0`. Its derivative `-4R-x-3H` stays negative for `R>=L`, since `x>-L`. Therefore `F` is increasing everywhere and strictly concave for `R>=L`.

It remains to prove `F(1/2)>1/2`. At that radius, the strict triangle inequality gives positive coordinates

\[
p=n+L-1/2>0,\quad q_*=L+1/2-n>0,\quad s=1-2L>0,\quad p+q_*+s=1.
\]

Put `A=q_*(1+p)+s>0`. The triangle metric gives `H=s/(2A)`, and the following exact identity supplies the strict sign:

\[
2nA\left(q(1/2)-H+L\right)
=q_*\left(q_*(1-q_*)(1+p)+s^2\right)>0.
\tag{8}
\]

The companion verifies (8) rationally, including the substitution for `H` and the norm equation. All factors on its right are nonnegative, and `q_*s^2>0`. Since `h1+H+L=1`, it proves `F(1/2)>1/2`.

Now `F(R)-R` is concave on `[L,1/2]` and strictly positive at both endpoints, hence strictly positive throughout. For `R>=1/2`, monotonicity gives `F(R)>=F(1/2)>1/2`. This proves (6).

## 3. The lower ellipse and its turning endpoint

Keep the upper triangle and the direction `nu` fixed. All positively oriented lower triangles of perimeter one with `P6=M nu` have

\[
P_7=\left(\frac M2+\frac{1-M}{2}\cos\beta\right)\nu
+B\sin\beta\,J\nu,\qquad
B=\frac{\sqrt{1-2M}}2,\quad0<\beta<\pi.
\tag{9}
\]

The side lengths are

\[
h_7=\frac{1-M+M\cos\beta}{2},\qquad
h_6=\frac{1-M-M\cos\beta}{2}.
\tag{10}
\]

Both norm identities and the perimeter identity are checked exactly. At `beta=0`, the lower cap has `d7=0`, `P7=nu/2`, and core value

\[
D_0=L+M+\frac{h_1+q(R)}2=M+\mathcal F(R)>\min(R,1/2).
\tag{11}
\]

There is exactly one `beta_*` in `(0,pi)` for which `cross(E,F)=0`. Write `nu=(nu_x,nu_y)`, where `nu_y>0`, and put `w=tan(beta/2)>0`. Apart from the positive factor `nu_y/(2(1+w^2))`, the second coordinate of `F=P7-P6` is

\[
(1-2M)-w^2+4B(\nu_x/\nu_y)w.
\tag{12}
\]

Its two real roots have negative product, so exactly one is positive. The actual strict turn therefore requires `0<beta<beta_*`.

At `beta_*`, the lower cap is still regular. Its positive orientation forces `F=-h6 E/H`, rather than the positive parallel direction. The outer orientation required by the turning lemma is also strict:

\[
\operatorname{cross}(P_2,-P_7)=\frac{My(H+R)}n+h_6y>0.
\tag{13}
\]

Define `d0_*=h1*h7+P2 dot P7>=0` and `D_*=d0_*+L+M`. Then

\[
D_*>1/2.
\tag{14}
\]

If instead `D_*<=1/2`, the two regular endpoint triangles, their core identity, the outer sign (13), and the nonnegative deficit slack `1/2-D_*` satisfy every premise of the analytic turning argument in sections 1–3 of [exhaustive_c0_turning.md](exhaustive_c0_turning.md). That argument would give `cross(E,F)>0`, contradicting the definition of `beta_*`. Applying that analytic inequality requires no realization of the remaining vertices at a deformed parameter.

## 4. Concavity closes the bound

Let `t=cos(beta)`. The core function is

\[
d_0(t)=\frac{h_1(1-M)+q(R)M}{2}
+\frac{h_1M+q(R)(1-M)}2\,t
+\frac{y(H+R)}n B\sqrt{1-t^2}.
\tag{15}
\]

The last coefficient is positive, so this function is concave on `[-1,1]`. The actual point lies between `t=cos(beta_*)` and `t=1`. At both endpoints, (11) and (14) give `d0+L+M>min(R,1/2)`. Concavity gives the same strict lower bound at the actual point:

\[
D>\min(R,1/2).
\]

Since the actual budget says `D<=1/2`, necessarily `R<1/2`, and then `D>R`. This proves (3), equivalently

\[
D\operatorname{cross}(E,P_6)+h_2C_{36}>0.
\tag{16}
\]

## 5. Consequence for the mixed brackets

Under actual `[2345]>0`, the certified conditional signs in [the cone package](exhaustive_c0_positive_cones.md) give `C36<=0`. Its zero-safe line argument already excludes `C36=0`. For `C36<0`, it gives `cross(E,P6)>0`; its strict cone and (16) then give `|Q4|<2uD`. This contradicts the exact radius

\[
|Q_4|=d_4+d_5+2uD\ge2uD.
\]

Thus actual `[2345]>0` is impossible. The checked marked reflection `i -> 1-i mod8` transfers the argument to `[4567]>0`, proving (1). The proof is uniform over `0<u<v<1/2`; the other height order was already excluded. The residual regular C0 problem retains both actual weak inequalities in (1), including every compatible generic completion of their zero cases.

## Reproduction

```sh
python research/type7_completion/exhaustive_c0_endpoint_bound.py
python research/type7_completion/exhaustive_c0_positive_cones.py /tmp/c0-positive-cones
python research/type7_completion/solver_cnf_certificates.py /tmp/c0-positive-cones-rup \
  --checker /tmp/type7-rup-check /tmp/c0-positive-cones
```

The checker replays the source metric and turning bindings, the conditional-cone identities and marked reflection, the support derivatives and positive identity (8), both ellipse norms, the half-angle polynomial (12), and the boundary outer-sign identity (13). The topology obligation is the single separately checked CNF. The concavity arguments above are analytic proofs, not numerical acceptance criteria.
