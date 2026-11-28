# An opening by successive small folds for Type 5

Let the periods be $1,B=x+iy$, with $0\le x<1/2$, $y>0$, $T=|B|^2\ge1$. This construction gives a Type 5 piecewise-linear isometric embedding at these fixed periods. The parameters are chosen successively small for the particular modulus. This avoids a uniform lower bound on a spatial determinant across moduli.

The spatial criterion used below is the following implication for the labeled Type 5 complex. Write $[ijkl]$ for $\det(r_j-r_i,r_k-r_i,r_l-r_i)$. The following strict signs imply embeddedness of the affine realization.

| | Increasing tetrahedra with the required signs |
|---|---|
| Four core vertices | $1234-,1235+,1245-,1345-,2345+$ |
| One leaf | $0125+,0135-,0234-,0245+,1236-,1247+,1357-,2357-,2456-$ |
| Two leaves | $0246+,0456+,2367-$ |

Here the core vertices are $1,2,3,4,5$. Each of $0,6,7$ joins to all five core vertices. We use the integral shifts of the square marking. The determinant criterion and the marked degree-one development identify the required geometric conclusion from these signs, positive marked face areas and equality of the 24 edge lengths. [Hand proof of the separation criterion](Type5HandProof.md#seven-planes-suffice) · [Development to the lattice quotient](Type5Rectangles.md#from-signs-to-a-torus)

## A planar configuration

Multiply the intrinsic and projected spatial coordinates by $A=(\bar B-B)/B$. The transformed periods are $A$ and $E=\bar B-B$. An original horizontal coordinate $u$ becomes the linear functional $L(q)=\operatorname{Re}(\bar A q)/|A|^2=u$. In these coordinates the real inner product is $v\cdot w=\operatorname{Re}(\bar v w)$. Put $S_v(w)=v\bar w/\bar v$, reflection across the line spanned by $v\ne0$. Let $q_i$ denote intrinsic locations and $r_i$ spatial locations, which initially lie in the plane. Write $(ijk)=\operatorname{Im}(\overline{r_j-r_i}(r_k-r_i))$ for projected double areas. We take successively small positive $d,\lambda,\eta$, in that order. All limits below have that meaning: first consider $d$ near zero with the later parameters zero, then vary $\lambda$, and finally $\eta$.

Set $q_1=r_1=0$, $q_2=r_2=P=B-1+2\lambda$, $q_5=r_5=R=B+2\lambda+2d/B$, and $k=1-2d/T$. In the original dot-product coordinates these assignments say
$$
 p_2\cdot1=w,\quad p_2\cdot B=-T/2,\qquad
 p_5\cdot1=w-1/2,\quad p_5\cdot B=-T/2+d,
 \qquad w=1/2-x-\lambda.
$$
Put $s=\operatorname{Im}(\bar P R)$. Its limiting value is $-y$. Define
$$
 r_3=\frac{R}{k\bar B},\quad q_3=\bar r_3,\qquad
 r_0=\frac{yPR}{s\bar B},\quad q_0=S_P(r_0).
$$
They satisfy
$$
 r_3=\bar q_3=S_R(q_3-A),\qquad
 r_0=S_P(q_0)=S_R(q_0-A).
$$
Indeed the first equality with $S_R$ follows from $R-\bar R=2iyk$, and solving $S_P(q_0)=S_R(q_0-A)$ gives the displayed $r_0$. Both $q_0,q_3$ have $L=1/2$. On that line $q-A=-(A/\bar A)\bar q$, so $S_R(q-A)$ is a fixed rotation of $q$.

Let
$$
 P'=P-A+E,\quad R'=R+E,\quad
 D=\frac{B+2d}{\bar B+2d},\qquad a=R'-R/D .
$$
The direct isometry $V(q)=D(q-a)$ takes $P',R'$ to $P,R$ because $D(P'-R')=P-R$. It also takes $q_0+E-A$ to $r_0$. To check the third image, put $N=P\bar R-\bar P R$ and $\ell=P-R$. The formula for $r_0$ gives $r_0=-PR\bar A/N$ and $q_0=P\bar R A/N$. Since $L(\ell)=1/2$, we have $\ell-A=-(A/\bar A)\bar\ell$, and hence $R\bar A+N=\ell(\bar R+R\bar A/A)$. Combining this identity and its conjugate gives $r_0-P=D(q_0-P)$, with $D=\ell/(\ell-A)$.

Choose $q_4$ by the two real linear equations
$$
 L(q_4)=-\lambda-\eta,\qquad 2a\cdot q_4=|a|^2,
 \qquad r_4=V(q_4).
$$
The second equation gives $|r_4|=|q_4|$. To check transversality and record the needed asymptotics, put $p=B-1$, $S=B/\bar B$, and $\rho=T-2x>0$. We have
$$
 a=(B-\bar B)\frac{2\lambda+2d(1/B-1)}{B+2d}.
$$
At $\lambda=\eta=0$, $q_4$ is a real multiple of $\bar B$, and $\operatorname{Re}(Ba)/d\to4y^2/T>0$. Substitution gives
$$
 q_4/d\longrightarrow 2|p|^2/B,\qquad
 r_4/d\longrightarrow 2p^2/B.
$$

There are two more leaves. Take $r_6=P+e$, $q_6=\bar r_6=r_6+E$, where $e$ is real. The squared-length equation at 4 is
$$
 |P+e-r_4|^2-|\bar P+e-q_4|^2
 =-2|A|^2\eta+2e\operatorname{Re}(q_4-r_4)=0.
$$
Here $V(P')=P$, $P'=\bar P-A$, and $L(q_4)=-\lambda-\eta$ give the constant term. The coefficient $\operatorname{Re}(q_4-r_4)/d$ tends to $4y^2/T>0$ at $\lambda=\eta=0$. In particular $e>0$ and it can be made arbitrarily small after choosing $d,\lambda$.

Take $q_7=S_R(r_7)$. The equations at 2 and 4 become
$$
 2U\cdot r_7=|P'|^2-|P|^2=2|A|^2\lambda,
 \qquad W\cdot r_7=0,\qquad
 U=S_R(P')-P,\quad W=r_4-S_R(q_4).
$$
At $\lambda=\eta=0$, as $d\to0$,
$$
 U\longrightarrow 2iS y\rho/T,\qquad
 W/d\longrightarrow4i pB\operatorname{Im}(p/B^2),\qquad
 \operatorname{Im}(p/B^2)=-y\rho/T^2.
$$
The limiting $U$ has inner product $2y^2\rho/T>0$ with $pB$. The two rows are independent. At $\eta=0$, the successive limit of $r_7/\lambda$, first as $\lambda\to0$ then as $d\to0$, is $2pB/\rho$. These formulas follow by substitution, using $|A|^2=4y^2/T$.

All distances already agree. For example the lifts of the six neighbors of 4 are $0,P',R',q_0+E-A,q_6,q_7$. The three distances to $P',R',q_0+E-A$ follow from $V$, the distance to the origin from its bisector equation, and those to $q_6,q_7$ from their defining equations. At 6 the three points $0,\bar P,q_3$ map by conjugation to $0,P,r_3$, while $q_6,R'$ map by translation by $-E$ to $r_6,R$. At 7 the triple $0,R,q_3-A$ maps by $S_R$ to $0,R,r_3$. At 3 the anchor equations follow from conjugation at 1 and 2, and from $S_R$ at 5. The equations at 0 follow from the two reflections and the common rotation at 0 and 3.

## Orientations at the planar configuration

The limiting projected points at $0,1,2,3,5$ are $-pS,0,p,S,B$. The following table is obtained by taking imaginary parts of pairwise products. The entries in the right column are the limits of the stated projected areas.

| Triples | Limit |
|---|---|
| $123,235$ | $y\rho/T$ |
| $125,135,013$ | $-y$ |
| $012$ | $-2xy|p|^2/T$ |
| $015,035$ | $y(1-2x)$ |
| $025$ | $2xy(1-2x)/T$ |
| $023$ | $2xy\rho/T$ |

For example $p-(-pS)=2xp/\bar B$. This gives $(025)=-\operatorname{Im}(2xp/\bar B)$ since $B-p=1$, and $(023)=2x\operatorname{Im}(\bar pS)$.

When $x=0$, $r_0=P$ at $\lambda=0$ for every $d$. In that case
$$
 r_0-P=-\frac{2\lambda P}{k+2\lambda(1-k)}
             \bigl(1-k+i/y\bigr).
$$
Thus the successive limit of $(r_0-P)/(2\lambda)$ is $1+i/y$. The limits of $(012),(025),(023)$ divided by $2\lambda$ are respectively $-(y+1/y),1/y,y$. Likewise $(024)/(2\lambda)$ tends to $y+1/y$ because $r_4=O(d)$ at $\lambda=0$. This supplies all strict signs from the table at the rectangular boundary.

Here are the remaining comparisons used below. For small positive parameters $(127),(137)>0$, by the limits $\operatorname{Im}(\bar p pB)=y|p|^2$, $\operatorname{Im}(\bar S pB)=y$. The same limit gives $(175)<0$. We have $(026),(236),(256)>0$: dividing by $e$ gives respectively $-\operatorname{Im}(P-r_0)$, $-\operatorname{Im}(r_3-P)$, and $-\operatorname{Im}(R-P)=2dy/T$. For the first one at $x=0$ use the expansion of $r_0-P$. Since $e\to0$ after $\lambda$ is chosen, $(056)<0$ follows from $(025)>0$.

For $(164),(147),(274)$, use $r_4/d\to 2p^2/B$, $r_7/\lambda\to2pB/\rho$, and $r_6\to P$. The first sign is positive because $\operatorname{Im}(\bar p p^2/B)=|p|^2y/T$. The second is positive because $\operatorname{Im}(\overline{p^2/B}\,pB)=|p|^2\operatorname{Im}(\bar pS)>0$. The third is negative, with leading term $-d\operatorname{Im}(2\bar p p^2/B)$ when $\lambda\to0$. These calculations and the table give all sixteen nonzero projected orientations in the face order of the square marking:
$$
 \begin{array}{c|rrrrrrrr}
 f&012&031&024&053&045&152&136&164\\
 \operatorname{sgn}(f)&-&+&+&-&+&+&-&+\\
 f&147&175&263&237&274&256&357&465\\
 \operatorname{sgn}(f)&+&-&-&+&-&+&-&-
 \end{array}
$$

Each marked intrinsic face has positive orientation. One can check this by comparing the signs just listed with the orientations of the plane isometries on those faces. In order, $012,031,024,053,045,152,136$ use $S_P$, the common rotation of $q_0,q_3$, $V$, $S_R$ after translation, $V$, the identity, and conjugation. For 164 the isometry fixing 1 cannot be conjugation, since $r_4\ne\bar q_4$ by their different leading coefficients. Its orientation is positive. For 147 it cannot be $S_R$ since $W\ne0$, so its orientation is positive. Faces 175 and 263 use $S_R$ and conjugation. On 237, the isometry agrees with $S_R$ at $q_3-A,q_7$, and $U\ne0$ excludes agreement at $P'$. Its orientation is positive. On 274 it agrees with $V$ at $P',q_4$. Agreement also at $q_7$ would imply $|q_7-R'|=|q_7-R|$, impossible for $\lambda,\eta$ sufficiently small with $d>0$ fixed: at $q_7=0$ the squared norms differ by $2|A|^2d$. Its orientation is negative. Face 256 uses translation, 357 uses $S_R$, and 465 agrees with $V$ only at $q_4,R'$. Indeed $V(q_6)=q_6-E$ would give $q_6=R'$, since $D\ne1$. Thus its orientation is negative.

## Opening the folds

Continue to write $q_2=P,q_5=R$, with the spatial anchors $0,P,R$ horizontal. For any trial intrinsic point $v=q_i$, its horizontal image $J_i(v)$ is affine in $v$. Subtract the equation for its squared distance to 1 from the equations for its squared distances to 2 and 5; these give its two inner products with $P,R$. The squared height required by the origin is $|v|^2-|J_i(v)|^2$. Throughout the following small perturbations the intrinsic face areas stay positive by continuity.

**First open edge 25.** Decrease the original horizontal coordinate of $p_2$ by $g>0$ while holding $p_2\cdot B=-T/2$. Thus $P$ increases by the real number $2g$. Keep the other anchor fixed, $q_3$ fixed, and $r_3=\bar q_3$. Keep $r_0=S_P(q_0)$. The two remaining equations at 0 to vertices 5 and 3 are linear in $q_0$ upon subtracting its squared distance to 1. At the initial configuration their rows are independent: the equation at 3 is homogeneous with nonzero row $S_P(r_3)-q_3$, since $S_P$ and conjugation are distinct reflections and $q_3\ne0$. The equation at 5 has nonzero constant $-|A|^2w$. They have a common solution, so their rows cannot be proportional. Thus $q_0$ continues uniquely.

To keep the distance to 0 at root 4, impose the corresponding subtracted equation on $J_4(q_4)$. It is affine in $q_4$ because $r_0$ has zero height. Its restriction to the line $L(q_4)=-\lambda-\eta$ has nonzero derivative. Indeed, before this opening, write $r_0=\alpha P+\beta R$; $\alpha+\beta\ne1$ because $(025)\ne0$. Subtract the matching combination of the equations at 2 and 5 from the equation at 0. The lifted locations are $a+D^{-1}r_0,a+D^{-1}P,a+D^{-1}R$, so the result is $(\alpha+\beta-1)(a\cdot q_4-|a|^2/2)=0$, up to overall sign. On the stated line its derivative is nonzero by $\operatorname{Re}(Ba)\ne0$. This proves existence and continuity of the perturbed $q_4$.

The squared height at 4 is now strictly positive. To see this directly, unfold the two intrinsic triangles 024 and 045 along their common side 04. Their vertices 2 and 5 lie on opposite sides because both triangles have positive marked orientation. The squared length between these unfolded vertices exceeds the prescribed squared length $|P-R|^2$ by $2|A|^2g$. For two fixed nondegenerate triangles on opposite sides of a hinge, with perpendicular altitudes $u,v>0$ to that hinge, rotating through angle $\theta$ shortens the opposite squared distance by $2uv(1-\cos\theta)$. The altitudes tend to positive limits as $g\to0$. A sufficiently small positive shortening therefore gives a noncoplanar tetrahedron with precisely the six specified lengths. Align its triangle 025 to $r_0,P,R$. The horizontal position of its fourth vertex agrees with the constructed $J_4(q_4)$, since subtracting pairs of equations at $0,2,5$ gives two independent horizontal equations. Its squared height then agrees with $|q_4|^2-|J_4(q_4)|^2$ by any of the subtracted equations and the distance to the corresponding anchor. Take the negative height.

**Lift vertex 3 and then vertex 0.** While $L(q_3)=1/2$ and $\operatorname{Im}P=y$, the first anchor equation implies $J_3(q_3)-\bar q_3$ is perpendicular to $P$. In the original coordinates the inner product of this difference with $p_5$ is
$$
 1/2-w-(1-2d/T)(p_3\cdot B),
$$
where complex conjugation in the transformed coordinates is reflection across $B^\perp$ in the original ones. This expression has nonzero derivative in the independent coordinate $p_3\cdot B$. At its zero, the derivative of the squared height $|q_3|^2-|J_3(q_3)|^2$ is nonzero, because $\bar q_3$ is not parallel to $P$, as $(123)>0$. We can therefore prescribe an arbitrarily small positive height $z_3$. The two equations at 0 and the equation for $q_4$ just solved remain nonsingular by continuity.

Next rotate the isometry $S_P$ used on face 012 about line 12 through a small angle. Thus $r_0$ is an isometric linear image of $q_0$ in a plane through 12. The two equations to 5 and 3 remain linear in $q_0$ and nonsingular. Either strict height sign at 0 is possible because $(012)\ne0$. Choose the positive sign and an arbitrarily small angle. In the equation to 0 at root 4 there is now the additional product of the heights. Since the chosen squared height at 4 is strictly positive, its negative square root is smooth. The nonzero derivative already proved for this equation gives the adjusted $q_4$ by the implicit function theorem.

**Complete vertices 6 and 7.** Until the last step, $\operatorname{Im}P=y$ and $L(q_3)=1/2$ remain exact. Consequently the intrinsic triples $0,P+E,q_3$ and $0,q_3-A,R$ are congruent to the spatial triples 123 and 135, respectively. Map each intrinsic plane isometrically onto the corresponding spatial plane using the specified triple; the resulting maps depend smoothly on the data. Use the first map on $q_6$ and the second on $q_7$. The two remaining conditions for each leaf are linear in its intrinsic point. Their Jacobians at the original planar configuration are nonsingular. At 6 the equation to 5 puts $r_6$ on $P+\mathbb R$ (here $d\ne0$), and the row to 4 has nonzero derivative $2\operatorname{Re}(q_4-r_4)$ on that line. At 7 the two rows are $U,W$ above. Thus both completions persist through all the preceding perturbations.

We now have all the desired determinant signs except those for $1236,1357$, which vanish because of the two exact plane isometries. Here are the sign checks. Immediately after opening 25, vertex 4 alone has negative height. The ten required brackets containing 4 have the displayed signs by expanding in this height. Their opposite projected triangles in the order of the criterion are $123,125,135,235,023,025,127,256,026,056$. For instance $[0246]=-z_4(026)>0$ and $[0456]=z_4(056)>0$. Next $[1235]=-z_3(125)>0$ and, before lifting 0, $[0135]=-z_3(015)<0$. The fact that 7 lies in plane 135 gives $z_7/z_3=(157)/(153)$. The quotient $[2357]/z_3$ thus extends continuously to zero height at 3. As the projected vertex 7 tends to vertex 1 in the nested planar limit it tends to $[2351]/z_3=(125)<0$. For $[2367]$, the difference of the affine height functions of planes 135 and 123 vanishes on line 13. At 5 it is $-z_3(125)/(123)>0$; at 7 its value is that number times $(137)/(135)<0$. Multiply by $(236)>0$ to obtain $[2367]<0$. These strict signs persist when 0 is lifted sufficiently little, and $[0125]=-z_0(125)>0$.

**Release the two remaining ties.** Increase $p_2\cdot B$ from $-T/2$ by $s^2$ and decrease $p_3\cdot1$ from $1/2$ by $s^2$. Keep their other independent dot products fixed. The two positive root radicands persist. Vertex 0 and root 4 continue by the same linear solve and implicit function theorem as above. The coherent opposite squared distances on hinges 36 and 57 exceed the prescribed distances on 12 and 13, respectively, by $2|A|^2s^2$. In both cases the two unfolded incident triangles have opposite sides at the hinge and positive limiting altitudes.

For clarity, consider leaf 6 with its intrinsic position temporarily free near the tied solution. The two unfolded triangles 136 and 263 determine the four spatial positions up to a rigid motion and a choice of folding direction. If their perpendicular altitudes to 36 are $u,v$, set $\cos\theta=1-|A|^2s^2/(uv)$ and $\sin\theta=\pm s\sqrt{2|A|^2/(uv)-|A|^4s^2/(u^2v^2)}$. These depend smoothly on $s,q_6$. Align the folded triple 123 to the prescribed spatial triple by a direct rigid motion; it is uniquely determined by the two ordered triangle frames and depends smoothly on them. This produces either sign of $[1236]$ for small positive $s$. At $s=0$ both constructions are the plane isometry used above. The last two distance equations still have nonsingular Jacobian in $q_6$, so the implicit function theorem gives a solution on each branch. The identical argument on faces 175 and 357 at hinge 57 gives either sign of $[1357]$ for vertex 7. The leaves have no edge between them and the choices are independent. Take both signs negative.

All inequalities introduced earlier are strict and survive this last small perturbation. The 24 marked lengths now agree on a spatial embedding with all 16 intrinsic faces positively oriented. The marked area formula gives a degree-one development to the prescribed lattice torus. Each pair of corresponding triangles is congruent by its three edge lengths. Undoing the common similarity finishes the construction.

This argument uses the off-ray hypothesis in $1-2x>0$ and $\rho=T-2x>0$. The sharp ray $x=1/2$ has a separate exact arithmetic proof above the hexagonal endpoint. [Sharp-ray proof](Type5SharpEmbeddings.md)

## Lean verification

The reflection and direct-isometry equations at 0 and 3 are checked in `reflected_leaf0` and `reflected_root3`. The identities in the core area table are checked in `limit_area_table`. The limiting bisector equations for vertex 4 are checked in `bisector_model`, the limiting two-row determinant for vertex 7 in `leaf7_limiting_rows`, and their projected directions in `direction_area_table`. The exact rectangular displacement, its joint limit, and the resulting area coefficients are checked in `rectangular_leaf0_difference`, `rectangular_leaf0_limit`, and `rectangular_area_coefficients`. The three marked distance changes are checked in `coherent_gaps`, the linear solve at 0 in `leaf0_nonsingular`, and the nonzero first variation of the squared height at 3 in `root_height_transverse`. The hinge distance and its two strictly nonplanar branches are checked in `hinge_shortening` and `hinge_branches`. The signed sine is jointly smooth through the tie by `hingeSine_smooth`, with its sign and cosine identity in `hingeSine_spec`. The height expansion of every bracket and the determinant identity for the tied leaves 6 and 7 are checked in `height_expansion` and `two_leaf_volume`. The successive small-parameter choices and the implicit-function arguments in this construction still require formalization. [Lean source](../../OrigamiTorus/EightVertex/Type5/OffRayOpening.lean)
