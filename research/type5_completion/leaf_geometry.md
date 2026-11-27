# Type 5 leaf geometry: reflection pairs and tangent hinges

This is a geometric hand proof, with exact algebra and incidence checks. It
excludes no F1 cell. Its main positive conclusion is that a fixed core with
strictly positive five-cycle deficits automatically admits two real local
leaf completions. Any obstruction must involve additional geometric
conditions or the compatibility of the three leaves.

Throughout, a **local completion** specifies both the spatial position and
the intrinsic position of one leaf, and satisfies its five incident
squared-length identities. It need not preserve face orientation, give a
valid intrinsic triangulation, or extend to an embedded torus.

## 1. Statements and geometric premises

The Type 5 anchors are $1,2,5$, the roots are $3,4$, and the leaves are
$0,6,7$. Every leaf is adjacent to all five core vertices. For a particular
leaf, choose coherent intrinsic lifts $s_i\in\mathbb R^2$ of those five
vertices, and let $r_i\in\mathbb R^3$ be their spatial positions. Put

$$
K_i=(r_i,s_i)\in V=\mathbb R^{3,2},\qquad
Q(r,s)=|r|^2-|s|^2,
$$

and let $B$ be the symmetric bilinear form associated with $Q$.
The five leaf equations for $Z=(r,s)$ are simply

$$
Q(K_i-Z)=0\qquad(0\le i\le4).
$$

Define the matrix of pairwise deficits by

$$
S_{ik}=-\frac12Q(K_i-K_k)
       =\frac{|s_i-s_k|^2-|r_i-r_k|^2}{2}.
$$

**Positive completion theorem.** For any five points $K_i\in V$, suppose
their deficit matrix, after relabeling, is a five-cycle with all five
weights positive. Then their affine span is a four-dimensional hyperplane
with signature $(2,2)$. Its normal line is spacelike: every nonzero normal
$N$ satisfies $Q(N)>0$. The five leaf equations have exactly two distinct
real solutions, reflected across this hyperplane. Writing

$$
c_0=\boldsymbol 1^T S^{-1}\boldsymbol 1,
$$

one has $c_0>0$, and their signed squared separation is $4/c_0>0$.
No pre-existing leaf is assumed in this theorem.

**Embedded Type 5 corollary.** In an embedded, facewise isometric Type 5
flat torus, every leaf has four strictly positive cycle weights. The fifth
is the contraction slack for the coherent root-root lift and is nonnegative.
If it is positive, the completion theorem applies. If it vanishes, the four
subtracted leaf equations still have rank four and a spacelike normal line,
but the remaining quadratic has exactly one solution, a double root.
Among the three leaves, at most one has this latter behavior.

These conclusions use global contraction of the lifted isometric map,
injectivity on the quotient, strict support at the universal vertices, and
nondegeneracy of clique tetrahedra. The strict-support and K4 premises have
the hand proof with checked finite incidences in [coverage.md](coverage.md).
The rank-four conclusion below is derived directly; it does not assume the
earlier LeafRank result. The argument applies to every modulus and Type 5
marking, including all five F1 endpoint cells. It requires no fixed positive
margin and makes no assertion about degenerate limits that cease to be
embeddings.

## 2. The weighted five-cycle

For an actual leaf $Z$, let $Y_i=K_i-Z$. Since $Q(Y_i)=0$,

$$
B(Y_i,Y_k)=S_{ik}.
$$

The diagonal and consecutive entries in the five-cycle link vanish by face
isometry. Every other entry is nonnegative by global contraction. Four of
these five nonconsecutive pairs are actual edges of the triangulation; their
deficits are strictly positive. Indeed, if one such entry vanished, use its
unique middle vertex on the two-edge link arc. All three pairwise signed
products of these neighbor vectors would then vanish, so their spatial Gram
matrix would equal their intrinsic planar Gram matrix. The leaf and those
three neighbors form a K4, which would be coplanar, contradicting strict K4
nondegeneracy. The only remaining pair is $3,4$.

In complement-cycle order the matrix is

$$
S=\begin{pmatrix}
0&a&0&0&e\\
a&0&b&0&0\\
0&b&0&c&0\\
0&0&c&0&d\\
e&0&0&d&0
\end{pmatrix},
\qquad a,c,d,e>0,\quad b\ge0.
$$

Here the root vertices occupy positions $1,2$, and $b$ is their slack.
The actual relabelings, checked against the Lean face list, are:

| Leaf | Matrix order | Universal neighbor between roots in the link |
|---|---|---|
| $0$ | $(2,3,4,1,5)$ | $5$ |
| $6$ | $(5,3,4,2,1)$ | $1$ |
| $7$ | $(1,3,4,5,2)$ | $2$ |

For $b>0$, positive diagonal scaling gives $S=DCD$, where $C$ is the
unweighted five-cycle adjacency matrix. For example, start with
$D_{00}^2=ace/(bd)$ and determine the other positive diagonal entries
successively from the first four edge weights. The fifth then agrees.
The characteristic polynomial of $C$ is
$(x-2)(x^2+x-1)^2$, so its inertia, and that of $S$, is $(3,2)$.
Also $\det S=2abcde$. When $b=0$, positive diagonal scaling instead gives
the adjacency matrix of a five-vertex path, with inertia $(2,2,0)$.

## 3. The positive inverse sum

For every positive weighted five-cycle,

$$
\boxed{\quad \boldsymbol 1^T S^{-1}\boldsymbol 1>0.\quad}
$$

To prove this, put $q=D^{-1}\boldsymbol 1>0$. The matrix $H=2C^{-1}$,
a permutation of the Horn matrix, is

$$
H=\begin{pmatrix}
1&1&-1&-1&1\\
1&1&1&-1&-1\\
-1&1&1&1&-1\\
-1&-1&1&1&1\\
1&-1&-1&1&1
\end{pmatrix},\qquad H\boldsymbol 1=\boldsymbol 1.
$$

Its negative entries form the complementary five-cycle, denoted $E_-$.
For any vector $z\ge0$, with $T=\sum_i z_i$,

$$
z^THz=T^2-4\sum_{\{i,k\}\in E_-}z_i z_k\ge0.
$$

Here is an elementary proof of the inequality. If $T=0$, it is immediate.
Otherwise normalize to $T=1$, maximize the edge sum on the compact simplex,
and choose a maximizer with smallest support. If its support contains two
nonadjacent vertices, move their combined mass to whichever has the larger
sum of neighboring weights. There is no product between these two masses,
so this does not decrease the objective and strictly reduces the support.
That contradicts minimality. The support is therefore a clique. A five-cycle
has no triangle, and the product of two nonnegative numbers with sum one is
at most $1/4$.

Now write $q=m\boldsymbol 1+z$, where $m=\min_iq_i>0$ and $z\ge0$.
Since $H\boldsymbol 1=\boldsymbol 1$,

$$
q^THq=z^THz+2m\sum_i z_i+5m^2>0.
$$

Thus $c_0=q^TC^{-1}q=\tfrac12q^THq>0$. This proof allows every finite
choice of positive weights; none is bounded away from zero.

## 4. Two completions from any positive core

This proves the positive completion theorem without starting from an actual
leaf. In the coefficient space $\mathbb R^5$, let

$$
U=\{h:\boldsymbol 1^Th=0\},\qquad
w=\frac{S^{-1}\boldsymbol 1}{c_0}.
$$

Then $\boldsymbol 1^Tw=1$, $w^TSw=1/c_0>0$, and $w$ is
$S$-orthogonal to $U$. Since $S$ has inertia $(3,2)$, its restriction
to $U$ is nondegenerate with inertia $(2,2)$.

For $h\in U$, expansion of the squared differences gives

$$
Q\left(\sum_i h_iK_i\right)=h^TSh.
$$

The corresponding bilinear identity shows that the map
$h\mapsto\sum_i h_iK_i$ is injective on $U$. Thus the core differences
span a four-space $W$ of signature $(2,2)$, and $W^\perp$ is a
positive one-dimensional space.

The point $Z_0=\sum_i w_iK_i$ lies in the affine core hyperplane. Its
barycentric coefficients may have either sign. Since $Sw=\boldsymbol 1/c_0$,
the affine squared-distance identity gives, for every $i$,

$$
\begin{aligned}
Q(K_i-Z_0)
&=\sum_k w_k Q(K_i-K_k)
 -\frac12\sum_{k,l}w_kw_lQ(K_k-K_l)\\
&=-2(Sw)_i+w^TSw=-\frac1{c_0}<0.
\end{aligned}
$$

Subtracting any two leaf equations forces a candidate to have the same
signed distance from all five core points. These four independent affine
equations define the normal line $Z_0+\mathbb RN$, where $N\ne0$ and
$Q(N)>0$. On this line, the remaining equation is

$$
-\frac1{c_0}+t^2Q(N)=0.
$$

Consequently its complete solution set consists of

$$
Z_\pm=Z_0\pm\frac{N}{\sqrt{c_0Q(N)}}.
$$

Reflection in the affine core hyperplane interchanges these two points and
fixes every $K_i$. Their signed separation is

$$
Q(Z_+-Z_-)=\frac4{c_0}>0.
$$

In particular, a single distance-nonincreasing map cannot contain both
completions with these intrinsic lifts: their spatial separation is strictly
larger than their intrinsic separation. This does not choose which candidate
can belong to a torus.

For comparison with an existing leaf $Z$, the five null vectors $Y_i$
form a basis. The normal

$$
N_* =\sum_i (S^{-1}\boldsymbol 1)_iY_i
$$

satisfies $B(N_*,Y_i)=1$ and $Q(N_*)=c_0$. On $Z+tN_*$, the equation
becomes $-2t+c_0t^2=0$; its roots are $0$ and $2/c_0$. This is the same
reflection pair expressed from one endpoint.

## 5. A saturated root lift gives one tangent completion

This part assumes an actual embedded realization; the positive-core theorem
alone does not supply the singular geometric premises.

When $b=0$, the deficit matrix has kernel

$$
\lambda=(0,-e/a,-d/c,0,1).
$$

Its rank is four: the principal minor on indices $0,1,2,3$ is $a^2c^2>0$,
and the displayed vector lies in its kernel. The five $Y_i$ cannot span all
of $V$, which would make their Gram matrix invertible. Their Gram rank is
four, so they span exactly a four-dimensional nondegenerate space $W$ of
signature $(2,2)$. The kernel relation is therefore a vector relation:

$$
Y_4=\alpha Y_1+\beta Y_2,\qquad
\alpha=e/a>0,\quad\beta=d/c>0.
$$

Indices $1,2$ are the roots $3,4$; index $4$ is the universal vertex
$M$ in the table above. For the leaf $j$, the spatial relation is

$$
r_M=\alpha r_3+\beta r_4+(1-\alpha-\beta)r_j.
$$

Strict support at $M$ forces $\alpha+\beta>1$. Otherwise $M$ would be a
convex combination of its three neighbors $3,4,j$, contrary to a strictly
supporting functional. Hence $\sum_i\lambda_i\ne0$. Normalizing the kernel
relation by this sum shows that zero belongs to the affine span of the
$Y_i$. Equivalently, $Z$ belongs to the affine core hyperplane, and the
four core differences span all of $W$.

The normal line $W^\perp$ is again spacelike. On the complete affine solution
line $Z+tN$, the remaining equation is now

$$
Q(K_i-Z-tN)=t^2Q(N)=0.
$$

There is exactly one local completion, with multiplicity two. This conclusion
uses no division by $b$ and leaves no extra rank stratum.

The relation also describes the spatial geometry. The root segment meets
the interior of the distinguished hinge edge $jM$, because

$$
\frac{\alpha r_3+\beta r_4}{\alpha+\beta}
=\frac{r_M}{\alpha+\beta}
 +\frac{\alpha+\beta-1}{\alpha+\beta}r_j.
$$

Both sides are strict convex combinations. The two faces $jM3$ and $jM4$
are therefore coplanar with their roots on opposite sides of $jM$: this
hinge is unfolded. Conversely, an unfolded pair preserves its coherent
root-root distance, so its slack is zero. The root segment is a missing
diagonal, so this crossing is not itself a surface intersection.

## 6. The three root lifts are distinct in every marking

Use the actual dual cocycle from
[WindingCocycle.lean](../../OrigamiTorus/Winding/WindingCocycle.lean), in the
basis of cycles $014,015$. If $K(u,v)$ denotes its directed edge period,
the coherent displacement of root $4$ from root $3$ through leaf $j$
has period part

$$
q_j=K(j,4)-K(j,3).
$$

Direct substitution in that source gives

$$
(q_0,q_6,q_7)=((0,0),(1,0),(1,-1)),
\qquad
\begin{pmatrix}q_0-q_6\\q_7-q_6\end{pmatrix}=-I_2.
$$

Their two differences therefore form an integral basis. The existing theorem
`cocycle_eq_mapPeriod` expresses any tree-normalized cocycle through this
dual cocycle. If its marking is $M$, the difference matrix becomes $-M$,
with determinant $\det M$. The existing
`marking_unimodular_of_quotient` in
[WindingGeneration.lean](../../OrigamiTorus/Winding/WindingGeneration.lean)
gives $|\det M|=1$ for coherent quotient data. A vertex gauge changes all
three $q_j$ by the same vector, so their differences are unaffected.
This proves the assertion for arbitrary valid Type 5 markings, without a
restriction to the sharp representative.

The exact checks also replay every actual archived Type 5 marking against
the Lean representative lists:

| Region/representative | Marking rows | Ungauged $(q_0,q_6,q_7)$ | Difference determinant |
|---|---|---|---|
| Interior 1 | $(-1,-1),(-1,0)$ | $(0,0),(-1,-1),(0,-1)$ | $-1$ |
| Interior 2 | $(-1,0),(-1,1)$ | $(0,0),(-1,0),(0,-1)$ | $-1$ |
| Sharp ray | $(-1,0),(-1,1)$ | $(0,0),(-1,0),(0,-1)$ | $-1$ |
| Hexagonal point | $(-1,0),(-1,1)$ | $(0,0),(-1,0),(0,-1)$ | $-1$ |

In the sharp marking gauged at vertex $1$, these shifts become
$((1,0),(0,0),(1,-1))$, agreeing with the F1 generator.

At most one of the three distinct lifts can saturate contraction. Indeed,
equality along an intrinsic straight segment makes the lifted map affine on
that segment. If two different root lifts saturated, points at the same
fraction $t$ on the two segments would have the same spatial image. Their
intrinsic difference is $t\ell$, where $\ell\ne0$ is the difference of
the two lattice shifts. Injectivity on the quotient would require $t\ell$
to be a lattice vector for every $t\in[0,1]$, contrary to lattice
discreteness for small positive $t$.

Thus at least two of the three leaf systems have two distinct real local
completions; at most one has a double root. Equivalently, at most one of the
three hinges $05,16,27$ can be unfolded in an embedding.

## 7. Verification and the remaining geometric gap

The exact checks accompanying the geometry verifier cover the weighted-cycle
inverse and Horn identities, the inertia polynomials, the singular kernel,
the arbitrary-core circumcenter identity, both reflection quadratics, every
leaf link/K4/hinge incidence, all archived and hexagonal marking data, and the
symbolic determinant identity for an arbitrary marking. The inequality in
Section 3 and the geometric implications are proved above; finite symbolic
checks are not substitutes for those arguments. This note is not a new
compiled Lean theorem.

The theorem supplies no uniform separation of the reflection pair. For
example, in the abstract matrix family $a=c=d=e=1, b=t>0$,

$$
c_0=\frac{4t+1}{2t},\qquad
Q(Z_+-Z_-)=\frac{8t}{4t+1}\longrightarrow0.
$$

This is a matrix example, not a family of torus embeddings. It explains why
the theorem cannot justify removing small positive fold angles or nearly
tangent stars.

For F1, the remaining task is to couple the selected completions from the
three different coherent core-lift hyperplanes. The positive theorem shows
that real solvability of each separate five-edge system is automatic once
its core has positive five-cycle deficits. Its two choices still have to
satisfy the F1 intrinsic ordering, mutual contraction, and all embedding
conditions. Their signed-space normals are not one common spatial
reflection plane. No argument here shows that every joint selection fails,
or that two of the root lifts must saturate. A full F1 contradiction remains
open.
