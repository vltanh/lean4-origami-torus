# Completing a Type 5 leaf

Fix the spatial positions of the five core vertices and their intrinsic lifts around one leaf. Suppose the spatial and intrinsic lengths agree on each edge of the leaf's link, and that the squared intrinsic distance strictly exceeds the squared spatial distance on each of its five diagonals. Then the leaf has exactly two simultaneous spatial and intrinsic positions. Every incident triangle has positive area at both positions. [Lean proof](../../OrigamiTorus/EightVertex/Type5/PositiveCycle.lean)

## The five deficits

Use the form $B((r,p),(s,q))=r\cdot s-p\cdot q$ on $\mathbb R^3\times\mathbb R^2$, and write $Q(u)=B(u,u)$. For the neighbors in oriented link order, let $K_i=(r_i,s_i)$, where $s_i$ is the intrinsic position in the coherent lift of this leaf star. Define $S_{ij}=-Q(K_i-K_j)/2$. Thus $S_{ij}$ is half the intrinsic squared distance minus half the spatial squared distance. Diagonal and consecutive entries vanish. The other entries are

$$
 S_{02}=a,\quad S_{03}=b,\quad S_{13}=c,\quad S_{14}=d,\quad S_{24}=e.
$$

Throughout this proof $a,b,c,d,e>0$. The indices in the display are local indices $0,\ldots,4$. In the table, each pair in the last column gives the actual vertex labels of the corresponding deficit. For example, $34$ can have a different intrinsic lift at each leaf. [Oriented link cycles](../../OrigamiTorus/EightVertex/Type5/Reconstruction.lean)

| Leaf | Neighbors $K_0,K_1,K_2,K_3,K_4$ | Pairs for $a,b,c,d,e$ |
| --- | --- | --- |
| $0$ | $1,2,4,5,3$ | $14,15,25,23,34$ |
| $6$ | $1,3,2,5,4$ | $12,15,35,34,24$ |
| $7$ | $1,4,2,3,5$ | $12,13,34,45,25$ |

## Positivity of the inverse quadratic form

Let $P=2abcde$. In the determinant expansion of $S$, a contributing permutation must cover all five vertices by disjoint cycles along edges of its support. The support is a pentagon, so the two orientations of that pentagon give the only terms. Both have positive permutation sign. Hence $\det S=P$. [Gram determinant](../../OrigamiTorus/EightVertex/Type5/LeafRank.lean)

We claim $v^TS^{-1}v>0$ whenever all five entries of $v$ are positive. Put $m=(ce,be,bd,ad,ac)$, $y_i=m_i v_i$, and $L=\sum_i y_i$. For subscripts read modulo five, set $h_i=m_i(L-2y_{i-1}-2y_{i+1})$. Then $Sh=Pv$. For instance, its first coordinate is $ah_2+bh_3=abd(2y_0)=Pv_0$. In each of the other four rows, the products of the two row weights with the corresponding $m_i$ likewise agree, and the four subtracted terms leave twice the remaining $y_i$. Taking the product with $v^T$ gives

$$
 P v^T S^{-1} v = L^2-4\sum_{i=0}^4 y_i y_{i+1}.
$$

Rotate the $y_i$ so their minimum $t$ occurs last. Write them as $(A+t,B+t,C+t,D+t,t)$, with $A,B,C,D\ge0$. Expanding the right side gives

$$
 (A+C-B-D)^2+4AD+2t(A+B+C+D)+5t^2.
$$

This is strictly positive since $t>0$. In particular $\tau=\mathbf1^T S^{-1}\mathbf1>0$. The Lean statement for general $v$ is `pentagonGram_inv_positive`. [Lean proof](../../OrigamiTorus/EightVertex/Type5/PositiveCycle.lean)

## The center and the two solutions

Put $w=S^{-1}\mathbf1/\tau$ and $Z_0=\sum_i w_iK_i$. Then $\sum_i w_i=1$ and $Sw=\mathbf1/\tau$. For any coefficient vector $c$ with $\sum_i c_i=0$, expansion of the squared distances gives

$$
 Q\!\left(\sum_i c_iK_i\right)
 =-\tfrac12\sum_{ij}c_ic_j Q(K_i-K_j)=c^TSc .
$$

Taking $c=e_i-w$ gives $Q(K_i-Z_0)=-1/\tau$ for every $i$. Polarization gives the corresponding bilinear identity for any two vectors of coefficients with sum zero.

Let $U$ be the matrix with four rows $K_i-K_4$ for $0\le i<4$, and $J=\operatorname{diag}(1,1,1,-1,-1)$. Its Gram matrix $G=UJU^T$ has entries $G_{ij}=S_{ij}-S_{i4}-S_{j4}$. To compute its determinant, change coefficient basis to the four rows $e_i-e_4$ followed by $w^T$. The change of basis has determinant $1$ since $\sum_i w_i=1$. The first four rows are $S$-orthogonal to $w$ and $w^TSw=1/\tau$. Thus $\det G=\tau\det S>0$. In particular the rows of $U$ span a nondegenerate four-dimensional subspace. The formal proof also gives the direct determinant expansion $\det G=(\sum_i m_i)^2-4\sum_i m_i m_{i+1}$.

Choose a nonzero $N$ with $UJN=0$. The orthogonal complement of the row space of $U$ has dimension one, and $N$ lies outside that row space by nondegeneracy. If $W$ has first row $N$ and remaining rows $U$, then its Gram matrix is block diagonal. Hence

$$
 0<(\det W)^2=\det(WJW^T)=Q(N)\det G.
$$

In particular $Q(N)>0$. A solution $Z$ must satisfy $Q(K_i-Z)=0$ for every $i$. Subtract the equation for $K_4$ from each of the other four. The equal distances already proved at $Z_0$ give $B(K_i-K_4,Z-Z_0)=0$. Thus $Z=Z_0+tN$. Since each $K_i-Z_0$ lies in the row space of $U$, substitution gives $Q(K_i-Z_0-tN)=-1/\tau+t^2 Q(N)$. Its two distinct roots give precisely

$$
 Z_\pm=Z_0\ \pm\ \frac{N}{\sqrt{\tau Q(N)}} .
$$

In the formal proof `leafBranch_spec` gives the formula for both solutions, their distinctness and their exhaustion of the distance equations. The center relative to $K_4$ is $U^TG^{-1}f$, where $f_i=Q(K_i-K_4)/2$. Indeed $G(w_0,w_1,w_2,w_3)^T=f$ because $B(K_i-K_4,Z_0-K_4)=Q(K_i-K_4)/2$. [Lean proof](../../OrigamiTorus/EightVertex/Type5/PositiveCycle.lean)

## The face areas

At either completion let $Y_i=K_i-Z$. Polarizing $Q(Y_i)=Q(Y_j)=0$ gives $B(Y_i,Y_j)=-Q(K_i-K_j)/2=S_{ij}$. As $\det S\ne0$, the five $Y_i$ are linearly independent. For consecutive distinct $i,j$, the span of $Y_i,Y_j$ is totally null because $S_{ij}=0$. If their intrinsic projections were dependent, some nonzero pair of scalar coefficients would give a combination with zero intrinsic projection. Its mixed norm is then just the squared Euclidean norm of its spatial projection. That norm vanishes, so the whole combination vanishes, contradicting independence. Their intrinsic projections therefore have nonzero determinant. Its absolute value is twice the intrinsic triangle area. These statements are `positive_cycle_rays_independent` and `positive_cycle_face_nondegenerate`. [Lean proof](../../OrigamiTorus/EightVertex/Type5/PositiveCycle.lean)

For a continuous family of such cores, a continuous choice of $N$ is obtained by setting $N_j=J_{jj}(-1)^j\det U_{\widehat j}$, with $U_{\widehat j}$ formed by deleting column $j$ and indices starting at zero. Expansion along a repeated row gives $UJN=0$, and some maximal minor is nonzero because $U$ has row rank four. The displayed formulas for $Z_\pm$ then give two continuous branches, as proved by `continuous_leafBranch`. On a connected parameter domain the signed area of each incident face keeps its sign at any one base point. The leaf argument applies separately to $0,6,7$ once their deficits are positive. The anchor face $152$, the choice of signs at the base point, and spatial separation between different faces are additional assertions of the torus construction. [Off-ray construction](Type5FoldedModuli.md)
