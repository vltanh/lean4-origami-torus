# Second blow-up: four affine intrinsic limit families for elongated Type 7 ray_4

## Theorem and scope

Conditional on the prior necessary orientation reduction, compactification and common-line limit theorem, any sequence of embedded Type 7 ray_4 tori with y tending to infinity has, after taking a subsequence and applying marking symmetries, limiting intrinsic data in one of the four affine segments below. In particular at least three of the eight horizontal ring steps tend to zero, and the spread of the rescaled vertical coordinates tends to its upper bound 3/8. This is stronger than common-line collapse: the earlier quarter-step collinear witness cannot be approached by actual embeddings. No assertion of eventual nonexistence or of closure of either positive-t branch is made.

We use the notation, correction matrix and orientation representatives of limit_obstruction.md. The argument is entirely about necessary limits, and does not assume that a degenerate limiting complex is embedded.

## 1. Magnify the transverse width, regardless of its rate of collapse

Let t=1/y^2. After the earlier compactification, normalize the long-axis coordinates so that the A-ring heights are O(t) and B-ring heights are 1+O(t), and the transverse vectors P_0=P_1=0 are bounded. Work in a subsequence with one fixed canonical weak mixed orientation representative R1 or R2. All extrinsic vertices cannot be coplanar: an embedded closed torus cannot lie in a plane (invariance of domain). Hence the transverse vectors span the plane at every positive t.

Rotate the transverse coordinates (orientation preserving) so that a P_i of maximum norm lies on the positive first axis. That maximum is bounded below away from zero: in either ring some horizontal intrinsic step is at least 1/4, and its physical extrinsic ring edge has the same length, while its physical axial component is O(sqrt(t)). By the previous common-line limit theorem the maximum absolute second coordinate epsilon tends to zero, but is strictly positive. Divide the second coordinate by epsilon; this is an invertible orientation-preserving affine change, and **does not change any of the full orientation signs**, even if epsilon tends to zero much faster than t. Pass to a convergent subsequence of these new bounded coordinates. The limiting transverse vectors span the plane: one has first coordinate bounded below and second coordinate zero, and another has second coordinate of absolute value one. Heights still tend to 0 or 1.

Write e_i,f_j for the cyclic planar edge vectors in this *magnified* limit. Write p_i,q_j for their first components, and a_i=|p_i|, b_j=|q_j|. These are the limiting horizontal intrinsic steps because the original second components and physical axial differences tend to zero. Thus 0<=a_i,b_j<=1/2, each ring's sum of these scalar lengths is one, and each vector cycle closes. The residual metric identities of the previous common-line limit apply to **first components only**, not to the magnified vector lengths. This distinction is essential. No comparison of the rates of epsilon and t is needed.

The mixed sign constraints of the previous limit theorem hold unchanged in the magnified plane. The cross-product matrix, with the same column permutation and sign, is a weak balanced Laplacian. Its rank cannot be zero: both rings have positive projected perimeter, so zero cross products would force all edges parallel to one common line, contradicting the spanning normalization. It has rank at most two. The rank/component argument in limit_obstruction.md therefore applies, including its proofs of the parallelogram, triangle, and two-stick possibilities using only signs and linear algebra.

## 2. Rank two: parallelograms impossible; triangles only at half-stick endpoints

For a 2+2 Laplacian partition the rings are nondegenerate magnified parallelograms, with cyclic edges (u,v,-u,-v) and (w,z,-w,-z); w=k*u and z=l*v for nonzero k,l of the same sign, by the mixed signs. The minors 0145 and 2367 impose opposite weak inequalities on (k-l)*cross(u,v), forcing k=l. Unit *projected* perimeter then implies |k|=1, even if one direction has zero first component. Write sigma=k. The metric residual N0+N1, using only projected components, becomes 4*sigma*(u_x^2+v_x^2)=0. The projected perimeter is one, so this is impossible.

For a 3+1 partition, rotate the zero A edge to index 0. The zero B edge is index 1 for R1, 3 for R2. The duplicate-vertex minors and K4 signs in the previous proof force the two triangle bases e1 and f0 (R1) or e1 and f2 (R2) to be positively parallel. Denote them by positive multiples of n. In cyclic order the two triangles have vectors (base,u,u') and (base,v',v). Both are clockwise; let u and v' make angles -theta and -psi with n, and u' and v make angles phi and chi, with theta,psi,phi,chi in (0,pi). The same K4 signs give theta>=psi, chi>=phi and phi+psi>=pi. These statements concern magnified directions.

Choose the sign of the first-coordinate functional so its value on n is nonnegative. Denote its values on the bases by alpha,beta>=0 and on u,v by U,W. The other components are -alpha-U and -beta-W. The magnified directions are nonzero but some components can vanish. The residual N0+N1 computed in projected components gives exactly
    |U|*|W| - U*W = 1/2-alpha-beta.
Suppose the first-coordinate functional is positive on n. Then alpha,beta>0. The identity forces alpha+beta<=1/2, so alpha,beta<1/2. By projected closure and perimeter, U is either -1/2 or 1/2-alpha, and W is either -1/2 or 1/2-beta. Opposite signs give a left side 1/2-alpha or 1/2-beta, which cannot equal 1/2-alpha-beta. Same signs force alpha+beta=1/2. If both U,W are positive, the directions of n,u,v are in an open halfplane defined by the functional, but theta+chi>=phi+psi>=pi, which is impossible for their angular interval through n. If both are negative, the components of u',v' are positive; n,u',v' cannot lie in that same open halfplane since phi+psi>=pi. This exhausts the possibilities.

Consequently the common base direction is in the kernel of the first-coordinate functional. Both alpha and beta are zero. Each remaining projected pair has components +1/2,-1/2 in some order. The residual requires U and W to have opposite signs. Choose the sign of the functional to make U=+1/2. In R1 the signed projected edges are p=q=(0,0,1/2,-1/2), and a rotation by two ring indices makes p=q=(1/2,-1/2,0,0). In R2 they are p=(0,0,1/2,-1/2), q=(1/2,-1/2,0,0). These are respectively endpoints of families F1 and F3 below. The two triangles can be magnified-nondegenerate even though both original rings have two zero limiting steps.

## 3. Rank one: four intervals

The balanced Laplacian now has one two-index block and two singleton blocks. One ring must be collinear in the magnified plane. Exchange the rings by the checked weak marking symmetry if needed so it is B. Since the cross-product matrix is nonzero, the singleton columns are zero B edges; the remaining B edges are opposite. Their first components are nonzero, because B's projected perimeter is one, so both have projected length 1/2.

By simultaneous cyclic rotation the nonzero indices are either (0,2) or (0,1). The opposite-index case (0,2) is impossible by the same duplicate-vertex mixed-minor proof as Section 6 of limit_obstruction.md: the mixed signs force all A chords parallel to B, contradicting rank one. This proof is unaffected by magnification.

For adjacent indices (0,1), choose the sign of the first-coordinate functional so that q=(1/2,-1/2,0,0). The two active A rows in R1 are 3,0; e1,e2 are parallel to the B line. The sign of e0,f0 and the cyclic triple signs force e1,e2 to point in the negative f0 direction (zero permitted), so p1=-a1,p2=-a2. In R2 the active A rows are 1,2, and the analogous triple signs give p3=-a3,p0=-a0. These deductions are the same planar half-plane arguments as before, but we apply them to the signs of the projected components, not to Euclidean lengths of the magnified edges.

The exact projected metric residual is
    0=-a0-2*a1-a2+p0-p2+1.
In R1, use perimeter and closure to get 0=2*a2+a3-p3. Each term is nonnegative, so a2=0 and p3=a3. Closure then gives p0=a1-a3, and since a0=|p0|, perimeter gives max(a1,a3)=1/2. In R2 the same computation gives 0=-2*a0-a1+p1, hence a0=0,p1=a1, p2=a3-a1 and max(a1,a3)=1/2. Notice that the inequalities are not strict here: the active magnified vectors need not have nonzero first component.

We obtain the following exhaustive necessary intrinsic limit families, with 0<=u<=1/2. B has b=(1/2,1/2,0,0), q=(1/2,-1/2,0,0) in all rows.

| Family | Orientation | a (unsigned horizontal steps) | p (signed projected steps) |
|---|---|---|---|
| F1 | R1 | (1/2-u,1/2,0,u) | (1/2-u,-1/2,0,u) |
| F2 | R1 | (1/2-u,u,0,1/2) | (u-1/2,-u,0,1/2) |
| F3 | R2 | (0,u,1/2-u,1/2) | (0,u,1/2-u,-1/2) |
| F4 | R2 | (0,1/2,1/2-u,u) | (0,1/2,u-1/2,-u) |

The previous rank-two triangle endpoints are included: F1(0) and F3(0). This list is an upper bound on the feasible limits, not a list of realized limiting sequences.

## 4. Exact affine recovery of all intrinsic data

The gauge-normalized horizontal coordinates x follow from the ring steps and the single unknown h=x_1. Set x_0=gamma_0=0 as before. The 16 exact slack equations from Section 1 of limit_obstruction.md become in the original common-line limit
    delta_ij = a_i*b_j-p_i*q_j
             = d*X + 1/8 + n'*(gamma_j-gamma_i)
where on the right i,j denote the exceptional cross edge's endpoints, and on the left the ring edge indices. After substituting the ring steps they form a linear system of rank eight in h,gamma_1,...,gamma_7. In each of F1–F4 it has a unique solution, checked exactly by the companion script. For compact notation let e=1/8.

| Family | h | (gamma_1,...,gamma_7) |
|---|---|---|
| F1 | -u | (e-u/2,2e-u/2,-e-u/2,-u/2,e-u/2,-u/2,e-u/2) |
| F2 | -1/2 | (-e,u/2-2e,-3e,-2e,-e,-2e,-e) |
| F3 | -1/2 | (-e,0,e,-u/2,-e,-2e,-e) |
| F4 | -1/2 | (-e,0,e,-2e,-e,-u/2,-e) |

In all four rows the vertical spread max gamma-min gamma is exactly 3/8 across the entire interval, saturating the earlier narrow-level theorem. The other cross shortest-lift slacks and |X|<=1/2 also hold weakly; no strict finite-t inequality has been inferred from these equalities. The checker validates the affine identities and these weak inequalities by endpoint evaluation. The table specifies the fourteen independent normalized intrinsic coordinates up to a finite relabeling, not the full extrinsic data.

## 5. Next gate: exclude approach to the four segments

This replaces an unrestricted continuous collinear limit analysis with four explicit compact line segments (two per orientation branch), including all zero-step endpoints. In particular compactness gives a uniform statement: if there are arbitrarily elongated ray_4 realizations, their intrinsic distance to the union of these segments and their symmetry images tends to zero in the chosen normalization. At least three horizontal steps must vanish in the limit, and the vertical spread must approach 3/8. The former exact collinear limit witness with eight quarter steps cannot occur as a limit of actual embeddings. Neither these statements nor weak feasibility of the listed families proves that any family is approached by actual realizations. They also say nothing about the other sharp-ray markings.

A promising next attack is an exact neighborhood obstruction using the strict slack conditions at the saturated three-edge paths and the positive-t Gram constraints. A uniform exclusion of neighborhoods of all four segments would prove eventual ray_4 nonexistence. No such exclusion is asserted here.

Reproduce with python3 check_blowup.py (SymPy, assertions enabled). The new script was run locally with the transcribed current ray_4 edge shifts and representative sign strings; the exact finite and polynomial checks passed. This is not a rerun of the prior SAT completeness proof or an independent audit of the earlier geometric lemmas. All prior audit qualifications remain.
