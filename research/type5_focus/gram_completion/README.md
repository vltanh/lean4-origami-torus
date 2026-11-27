# Type 5: signed Gram completion and global root-chord inequalities

**Status: open. B1.1 remains 0/14 excluded; no other chamber is declared closed.** The new metric formulation covers both height families without enumerating reconstruction signs, and the new slack inequalities apply across all chambers. The earlier marking and strict-support/K4 nondegeneracy proof premises still require independent audit. No novelty or Lean-verification claim.

## 1. Labeled edge lengths determine the embedding

The Type 5 graph is K3 joined to K2,3, with anchor face A=(1,2,5), roots (3,4), and leaves (0,6,7). Fix any nondegenerate anchor triangle. Distances to its three vertices determine the planar projection and squared height of each of the other five vertices. By the earlier K4 lemma each height is nonzero in an embedded flat realization. Every root-leaf edge determines the product of the two signed heights by the remaining distance equation. Since K2,3 is connected, these products uniquely determine the five signs up to simultaneous reflection. Thus every Type 5 embedded flat realization is uniquely determined up to congruence by its 24 labeled edge lengths, conditional on the K4 lemma. This argument is independent of the lattice metric and needs no generic nonclique determinant signs. It does not say that any proposed edge lengths are realizable.

## 2. Six polynomial equations in 14 intrinsic variables

At the hexagonal marking work in the scaled coordinate norm x^2+3y^2, gauge all shifts from 1 to zero, and align the extrinsic anchor triangle with its intrinsic lift. Let p1=0, D=cross(p2,p5)>0 (the oriented area of face 152 is negative; the total signed double area is -1 for this cocycle). For each known Gram entry set G_ii=||p_i||^2, G_ij=(G_ii+G_jj-||p_j-p_i+K_ij||^2)/2. The anchor 2-by-2 block for 2,5 is positive definite with determinant 3D^2.

For each outside vertex i define
    T_i=(G_2i*p5_y-G_5i*p2_y, (p2_x*G_5i-p5_x*G_2i)/3),
    H_i=D^2 G_ii-||T_i||^2,
    J_ij=D^2 G_ij-<T_i,T_j>  (root-leaf edges).
For anchors use T_i=D*p_i. In a true realization T_i=D times the horizontal projection and H_i=D^2*z_i^2, J_ij=D^2*z_i*z_j. Require each H_i>0. Instead of introducing radicals or unknown missing Gram entries, impose exactly six determinant equations:

* Four principal 4-by-4 Gram minors with index sets (2,5,3,j) for j=0,6,7 and (2,5,4,0).
* Two mixed 4-by-4 Gram minors with rows (2,5,3,4) and columns (2,5,0,j) for j=6,7.

By the Schur determinant identity (anchor block invertible) these are respectively J_3j^2=H_3 H_j, J_40^2=H_4 H_0, and J_40 J_3j=J_4j J_30. Conversely put v3=sqrt(H3)>0, vj=J_3j/v3, v4=J_40/v0. All denominators are nonzero, and exactly these six equations give all radial equalities and root-leaf products. Thus the metric equations hold for extrinsic coordinates (T_i/D,v_i/D). The mixed equations are important: six squared principal-minor tests alone do not ensure compatible signs.

For incidence tests use polynomial coordinates (T_i,W_i) with W_i=0 for anchors, W3=H3 H0, Wj=H0 J_3j for leaves, W4=J_30 J_40. These are obtained from the true reconstructed coordinates by positive horizontal scaling D and positive vertical scaling D H0 sqrt(H3). Thus they preserve all affine incidence signs and intersections, including degenerate cases. No division or radical appears in the generated system. With intrinsic consistently oriented degree-one faces, strict nearest-edge tests, and the full disjoint-simplex circuit exclusions, the formulation is equivalent to the fixed-marking embedded problem under the earlier nondegeneracy premise. In particular no sign archive is required for the default full system; the optional B1.1 restriction uses the old weak/strict chamber convention. It has only 14 declared real variables, compared with the prior explicit-coordinate systems; this is not a reduction below the eight-variable radical core in continuous dimension.

## 3. New low-degree global root-chord bounds

Use the notation and three gauges from ../branch_ledger/b11_height/README.md. In any one gauge v let a,b be the other anchors, c,d the ordered roots, l,m the chosen leaves. The slack s_ij=<r_i,r_j>-<p_i,p_j> in that gauge is nonnegative by metric contraction. In particular zero shifts give zero slacks and nonzero edge shifts give strict positive slacks. Write ac=s_ac, ad=s_ad, bc=s_bc, bd=s_bd, M=s_am, L=s_bl, U=s_cm, V=s_dl and w=s_lm. All eight named edge slacks are positive. Put delta=ad*bc-ac*bd, alpha=ac/M, beta=bc/L, alpha2=ad/M, beta2=bd/L. In the prior anchor-plane orthogonalization define h_c=z_c-alpha*z_m-beta*z_l, h_d=z_d-alpha2*z_m-beta2*z_l. Its identities are
    h_c^2=2 alpha (beta*w-U),
    h_d^2=2 beta2 (alpha2*w-V),
    h_c*h_d=s_cd+(alpha*beta2+alpha2*beta)*w-beta*V-alpha2*U.

Taking k=ac/ad and completing the square gives
    (h_c-k*h_d)^2=2*k*((beta-k*beta2)*V-s_cd).
Taking k=bd/bc gives the other square
    (h_d-k*h_c)^2=2*k*((alpha2-k*alpha)*U-s_cd).
Consequently, without any height-side hypothesis,
    0 <= s_cd <= delta*V/(L*ad),
    0 <= s_cd <= delta*U/(M*bc).
In particular delta>=0. Equality delta=0 implies s_cd=0 and h_c=(ac/ad)*h_d, hence z_c=(ac/ad)*z_d, so opposite root heights imply delta>0. These sharpen the previous product tests by bounding the missing root distance in every gauge.

Let q_v be the root displacement in gauge v. The three lifts differ by lattice shifts (0,0),(1,-1),(1,0) in the origin-1 cocycle. For each gauge w, s_cd^(v) >= (||q_v||^2-||q_w||^2)/2 by metric contraction along q_w. Hence the two upper bounds above give 18 division-free inequalities involving only intrinsic coordinates. The chart-square differences are affine, so these tests are cubic at most.

There is also a slope-order test. In each gauge let n be the remaining leaf; s_cn=s_dn=0. For i=c,n,d write k_i=(s_ai,s_bi), with strictly positive entries. Take lambda_c=det(k_n,k_d), lambda_n=det(k_d,k_c), lambda_d=det(k_c,k_n), so sum lambda_i k_i=0. The horizontal projection of sum lambda_i r_i equals sum lambda_i p_i because its two anchor inner-product deficits vanish. Its squared vertical component is exactly 2 lambda_c lambda_d s_cd. If s_cd>0 then lambda_c lambda_d>=0, which puts the middle slope s_an/s_bn between s_ac/s_bc and s_ad/s_bd (ordered by delta>=0). In the equality case delta=0 the previous upper bounds imply s_cd=0, so no ambiguity is imposed. At most one of the three gauges can have s_cd=0: equality would make the projected intrinsic straight segment an extrinsic straight segment, and two different lattice lifts cannot map to the same segment in an embedding. Thus at least two of the three slope-order tests hold. This is an exact disjunction covering both B1 and B2, not a genericity assumption.

## 4. Reproduction and limitations

Run from this directory: 

    python verify.py
    python gram.py --relax > relaxed.smt2
    python gram.py --b11 > full_B11.smt2
    python ../solve.py 10000 relaxed.smt2 full_B11.smt2

The symbolic Schur determinant identity, both slack-square identities and the rational signed completion checks passed. The SMT generator was tested locally with the current marking and 14 B1.1 sign strings transcribed from the repository; both 10-second solver runs returned UNKNOWN (timeout), including with the new root-chord tests. The full system is the default; --relax omits the simplex exclusions and is only necessary. The direct clone was unavailable in that environment, so the committed generator was not replayed via a fresh checkout. No SAT or UNSAT claim and no independent proof audit. An exploratory floating optimization of the new low-degree inequalities alone found positive margin, so those inequalities by themselves are not a proposed global contradiction. The unresolved gate is to decide the exact full polynomial system or find a stronger geometric contradiction; B1.1 remains active and open.
