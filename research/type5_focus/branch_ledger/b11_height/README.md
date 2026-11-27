# B1.1: simultaneous height and metric-deficit pruning

**Status: open (0/14 chambers excluded in their entirety).** This checkpoint stays on the fixed Type 5 hexagonal target and the B1.1 orientation branch. It neither proves nonuniversality nor supplies a full embedding. As before, the marking and orientation reduction is subject to independent audit.

## 1. Three strict core inequalities, valid throughout B1

Use the hexagonal metric `dot(p,q)=p_x*q_x+3*p_y*q_y` in the scaled intrinsic coordinates. Gauge at any of the three universal vertices v=1,2,5, setting both intrinsic and extrinsic positions of v to zero and changing lifts of all other vertices so all edge shifts out of v are zero. The gauge is legitimate because v is adjacent to every other vertex. Thus the squared norm of every p_i agrees with that of r_i. Define the symmetric deficit matrix

    s_ij = <r_i,r_j> - <p_i,p_j> = (||p_i-p_j||^2-||r_i-r_j||^2)/2.

All diagonal entries vanish. All entries are nonnegative because intrinsic straight-line separation of any two lifted points bounds extrinsic distance (the segment projects to a path on the torus). For an edge with shift k_ij, the edge equation gives `s_ij= -<p_j-p_i,k_ij> - ||k_ij||^2/2`. It is zero for a zero shift and strictly positive for a nonzero shift: the edge is the unique shortest intrinsic geodesic, since its image is an embedded straight segment. In origin-1 coordinates, the same deficit in gauge v is `||k||^2/2 - <u_ij,k>`, where `u_ij=p_j-p_i+K_ij` is the original edge displacement and `k=K_ij+K_vi-K_vj` is the gauged edge shift. The checker verifies each required zero/nonzero shift directly from the exact cocycle.

Fix one gauge and label the remaining two anchor vertices a,b, the two roots c,d and the two selected leaves l,m as in the table.

| v | a,b | c,d | l,m |
|---|---|---|---|
|1|2,5|3,4|0,7|
|2|1,5|4,3|0,6|
|5|1,2|3,4|7,6|

In each row `s_ab=s_al=s_bm=s_cl=s_dm=0` and `s_am,s_bl,s_ac,s_bc,s_ad,s_bd,s_cm,s_dl>0`. The roots c,d have opposite nonzero heights over the anchor face 125 in B1. This includes all 14 B1.1 chambers.

Let `alpha_i=s_ai/s_am`, `beta_i=s_bi/s_bl` for i=c,d. The two vectors

    W_i = r_i-alpha_i*r_m-beta_i*r_l,
    U_i = p_i-alpha_i*p_m-beta_i*p_l

have the same inner products with the independent anchor vectors r_a=p_a,r_b=p_b (rigidly align the anchor faces). The horizontal projection of W_i is therefore U_i. Write its vertical component as `h_i=z_i-alpha_i*z_m-beta_i*z_l`. Bilinearity of the Gram deficit yields

    h_c^2 = 2*alpha_c*(beta_c*w-s_cm),
    h_d^2 = 2*beta_d*(alpha_d*w-s_dl),
    h_c*h_d = s_cd + (alpha_c*beta_d+alpha_d*beta_c)*w
                          - beta_c*s_dl - alpha_d*s_cm,

where `w=s_lm`. The first two identities and positive s_cm,s_dl force w>0. Set

    A=alpha_c*beta_d, B0=alpha_d*beta_c,
    X=1-s_cm/(beta_c*w), Y=1-s_dl/(alpha_d*w).

Then X,Y are in [0,1), `|h_c*h_d|=2*w*sqrt(A*B0*X*Y)`, and `h_c*h_d=s_cd+w*(A-B0+B0*(X+Y))`. Suppose A>=B0. If A>B0, by X+Y>=2*sqrt(X*Y) and sqrt(X*Y)<=1,

    A-B0+B0*(X+Y)-2*sqrt(A*B0*X*Y)
       >= A-B0+2*(B0-sqrt(A*B0))*sqrt(X*Y)
       >= (sqrt(A)-sqrt(B0))^2 > 0.

Since s_cd>=0 this contradicts the absolute value identity. If A=B0, equality forces s_cd=0, X=Y and h_c*h_d>=0. With `k=alpha_c/alpha_d=beta_c/beta_d>0`, the squared identities then give `h_c=k*h_d`, including if both are zero. Substituting the definitions gives z_c=k*z_d, contradicting their opposite nonzero signs. Therefore A<B0, i.e. `s_ac*s_bd < s_ad*s_bc`. The three rows yield the three new strict quadratic inequalities in origin-1 core coordinates. This proof does not require nonzero nonclique determinants or strict contraction for the missing root pair.

## 2. Exact simultaneous leaf filter

Keep origin 1 and the independent anchor triangle 125. The eight core variables are the two scaled intrinsic coordinates of each of 2,3,4,5. Root projections onto the anchor plane are reconstructed by the two inner-product equations with anchors 2 and 5; their heights are reconstructed by positive square roots of the radial norm differences, with signs +,-.

For each remaining vertex j=0,6,7, let q=p_j, write its prescribed signed height as sigma_j*h, h>0, with sigma=(+,-,-). The two anchor inner-product equations give the extrinsic horizontal projection as `t(q)=t0+T*q`, affine in q. The edge equations to roots 3 and 4 give two affine equations `N*q = b+c*h`. When N is invertible (or its determinant interval excludes zero), Cramer's rule gives `q=q0+q1*h` and `t=t0'+t1'*h`. The radial norm equality is precisely

    A*h^2+B*h+C=0,
    A=1+||t1'||^2-||q1||^2,
    B=2*(<t0',t1'>-<q0,q1>),
    C=||t0'||^2-||q0||^2.

For example if A,B,C have the same weak sign and one has a strict sign, there is no positive root. Otherwise the quadratic formula encloses both real roots whenever the coefficient of h^2 is separated from zero. The checker retains a conservative height interval if that coefficient may vanish, and retains the entire core box if the projection system may be singular. This is deliberate: it never assumes all regular cores, quadratics or determinants are nondegenerate. Each surviving height interval is intersected with [0,3/5], an enclosing interval for the true height since the hexagonal lattice covering radius is 1/sqrt(3). The exact linear propagation of shortest-edge inequalities also bounds every intrinsic coordinate, including leaf coordinates. The core and all candidate leaf intervals are tested for strict nearest-image inequalities, negatively oriented intrinsic faces, common determinant signs (strict for cliques, weak otherwise), and nonedge metric contraction. For every combination of surviving intervals (up to 2^3) the filter tests the same constraints jointly, including determinants with two or three leaves, all nonedge pairs, and the disjunction of the fourteen archived chamber sign vectors. These are necessary conditions, not a complete embedding test. Any box rejected by these tests is rigorously excluded; a box that survives is unresolved, not a solution.

## 3. Avoid singular division in the core tests

Let Delta=cross(p2,p5)>0, G the 2x2 anchor Gram matrix, D=det G=3*Delta^2. For root i=3,4, define v_i=(s_2i,s_5i) and A_i=(cross(p_i,p5),cross(p2,p_i)). Its height satisfies

    H_i = D*z_i^2 = -6*Delta*(v_i dot A_i) - v_i^T adj(G) v_i > 0.

The horizontal projection is p_i+delta_i, where `<p_a,delta_i>=s_ai`. The horizontal metric deficit between roots is `L/D`, with

    L = 3*Delta*(v_4 dot A_3+v_3 dot A_4) + v_3^T adj(G) v_4.

Since the two root heights have opposite signs and s_34>=0, necessarily `L>0` and `L^2>=H_3*H_4`. These are polynomial tests requiring no division by Delta. The extrinsic root coordinates multiplied by Delta can likewise be evaluated with horizontal numerators and vertical heights `+sqrt(H_3/3),-sqrt(H_4/3)`. Thus the shared core signs can also be tested before certifying that the interval for Delta is bounded away from zero. In `height.py`, the optional `--poly` switch adds these tests.

## 4. Certified exclusion of the prior core witness

`python height.py --witness` replays the previous exact six-point certificate in `../b11_core/verify_six.py`, reconstructs its radicals, changes the intrinsic gauge from vertex 5 to vertex 1, and proves that the resulting eight core coordinates are contained in the smallest rational box tested. The centers, ordered by vertices 2,3,4,5, are:

    ( 0.370172461232,  0.049030942559)
    ( 0.161261472737, -0.267213319645047)
    (-0.492828236876, -0.092695539023835)
    (-0.057681158541,  0.100369943614)

For sup-norm radius 10^-10 through 10^-6, the leaf-0 positive-height quadratic has no positive root by interval tests. At radius 10^-5, leaf 0 fails the combined necessary constraints even with the conservative height-root enclosure. All six boxes are excluded for every B1.1 chamber. This proves that the earlier exact partial witness cannot be completed; it does not prove that other cores cannot be completed.

## 5. Global exact interval experiment

Use Python 3 with assertions enabled. The checker uses integer intervals with denominator 2^100, including integer square-root enclosures. Strict nearest-edge linear inequalities are propagated by outward-rounded bounds. The initial box is the full bounded origin-1 intrinsic region (all seven non-origin vertices lie in the hexagonal Voronoi cell, hence |x|<=1/2, |y|<=1/3 in scaled coordinates); only the eight core coordinates are split. Every split covers the parent, including the midpoint; propagation retains all feasible points. All exclusions follow from the preceding necessary inequalities. Breadth-first search stops at the requested work budget. Unresolved boxes remain explicit in the generated frontier. No interval width or timeout is itself an exclusion.

Run from this directory:

```
python height.py --witness
python height.py --budget 20000 --depth 40
python height.py --budget 20000 --depth 40 --poly --output frontier_poly.json
```

The baseline run visited 20,000 nodes, excluded 1,814 boxes by necessary constraints (including 46 by the new deficit products), and left 16,444 unresolved frontier boxes. These are subdivision cells, not orientation chambers. The large generated JSON frontiers are omitted from the Git commit and can be reproduced by these commands. `search.log`, `search_poly.log` and `witness.log` record the runs. These experiments do not exhaust the core domain. The interval dependency/near-singular anchor problem still prevents a practical exhaustive certificate; do not repeatedly subdivide without a stronger exclusion argument. No B1.1 subcase can yet be declared closed in its entirety.

With the division-free polynomial tests enabled, the second run excluded 1,820 boxes and left 16,432 unresolved frontier boxes after 20,000 visited nodes. Of its exclusions, 45 used the strict deficit-product inequalities and 68 used the new polynomial root-contraction test. Different pruning decisions change the subdivision tree, so these two runs' counts are not additive. Neither variant closes any chamber. The small preliminary floating search was not used as evidence for these conclusions.
