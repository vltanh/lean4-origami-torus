# A hand proof of spatial embeddedness for Type 5

Up to a similarity and reflection, a flat torus has periods $1$ and $x+iy$ with $0\le x\le1/2$, $y>0$, and $x^2+y^2\ge1$. For $x<1/2$, one can start with an explicit planar configuration, open its hinges successively at fixed periods, and choose the sides of two final folds. The resulting seventeen spatial signs imply embeddedness by the first theorem below. On $x=1/2$ above the hexagon, a different seventeen signs suffice. Their realization along the whole ray currently uses an exact polynomial calculation. Together these give all nonhexagonal similarity classes. [Off-ray hand construction](Type5OffRayConstruction.md) · [Sharp-ray calculation](Type5SharpSigns.md)

The Palomar statements proved in Lean cover both determinant implications, the two leaf completions, the square and two explicit modulus boxes. The global parameter argument is only partially formalized. [Comparison statements](../../palomar/OrigamiTorus/EightVertex/Type5/Challenge.lean)

Let $r_0,\ldots,r_7\in\mathbb R^3$. Join these points by affine triangles with the following oriented vertex triples, in Lutz's labeling.

```text
012  031  024  053  045  152  136  164
147  175  263  237  274  256  357  465
```

**Separation theorem.** Write $[abcd]=\det(r_b-r_a,r_c-r_a,r_d-r_a)$. If the following seventeen brackets have the indicated strict signs, the affine realization of this complex is a closed embedding.

```text
1234− 1235+ 1245− 1345− 2345+ 0125+ 0135− 0234− 0245+
1236− 1247+ 1357− 2357− 2456− 0246+ 0456+ 2367−
```

This applies to placements with coplanar quadruples among the other labels. The theorem gives the spatial part of the off-ray construction. A second application below constructs actual piecewise-isometric embeddings throughout an oblique box. [Lean separation theorem](../../OrigamiTorus/EightVertex/Type5/OffRaySeparation.lean) · [Lean box theorem](../../OrigamiTorus/EightVertex/Type5/OffRayBase.lean)

## Fourteen determinant identities

Fix $u,v$. With $D_{ab}=[uvab]$, expansion of the two-by-two minors in the quotient by the line $r_ur_v$ gives
$$
D_{ab}D_{cd}-D_{ac}D_{bd}+D_{ad}D_{bc}=0.
$$
The identity also follows by expanding the three determinants and holds if $r_u=r_v$. In each row below, substitute the six labels into this identity and sort the four indices of each bracket, changing sign on every transposition. Two summands have the same strict sign. The third has the opposite sign, and one factor of that product is already known. For example, the first row reads
$$
[0245][2346]=[0234][2456]+[0246][2345]>0.
$$
Since $[0245]>0$, this gives $[2346]>0$. The rows are ordered so that every other factor comes from a hypothesis or a preceding row. [Determinant identity](../../OrigamiTorus/Geometry/AffineDeterminants.lean)

| $uv$ | $abcd$ | Deduction | $uv$ | $abcd$ | Deduction |
|---|---|---|---|---|---|
| `24` | `0356` | `2346+` | `25` | `0134` | `0235−` |
| `24` | `1356` | `1246−` | `35` | `0124` | `0345+` |
| `12` | `3456` | `1256+` | `45` | `0236` | `3456−` |
| `24` | `0136` | `0124+` | `26` | `1345` | `2356−` |
| `23` | `0456` | `0236−` | `25` | `0346` | `0256−` |
| `35` | `0246` | `0356−` | `35` | `0146` | `1356+` |
| `35` | `1267` | `3567−` | `15` | `0236` | `0156−` |

## Seven planes suffice

For the ordered plane $abc$, the function $L(z)=\det(r_b-r_a,r_c-r_a,z-r_a)$ is affine in $z$. Its values on the other vertices are the brackets just computed. Every row has a strictly positive witness, so its three plane vertices are affinely independent.

| Plane | $L>0$ | $L<0$ | Maximal disjoint pairs assigned to the plane |
|---|---|---|---|
| `056` | `4` | `123` | `045/136 045/236` |
| `124` | `37` | `056` | `045/12 045/237 146/237 237/456` |
| `125` | `46` | `03` | `012/456 013/256 013/456 03/125 035/12` |
| `135` | `0246` | `7` | `012/357 013/57 024/157 024/357 045/17 136/57 146/357 157/46 17/456` |
| `236` | `015` | `47` | `01/236 01/237 012/36 012/47 013/247 035/247 035/26 125/36 125/37 125/47 136/247 15/237 15/247 247/56` |
| `246` | `135` | `0` | `024/136 024/56 04/125 04/256 125/46` |
| `356` | `02` | `147` | `02/146 02/147 03/157 035/146 035/147 136/25 146/25 147/236 147/256 157/236 256/37 26/357` |

Here $s/t$ means that $s,t$ lie in opposite **closed** half-spaces and that the only allowed zero vertices belong to the displayed plane triple. To check completeness from the sixteen faces, form their 24 unordered edges. For each face list every disjoint face, keeping each unordered pair once. This gives 21 pairs. Pair each face also with every disjoint edge whose two incident faces both meet the original face. This adds 30 pairs. Every disjoint pair of subfaces extends to one of these 51 entries. Equivalently, form the nonempty subsets of the sixteen triples, discard duplicates, and delete each disjoint pair contained in a larger disjoint pair. This gives exactly the last column. The Lean proof checks the half-space inclusions directly on all subfaces.

Suppose convex combinations of vertices in such a pair have the same value $z$. Their values of $L$ force $L(z)=0$. Every coefficient of a strictly positive or negative vertex therefore vanishes. The remaining coefficients on both sides belong to the same three affinely independent vertices. Uniqueness of barycentric coordinates forces these coefficients to agree, which is impossible for disjoint supports of total mass one.

Finally, if two barycentric points of the complex have the same image, subtract their coordinatewise minimum from both weight vectors. The remainders have disjoint supports, agree in spatial value, and have the same total mass. A positive mass would give the excluded pair after normalization. Thus the original weights agree. The realization map is continuous and injective from a compact complex to a Hausdorff space, so it is a closed embedding. [Lean half-space and barycentric argument](../../OrigamiTorus/EightVertex/Type5/BracketEmbedding.lean)

## The sharp-ray determinant criterion

The same labeled complex has a second sufficient set of strict bracket signs, attained by the open sharp-ray family.

```text
0125+ 0126+ 0134− 0136− 0234− 1234+ 1236− 1237+ 1245+
1345− 1356+ 1357− 1456+ 2345+ 2347− 2456− 2467−
```

The first deduction is $[1235]>0$. Expand a determinant with two identical rows of ones to obtain
$$
[2345]-[1345]+[1245]-[1235]+[1234]=0.
$$
All four terms other than $-[1235]$ are positive. The remaining deductions use the three-term identity above, reading each row from left to right.

| $uv$ | $abcd$ | Deduction | $uv$ | $abcd$ | Deduction |
|---|---|---|---|---|---|
| `13` | `2456` | `1346+` | `13` | `2457` | `1347−` |
| `13` | `0246` | `0123+` | `12` | `0356` | `1256−` |
| `12` | `3456` | `1246−` | `24` | `1356` | `2346−` |
| `24` | `1367` | `1247−` | `14` | `2357` | `1457−` |
| `12` | `0456` | `0124+` | `24` | `0136` | `0246+` |
| `12` | `0347` | `0127+` | `12` | `0367` | `1267+` |

The seven planes below account for the same 51 maximal pairs. The half-space and barycentric arguments apply verbatim, proving the sharp-ray separation criterion. [Lean theorem](../../OrigamiTorus/EightVertex/Type5/SharpRaySeparation.lean)

| Plane | $L>0$ | $L<0$ | Maximal disjoint pairs assigned to the plane |
|---|---|---|---|
| `126` | `3457` | `0` | `01/237 36/012 456/012` |
| `127` | `4` | `036` | `013/247 136/247` |
| `134` | `026` | `57` | `012/357 012/47 013/57 024/357 157/024 157/03 157/236 236/147 57/136` |
| `136` | `0` | `245` | `013/256 013/456 236/01` |
| `145` | `26` | `37` | `157/46 256/147 357/146 357/26 456/17` |
| `234` | `05` | `167` | `02/147 035/12 035/146 035/147 035/247 035/26 12/045 136/024 136/045 136/25 17/045 236/045 237/045 25/146` |
| `246` | `15` | `037` | `02/146 024/56 125/03 125/04 125/36 125/47 146/237 15/237 15/247 256/04 37/125 37/256 456/237 46/125 56/247` |

## A flat torus in the off-ray family

**Oblique-box theorem.** Put $A=(1,0)$ and $B=(x,y)$, where $y>0$. If
$$
\left|x-\tfrac14\right|\le2^{-80},\qquad
\left|y^2-\tfrac{31}{16}\right|\le2^{-80},
$$
then $\mathbb R^2/(\mathbb ZA+\mathbb ZB)$ has a piecewise-isometric Type 5 embedding. The center has $|B|^2=2$ and $1/2-x=1/4$. We use the same five rational core points throughout this box in the coordinates $(p_x,yp_y)$.

| Vertex | $p_x$ | $yp_y$ |
|---|---:|---:|
| 1 | 0 | 0 |
| 2 | $1903/8192$ | $-72710356991/68719476736$ |
| 3 | $1073741823/2147483648$ | $28632416275/163208757248$ |
| 4 | $-3/32$ | $133347454740336344998423771343888576536231/450883210163767894319335326818189031768064$ |
| 5 | $-137/512$ | $-1687/2048$ |

For increasing indices the nonzero shifts $K_{ij}$ are $A-B$ on $04,24,27$, $A$ on $05,35,37$, $-B$ on $23,26,56$, and $B$ on $45$. Reverse the sign on reversing an edge. Set $r_i=(p_i,0)$ for $i=1,2,5$. For a vertex $j$ with intrinsic coordinate $u$ and spatial coordinate $v$, put $s_i=p_i-K_{ij}$. The required distances to vertex 1 and a core neighbor $i$ are equivalent to
$$
|v|^2=|u|^2,\qquad
r_i\cdot v-s_i\cdot u=(|r_i|^2-|s_i|^2)/2.
$$
The rows for $i=2,5$ give the horizontal part of $v$ as an affine function $c+Mu$ by Cramer's rule. At $j=3,4$ take the prescribed $u=p_j$ and the square root of $|u|^2-|c+Mu|^2$ with signs $+,-$, respectively. The remaining vertices $j=0,6,7$ each have all five core vertices as neighbors.

For clarity, the leaf calculation can be reproduced with two-dimensional vectors. Write $h_i=(r_i)_z$, $w_i=(r_i)_{xy}$, $a_i=s_i-M^Tw_i$, and $b_i=(|r_i|^2-|s_i|^2)/2-w_i\cdot c$. The remaining linear equations are $h_i v_z=a_i\cdot u+b_i$ for $i=3,4$. Put
$$
n=h_4a_3-h_3a_4,\quad k=h_4b_3-h_3b_4,\quad
u_0=-kn/|n|^2,\quad u'=(-n_y,n_x).
$$
Take $u=u_0+tu'$ and $v=(c+Mu,(a_3\cdot u+b_3)/h_3)=v_0+tv'$. The norm equation is $at^2+bt+c_0=0$, with
$$
a=|v'|^2-|u'|^2,\quad b=2(v_0\cdot v'-u_0\cdot u'),\quad c_0=|v_0|^2-|u_0|^2.
$$
In $t=(-b\pm\sqrt{b^2-4ac_0})/(2a)$ use signs $+,-,+$ in leaf order $0,6,7$. Substitution now proves the 24 edge equations identically. [Radical reconstruction in Lean](../../OrigamiTorus/EightVertex/Type5/RadicalChart.lean)

The following bounds record the numerical part of the proof as inequalities on rationals. Enclose each of $(p_x,p_y,r_x,r_y,r_z)$ in $2^{-30}[N-1,N+1]$ for the integer $N$ in its column.

| Vertex | $p_x$ | $p_y$ | $r_x$ | $r_y$ | $r_z$ |
|---|---:|---:|---:|---:|---:|
| 0 | 536869725 | −610604172 | −103832497 | −806402734 | 1476 |
| 1 | 0 | 0 | 0 | 0 | 0 |
| 2 | 249430016 | −816197852 | 249430016 | −816197852 | 0 |
| 3 | 536870912 | 135329836 | 456214557 | −313697683 | 2565591 |
| 4 | −100663296 | 228139078 | 158583508 | −184710882 | −53978692 |
| 5 | −287309824 | −635424776 | −287309824 | −635424776 | 0 |
| 6 | 254581575 | 725656030 | −13841047 | −768891230 | −1775918 |
| 7 | −49358580 | 30428902 | 55447943 | −16959782 | 280973 |

One way to check the integer table is to use denominator $D=2^{256}$. Start with the stated bounds on $x,y^2$ and the rational core table. For a product take the minimum and maximum of the four endpoint products, rounding outwards to multiples of $1/D$. For a reciprocal reverse and invert its endpoints after checking that they have one strict sign. For a square root of $[l,h]/D$ use $[\lfloor\sqrt{lD}\rfloor,\lceil\sqrt{hD}\rceil]/D$. Apply these rules to the two-by-two solve and then the formulas above. The squared heights at 3 and 4 exceed $5\cdot10^{-6}$ and $2\cdot10^{-3}$. The leaf discriminants at 0, 6 and 7 exceed $4\cdot10^{-4}$, $8\cdot10^{-14}$ and $2\cdot10^{-12}$, respectively. All three divisors $2a$ and $|n|^2$ exclude zero. The formal proof uses the same enclosure principle with the library's 120-bit reciprocal and square-root bounds. [Interval operations](../../OrigamiTorus/EightVertex/Type5/BoxArithmetic.lean) · [Chart enclosures](../../OrigamiTorus/EightVertex/Type5/ChartBounds.lean)

For each face $ijk$, take the determinant of $p_j-p_i+K_{ij}$ and $p_k-p_i+K_{ik}$. Direct substitution of the integer intervals gives a lower bound of $7/1000$ for all sixteen determinants. The spatial intervals give the seventeen signs of the separation theorem, each with absolute value greater than $4\cdot10^{-7}$. For example, the smallest is $[0125]$ and its enclosure lies between $467\cdot10^{-9}$ and $470\cdot10^{-9}$. These last determinants use only integer products once the coordinates are enclosed.

The shifts cancel around each face. They induce the fixed degree-one marking of the torus, and the signed double areas sum to $2y$. Positive face orientations make every interior preimage contribute local degree one. At an edge the two adjacent oriented triangles develop on opposite sides, and at a vertex the positive link winds at least once. Degree one therefore makes the development a homeomorphism onto the lattice quotient. The matching three edge lengths on each face imply equality of its two Gram matrices by polarization, hence equality of distances for all pairs of points in that face. Composing the inverse development with the spatial embedding proves the oblique-box theorem. [Degree and facewise metric in Lean](../../OrigamiTorus/EightVertex/Type5/ContinuationTorus.lean)

## Scope of the comparison

The determinant theorem makes no assumption on periods. Applying it at every off-ray modulus requires a construction attaining the seventeen signs and positive marked face areas at each modulus. The oblique-box theorem supplies these data on the box displayed above. A successive-fold construction gives a separate hand proof throughout the off-ray region. Its parameter-dependent perturbation argument is only partially formalized. The existing global certificates cover that region and the open sharp ray. Existence for the hexagonal torus remains open. [Off-ray hand construction](Type5OffRayConstruction.md) · [Global off-ray certificate](Type5FoldedModuli.md) · [Sharp-ray certificate](Type5SharpEmbeddings.md) · [Leaf completion hand proof](Type5PositiveCycle.md) · [Palomar statements](../../palomar/OrigamiTorus/EightVertex/Type5/Challenge.lean)
