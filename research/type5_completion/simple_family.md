# Constructive Type 5 family with small rational core

**Positive result (research proof, not yet Lean).** The same explicit core
and five radical choices give an embedded Type 5 torus for every modulus
in the union of

    x = 0, 1 <= y <= 41/40
    0 <= x <= 1/1024, 1 <= y <= 513/512.

This covers infinitely many moduli, including an open two-dimensional set
of nonrectangular moduli. It does not settle Type 5 universality. The earlier
hexagonal and elongated exclusion ledgers are not used.

## 1. Construction

Take the periods (1,0),(x,y) and the exact square marking in
OrigamiTorus/Type5/Square.lean, with shifts zero out of vertex 1. Write
K_ij for the physical period displacement. Fix e=2^(-20). In physical
intrinsic coordinates choose

    p1 = (0,0)
    p2 = (43/96, ((e-1/2)*(x^2+y^2)-(43/96)*x)/y)
    p3 = (1/2-e, 3*y/32)
    p4 = (-1/12, 7*y/16)
    p5 = (-1/32, -5*y/32).

The formula is motivated by the near-ties of edges 12 and 13: the
projection of p2 onto the second period is e-1/2 times its squared
length, and that of p3 onto the first is 1/2-e. The other six constants
are small fractions, not long fitted decimals. The small e is necessary
for this particular candidate to work; the exact ties themselves are
not asserted to give an embedding.

Let r1,r2,r5 be the intrinsic anchors placed at height zero. Form the
2-by-2 matrix A with rows p2^T,p5^T, and D=det A. For a vertex j with
intrinsic point u, define s_i=p_i-K_ij and c_i=(||p_i||^2-||s_i||^2)/2.
The linear map

    P_j(u) = A^(-1) [s_2.u+c_2, s_5.u+c_5]^T

gives the horizontal part of r_j. For roots 3 and 4 use

    r_j = (P_j(p_j), sigma_j sqrt(||p_j||^2-||P_j(p_j)||^2)),
    (sigma_3,sigma_4)=(+1,-1).

For leaf j in (0,6,7), write P_j(u)=M u+c. For each root i=3,4 define

    a_i = s_i-M^T r_i,xy,
    b_i = c_i-r_i,xy.c,
    z_i = r_i,z.

The two remaining subtracted length equations are z_i v_z=a_i.u+b_i.
Set l=z4*a3-z3*a4, m=z4*b3-z3*b4, and

    u0 = -m*l/||l||^2,
    du = (-l_y,l_x),
    v0 = (M*u0+c, (a3.u0+b3)/z3),
    dv = (M*du, a3.du/z3).

Choose u=u0+t*du, v=v0+t*dv, where t solves the one remaining quadratic

    q(t)=||v0+t*dv||^2-||u0+t*du||^2 = alpha*t^2+beta*t+gamma.
    t = (-beta + sigma sqrt(Delta))/(2*alpha),
    (sigma_0,sigma_6,sigma_7)=(+1,-1,+1).

This is the same geometric reconstruction as the existing square witness.
Every required denominator is checked nonzero. The five radical choices
satisfy all 24 marked edge lengths by construction. There is no iterative
numerical solve in the definition of the family.

## 2. A stable discriminant identity

The new identity makes a uniform certificate practical near the ties.
Use the quadratic form Q(v,u)=||v||^2-||u||^2 on R^(3,2), with bilinear
form B and diagonal matrix J=diag(1,1,1,-1,-1). In this section B is the
bilinear form, not the scale factor of the interval code.

For a leaf let C_i=(r_i,s_i), i in (1,2,5,3,4). C_1=0. Define the
5-by-5 signed deficit matrix

    S_ik = -Q(C_i-C_k)/2.

The diagonal and consecutive pairs in the leaf link are zero by the
marked face cocycle and the core length identities. The complementary
five pairs form a five-cycle (checked for all three leaves). Consequently

    det S = 2 * product of its five complementary entries.

This follows directly by determinant expansion: in the zero-diagonal
five-cycle matrix the only nonzero permutations are the two directed
five-cycles. The entries are computed as half a squared-length
difference. For a core edge ik, the expression is just

    S_ik = d.h + ||h||^2/2,
    d = p_k-p_i+K_ik, h=K_ij-K_kj-K_ik.

The root pair 34 is computed directly; it is the only missing core edge.

**Claim.** For the quadratic q(t) above,

    Delta = beta^2-4*alpha*gamma = 4*det S/D^2
          = 8 * product of the five entries / D^2.

Proof. Put Z=(v,u)=Z0+t*N with N=(dv,du). The four linear
equations B(C_i,Z)=Q(C_i)/2 have coefficient matrix T whose rows
are C_i^T J for i=2,5,3,4. The cofactor null vector of T, with entries
(-1)^k det(T with column k deleted), k=0,...,4, equals D*N.
Indeed, elimination of the two anchor coordinates leaves the two root
equations; the last two cofactors are -D*l_y and D*l_x. Since l is
nonzero, T has rank four, and its null vector is determined by these
coordinates. Write W for the 5-by-4 matrix of those four core vectors.
Cauchy--Binet, using det J=1 and the diagonal signs of J, gives
det(W^T J W)=D^2*Q(N).

For every Z on the affine line the Gram matrix of the five columns
C_i-Z is S+Q(Z)*11^T. Its determinant is the square of the ordinary
column determinant (det J=1). Subtracting the first column from the
others reduces this determinant, up to sign, to that of [W,Z].
The same cofactor vector gives its square as D^2*B(N,Z)^2.

On the other hand, subtracting the first row and column of the Gram
matrix from the other rows and columns shows that its determinant is
det S+Q(Z)*det(W^T J W). Therefore

    det S = D^2*(B(N,Z)^2-Q(N)*Q(Z)).

At Z=Z0 the right hand side is D^2*(beta^2/4-alpha*gamma),
proving the claim. This argument does not assume a real leaf completion
already exists. All five deficit factors are strictly positive on the
certified domains. This product is far more stable than subtracting
nearly equal terms of the discriminant.

## 3. Certification

The standard-library verifier verify_simple_family.py uses 100-bit
outward-rounded integer intervals. For two parameters it propagates both
value and partial-derivative intervals, together with an independent
midpoint value. Each value interval is intersected with the multivariate
mean-value enclosure. All operations, including square roots, round
outwards. Differentiation uses the product, quotient and square-root
rules on their certified domains. Strict sign checks reject an interval
on which any required denominator, radicand, face area, or determinant
cannot be separated from zero. Each failed box is split at a rational
midpoint along its wider coordinate. Every accepted box covers its
boundary, and the entire initial box is covered once the frontier is
empty. The integer signs, not the printed decimal values, are the proof.

The proof checks all 16 intrinsic face determinants strictly positive,
the cocycle and signed double-area identity 2*y, and all 70 spatial
affine four-point determinants strictly nonzero. The area identity
is exact: opposite directed sides cancel the terms quadratic in vertex
coordinates, the linear coefficients cancel by the link cocycles,
and the constant sum of determinants of integer shifts is 2.
The physical period map multiplies it by y. Thus the intrinsic
periodic map has degree one; its locally open face charts give the
flat torus as in docs/Type5.md.

All 138 disjoint edge-face pairs are separated by the signs of the
unique five-point affine dependencies. For an intersection beyond a
common simplex, cancel common barycentric coordinates and reduce the
resulting disjoint supports by an affine dependence until their union
has size at most five. General position then forces size five, with
two vertices on one side and three on the other. The checked
edge-face pairs exclude this, establishing embeddedness. This also
rules out shorter alternative edge lifts, by global contraction and
injectivity, without needing an additional nearest-lift margin test.

Replay:

    python3 research/type5_completion/verify_simple_family.py

Local tests of the verifier (with the actual square shift and face
tables transcribed from the existing Lean witness) returned:

    rectangle [1,131/128]: 188 accepted boxes, max depth 8
    rectangle [131/128,41/40]: 16 accepted boxes, max depth 4
    box [0,1/1024] x [1,513/512]: 256 accepted boxes, max depth 8

The square point check returned minimum oriented double area greater
than 0.0388 and minimum absolute affine determinant greater than
0.0000630. The latter is substantially larger than the old square
witness's roughly 5.6e-8. Each accepted box checks all 138 separations.
The code also compares the product discriminant against the original
quadratic discriminant at the square point as a regression check.
The two rectangular pieces and the box were run separately to fit the
local execution limit. No Lean build or new formal theorem is claimed.

## 4. Next constructive gate

This is a simpler parametrized family, not an elementary universal
construction. The near-tie template and the discriminant product
suggest a systematic construction: choose simple formulas for the
six remaining core parameters in terms of the modulus, keep both
near-tie margins positive, and control all five radical branches and
embedding signs over complete modulus regions. Numerical continuation
of the same branch suggests other rectangles are accessible but has
not been certified. The displayed constants are only proved on the
domains above. In particular, the hexagonal point and arbitrarily
elongated moduli remain unconstructed.
