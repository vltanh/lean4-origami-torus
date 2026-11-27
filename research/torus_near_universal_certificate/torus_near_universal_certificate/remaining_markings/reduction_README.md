# Finite polynomial reduction for the remaining universal-triangulation problems

This is an exact reduction, not a solved universality classification. Run `python generate.py` with Python 3 and SymPy. It enumerates the winding markings and automorphism orbits, and produces 15 QF_NRA SMT-LIB systems and cases.json. The systems have 18 geometric real unknowns and one (ray) or two (interior) modulus parameters. The optional `python parse_check.py` uses the system libz3 library to confirm syntax; all 15 parsed. No SMT satisfiability or quantified coverage result is claimed. To test a specified metric, insert assertions fixing x (if present) and w before `(check-sat)`. For Type 4 interior, one may restrict to x>9/20 after the separately certified wide strip. To prove universality on a parameter region, prove for every parameter in the region that the disjunction of the case systems admits an existential geometric solution. Nonuniversality requires a parameter for which every applicable case is infeasible. Merely finding SAT at some parameter is insufficient.

## 1. The winding bound

An embedded piecewise affine isometric torus has the following useful property: every edge is the **unique** shortest intrinsic path between its endpoints (up to parametrization). Its image is the Euclidean segment, so its length is the Euclidean distance and no surface path is shorter. Any second equal-length shortest path would have image contained in that same segment with identical traversal, contradicting injectivity. This holds without general position assumptions.

Normalize the reduced lattice basis to (1,0) and (x,y), where 0<=x<=1/2, y>0, x^2+y^2>=1. Write w=y^2. Let (X,Y) be the physical displacement along an intrinsic edge in the universal cover. By the strict nearest-lattice-point inequalities for the three nonzero lattice vectors (1,0), (x,y), (x-1,y),

    |X| < 1/2,
    |x X + y Y| < (x^2+w)/2,
    |(x-1) X + y Y| < ((x-1)^2+w)/2.

Taking the convex combination of the latter bounds with weights 1-x and x gives |Y/y| < 1/2+x(1-x)/(2w) <= 2/3. A closed three-edge cycle therefore has period (m+n*x,n*y), with integer m,n, |n|<2, |m+n*x|<3/2. A noncontractible three-cycle must have nonzero period. For x<1/2 the possible periods in lattice coordinates belong to

    V1 = {+/- (1,0), +/- (0,1), +/- (1,1), +/- (-1,1)}.

For x=1/2 the strict inequality removes +/- (1,1), leaving V0 of size six. The strictness also treats the hexagonal endpoint w=3/4.

## 2. Markings and symmetry

Choose a spanning tree in the 1-skeleton, and an integer cocycle on oriented edges (antisymmetric edge values, zero on the chosen tree, zero sum around each oriented face). The vector space of tree-normalized cocycles is two-dimensional. Compute a rational nullspace basis, verify that its entries are integers (the free coordinates are unit coordinate vectors, so it is an integral basis of the integer solutions), and choose two triangular cycles on which the resulting 2x2 evaluation matrix has determinant +/-1. This gives an integral homology basis. Changing to its dual basis makes the cocycle matrix C evaluate to the identity on these cycles. An intrinsic torus realization identifies H_1 with the lattice, hence its marking is a unimodular integer 2x2 matrix M. Its two rows must belong to V0 or V1, and the same must hold for the images of every nonzero three-cycle class.

`generate.py` enumerates every candidate M, all automorphisms by the 8! vertex permutations, and their induced action on H_1. It quotients by these and by -I on the lattice; at x=1/2 it also uses the two coordinate reflections preserving the lattice. The latter are valid for all w>=3/4, including the hexagonal endpoint (no extra endpoint symmetries are needed). The resulting orbit counts are:

| Type | x<1/2 raw | x<1/2 orbits | x=1/2 raw | x=1/2 orbits |
| 4 | 24 | 6 | 12 | 2 |
| 5 | 24 | 2 | 12 | 1 |
| 7 | 40 | 10 | 24 | 4 |

The Type 7 interior is not emitted, because the Doyle-Schwartz near-universality theorem plus the previously certified rectangular family covers it. For other types all the relevant cases are emitted. The orbits are exhaustive for the necessary winding conditions, not assertions of geometric realizability.

## 3. Eighteen-variable exact feasibility systems

For a fixed marking M, write p_i=(a_i,b_i) for lifted intrinsic vertex coordinates in the lattice basis, with p_0=(0,0). Tree edges can be made to have zero integral shifts by the arbitrary choice of vertex lifts. The face cocycle determines the remaining shifts K=C M. The oriented displacement for edge ij is (a_j-a_i,b_j-b_i)+K_ij. Its squared intrinsic length is the polynomial

    d_ij = (u_ij + x*v_ij)^2 + w*v_ij^2.

There are 14 free intrinsic coordinates. The graph has 24 edges; introduce four independent positive squared distances for the four missing edges of K8. No other geometric real variables are needed. The PL map to the lattice torus defined by these coordinates and shifts is continuous (face cocycle sums vanish). Its induced map on H_1 is M, hence its degree is +/-1. Require that all 16 oriented intrinsic face areas have the same strict sign. The map is locally orientation-consistent across edges; around each vertex it has local positive covering multiplicity when orientations are chosen to match its degree. Every regular value has exactly one preimage by the degree formula. Local openness at vertices follows from the cyclically ordered positive turns, each in (0,pi), with positive integral winding. Thus degree one and nondegenerate consistently oriented faces make this map a homeomorphism onto the target torus. In particular the metric built from these triangles is precisely the desired flat torus.

Form the centered seven-by-seven Gram matrix

    G_ij = (d_0i + d_0j - d_ij)/2  (1<=i,j<=7).

An extrinsic realization in R^3 exists exactly when G is positive semidefinite of rank at most three; rank exactly three is necessary for an embedded closed torus, which cannot lie in a plane. The systems implement PSD rank three with five pivot branches: fix the two vectors of a nondegenerate face at vertex 0, and choose a third vector to make a positive-definite 3x3 principal block A. Sylvester's criterion gives three strict inequalities. The ten entries of the complementary Schur block must vanish, expressed by bordered 4x4 determinants. In each branch these equations and strict inequalities are equivalent to PSD rank three. They remain valid for coplanar subsets.

## 4. Exact embedding constraints, including degeneracies

Extend G by a zero row and column at vertex 0; let B=1*1^T+G_extended be the Gram matrix of the augmented points (1,p_i^extrinsic). It is PSD with rank four. A finite simplicial complex with nondegenerate faces is embedded if and only if convex hulls of disjoint nonempty simplices never meet: in an unintended intersection of simplices with shared vertices, cancel common barycentric weights to obtain two disjoint supporting faces with intersecting convex hulls.

If two disjoint simplices intersect, choose a sign-compatible affine dependence supported on a minimal set of vertices S. Minimality gives a one-dimensional kernel of B_S and no zero coefficients (otherwise an independent kernel vector could be used to reduce the support while keeping the same coefficient signs). Thus |S|<=5, all proper principal submatrices of size |S|-1 have positive determinant, and det B_S=0. The adjugate of B_S is a positive scalar multiple of the outer product of the dependence vector with itself. Its first-row off-diagonal cofactors identify exactly which coefficients have the same or opposite signs as the first one. Conversely such a circuit with the required sign partition gives an intersection, by normalizing positive and negative coefficients to sum one. Hence the generator forbids each partition of each circuit-sized subset into disjoint simplices by an exact polynomial Boolean condition. This handles collinear and coplanar configurations, not just uniform oriented matroids. Together with the Gram and intrinsic conditions this is necessary and sufficient for an embedded isometric realization of the given marking and target lattice.

## 5. What remains

The systems were generated and syntax-checked, not solved. Nonlinear feasibility and quantified coverage can still be hard. The finite winding reduction removes an otherwise unbounded search over lattice basis changes; it does not imply that every remaining polynomial case is easy. The Type 7 sharp ray has four marking orbits, not four discrete configurations: each orbit is a continuous semialgebraic feasibility problem. The exact certificate for Type 4's wide strip is separate. Direct numerical searches and a two-diagonal-flip construction did not close the remaining cases. No independent audit or novelty review is claimed.
