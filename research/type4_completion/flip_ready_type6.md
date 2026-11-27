# Constructive pivot: a flat diagonal exchange from Type 6

Status: a sufficient geometric route, not a Type 4 realization on the sharp ray.
The eight fixed-target exclusions remain open. Do not interpret a failed
search within the flip locus as nonuniversality.

## 1. Exact combinatorics

With the standard Lutz labels, the only legal diagonal flips of Type 6
whose resulting triangulation is isomorphic to Type 4 are:

| Old edge | New edge | Relabel old vertex 0,...,7 to Type 4 |
|---|---|---|
| 45 | 06 | 24607153 |
| 16 | 34 | 01234576 |

For a genuine embedded flat Type 6 torus, either flip is an isometric
retriangulation if its four spatial vertices make a strictly convex planar
quadrilateral with the two old faces as its triangulation. The intrinsic
quadrilateral is congruent to that spatial quadrilateral, since the
individual triangles are isometric and lie on opposite sides of the common
edge. The underlying embedded surface, its cone angles, and its lattice
are unchanged. In particular one need not solve any new Type 4 equations
at the exact flip.

The two diagonals must intersect in their relative interiors. Equivalently,
for old edge ab and opposite vertices c,d, require
    (1-s) r_a + s r_b = (1-t) r_c + t r_d,  0<s,t<1,
with the four vertices spanning an affine plane. Alternatively, solve the
single scalar coplanarity equation det(r_b-r_a,r_c-r_a,r_d-r_a)=0 and test
strict convexity. Coplanarity alone also includes folded-over,
nonflippable quadrilaterals.

## 2. A flip preserves fixed-period length regularity

This is a useful local theorem beyond the combinatorial observation.
Write E_ij and I_ij for squared spatial and intrinsic edge lengths, with
the relevant period shift included in I. Let R_ij=E_ij-I_ij.
Suppose an embedded fixed-period Type 6 solution has a strictly convex
coplanar flip quadrilateral, and its fixed-period length-residual derivative
in the chosen spatial/intrinsic variables is surjective onto R^24.

On the quadrilateral, choose a nonzero affine dependence lambda:
    sum_i lambda_i=0,   sum_i lambda_i r_i=0.
Every coefficient is nonzero because a strictly convex quadrilateral
has no collinear triple. The coherently lifted intrinsic quadrilateral is
congruent to the spatial one and has the same affine dependence.

For arbitrary vertex velocities v_i, the exact linear identity
    sum_{i<j} lambda_i lambda_j
        (r_i-r_j) dot (v_i-v_j) = 0
follows by expanding and using both affine-dependence equalities.
Apply it to the spatial and intrinsic velocities and subtract. Thus
    sum_{i<j} lambda_i lambda_j dR_ij = 0.
This is a relation among the six squared-length residual rows of the
complete quadrilateral, valid also for arbitrary out-of-plane spatial
velocities. The four boundary-edge rows remain in the new triangulation.
Both diagonal coefficients are nonzero. Replacing the old diagonal row
by the new one is therefore an invertible elementary row replacement.
Surjectivity is preserved; any nonsingular 24-column minor for the old
system is still nonsingular in the new system.

The implicit function theorem now solves the Type 4 residual equations for
all nearby lattice periods. Embeddedness is open and the developed
intrinsic triangulation is preserved locally by strict face orientation
and degree one. Hence a regular flip-ready Type 6 solution gives not just
one Type 4 modulus, but an open neighborhood of moduli. The theorem is
conditional on length regularity at the flip-ready solution; the known
rank theorem for one Type 6 construction does not establish it on the
entire Type 6 solution space.

## 3. Why not just change diagonals in the published planar family?

The published Type 3 folding pattern (Doyle--Lander--Schwartz--Trettel,
arXiv:2611.21909, Section 3.2) can be encoded using the oriented face list
    012 031 024 043 152 136 145 174 167 264 257 276 347 356 375 465
with signs
    +--+++++-+----+-.
A strictly convex, metric-preserving planar diagonal exchange must occur
at a noncrease: the two incident faces have the same folding sign. Indeed,
opposite signs put the two folded triangles on the same side of their
shared edge. Relaxing all convexity and distance restrictions, enumerate
all legal equal-sign flips, inheriting that sign on both replacement faces.

There are exactly three labeled signed states reachable from this pattern:
the start, its flip 12 -> 05 (the published Type 6 construction), and the
further flip 67 -> 12 in the published labels. The graph is a three-state
path, with no Type 4 state, even up to relabeling. Consequently retuning
the five-parameter family without changing the folding pattern, even with
multiple noncrease flips, cannot produce Type 4.

For comparison, the four Type 3 sign assignments reversing on every
clique-adjacent dual edge, modulo overall sign, have reachable state
counts 20,3,4,4 (lexicographically ordered faces, plus before minus).
Only the first has a Type 4 state, reached by 12 -> 05 then 34 -> 07.
This is a combinatorial possibility, not a geometrically valid family.
In particular it does not give a hexagonal construction, as below.

## 4. A necessary metric identity for that alternate pattern

In the final doubled-flip labels, the two large monochromatic islands are
    A = 013,015,025,136;  B = 024,037,047,246.
They share vertices 0,2,3 with identical coherent lifts and vertex 6 with
lifts differing by one primitive lattice vector L. The two island
isometries have opposite orientations. Normalize the A isometry to the
identity and the B isometry to reflection across the axis through
0,2,3. The lift difference at 6 forces L perpendicular to this axis
and p6 to have signed normal coordinate -|L|/2.

Transporting both sharp-ray marking representatives from type4_gap_enum.py
through the four face-list isomorphisms gives, in the island gauge, the
nonzero edge shifts
    14=17=67=-M; 26=46=L;
    27=56=57=L-M; 35=M-L; 45=M.
Here L,M are lattice basis vectors; at the hexagon they have equal lengths.
For ray 1, |M|<=|L|, and for ray 2, |L|=1 and |M|^2=w+1/4.
These statements were checked by exact integer cocycle transport, not
inferred from an assumed marking for the alternate pattern.

After a similarity write L=(1,0), M=(m,n), n!=0, and write the spatial
planar points
    p0=(0,0), p2=(0,b), p3=(0,c), p6=(-1/2,f),
    p5=(e,E), p7=(g,G).
The intrinsic coordinates of vertices 5,6 are p5,p6 in the A gauge,
whereas vertex 7 has reflected intrinsic coordinate (-g,G).
The three edge equalities 56,67,57 imply
    2*n*(E-f) + 2*e*(m-1) + m*m-m+n*n = 0,
    -2*n*(G-f) + 2*g*(m-1) + m*m-m+n*n = 0,
    2*n*(E-G) + 4*e*g + 2*(e+g)*(m-1)
        + m*m-2*m+n*n+1 = 0.
Subtract the first two equations (or eliminate E and G) to obtain
    4*e*g = m*m+n*n-1.

Nondegeneracy and the intrinsic triangulation at 0 force 2 and 3 to be on
opposite rays along their common line, with the A island and the B island
on opposite sides intrinsically. After reflection their folded vertices 5
and 7 lie strictly on the same side. Hence e*g>0. The actual edges 05 and
07 also have shortest lifts (weak comparisons suffice for a flattened
torus), so |e|,|g|<=1/2. Necessarily
    1 < |M|^2 / |L|^2 <= 2.
This particular alternate pattern therefore cannot produce the hexagonal
metric, any ray-1 sharp modulus, or a ray-2 sharp modulus with w>7/4.
This is not an exclusion of any three-dimensional marking.

## 5. A practical new target

Use the already established regular Type 6 fixed-metric family as a
starting point, and continue *inside the spatial fixed-period solution
manifold*. Seek one of the two coplanarity zeros with convexity and
embeddedness maintained. The dimension near a regular fixed-modulus
Type 6 embedding is eight modulo similarities; a transverse scalar
coplanarity condition reduces it by one. A constrained continuation,
rather than unrestricted global SMT over Type 4 coordinates, can use
this structure. At a candidate, certify the residual equations,
coplanarity, convexity, and the derivative minor by exact or validated
methods, then invoke Section 2.

Start at the hexagonal metric, not y=10^6. A regular flip-ready solution
would cover an interval of sharp-ray heights and could be continued in
height. The unbounded end still needs a uniform family or a separate
argument. No such solution or path has been obtained in this checkpoint.
It is also possible that the flip-ready locus at some modulus is empty
even if Type 4 is universal, so this is a sufficient construction route,
not an equivalent reformulation.

## Reproduction of finite checks

The following standard-library checker enumerates the planar flip orbit,
the two Type 6 -> Type 4 edges, and the alternate-pattern flip path.
The integer marking transport and three edge identities above were
separately checked using exact arithmetic. No Lean theorem or new full
case exclusion is claimed.

```python
from itertools import combinations, permutations, product
from collections import deque
F3='012 031 024 043 152 136 145 174 167 264 257 276 347 356 375 465'.split()
F4='012 031 024 053 045 152 134 146 165 264 257 276 374 356 367 475'.split()
F6='012 031 024 053 045 152 136 164 147 175 274 256 267 357 376 465'.split()
def key(s): return ''.join(sorted(s))
def graph(F): return {''.join(e) for f in F for e in combinations(key(f),2)}
def canon(F): return tuple(sorted(map(key,F)))
targets={canon(''.join(p[int(i)] for i in f) for f in F4)
         for p in permutations('01234567')}
def flips(F):
    E=graph(F)
    for edge in sorted(E):
        faces=tuple(f for f in F if set(edge)<=set(f))
        assert len(faces)==2
        new=key(set(''.join(faces))-set(edge))
        if new not in E:
            yield edge,new,faces
assert sorted((e,n) for e,n,ff in flips(canon(F6))
              if canon([f for f in canon(F6) if f not in ff]+
                       [a+n for a in e]) in targets)==[('16','34'),('45','06')]
def search(start):
    seen={start}; queue=deque([start])
    while queue:
        s=queue.popleft(); D=dict(s)
        for e,n,ff in flips(D):
            if D[ff[0]]!=D[ff[1]]: continue
            G=D.copy(); sign=G.pop(ff[0]); G.pop(ff[1])
            G.update({key(a+n):sign for a in e})
            state=tuple(sorted(G.items()))
            if state not in seen: seen.add(state); queue.append(state)
    return seen
start=tuple(sorted((key(f),s) for f,s in
                   zip(F3,'+--+++++-+----+-')))
states=search(start)
assert len(states)==3
assert not any(tuple(f for f,s in state) in targets for state in states)
F=canon(F3); E=graph(F)
clique=[]
for edge in E:
    ff=[f for f in F if set(edge)<=set(f)]
    if key(set(''.join(ff))-set(edge)) in E:
        clique.append(tuple(F.index(f) for f in ff))
patterns=[tuple(zip(F,('+',)+ss)) for ss in product('+-',repeat=15)
          if all((('+',)+ss)[i]!=(('+',)+ss)[j] for i,j in clique)]
assert len(patterns)==4
assert [len(search(p)) for p in patterns]==[20,3,4,4]
assert [sum(tuple(f for f,s in q) in targets for q in search(p))
        for p in patterns]==[1,0,0,0]
print('PASS flip enumeration and noncrease retriangulation orbits')
```


## 6. Exact intrinsic flip families on the entire sharp ray (new)

For the published Type 6 construction's marking, **both proposed flips
are intrinsically possible at every sharp-ray modulus**. There is no
shortest-lift or convex-intrinsic-quadrilateral obstruction.

Use the published labels of Defs.lean, rather than the Lutz labels in
section 1. The two ordered quadruples (old diagonal a,b; new c,d) are
(5,7,2,3) and (3,4,0,7). The new cocycles on c->d are respectively
(-1,1) and (0,-1). In both cases the cocycle is obtained by adding the
two shifts along c->a->d, equivalently c->b->d.

Put W=y^2 >= 3/4, use periods h=(1,0), g=(1/2,y), and place the
intrinsic vertices at q_i=(X_i,y*b_i(W)). Here
    b(W) = b_infty + (3/(4W))*(b_hex-b_infty).

The following exact vectors are listed in vertex order 0,...,7.

| Old/new diagonals | 10 X | 30 b_hex | 30 b_infty |
|---|---|---|---|
| 57 / 23 | 0,2,-3,2,3,-1,5,5 | 0,4,2,-12,18,14,-2,14 | 0,4,4,-11,19,13,-5,10 |
| 34 / 07 | 0,2,-2,1,2,-1,4,5 | 0,4,4,-10,20,14,0,14 | 0,0,0,-10,15,15,0,15 |

Every old and new oriented face has positive normalized double area at
both endpoints of the interpolation, so it is positive throughout. The
sum is exactly 2 for both triangulations. The new pairs of faces are
532,723 and 307,470 respectively. Their boundary orientations agree
with the old pairs. The coherent face lifts with positive areas and
degree one give the actual intrinsic triangulations of the flat quotient
(by the same open-development and area argument used in Type6.md).
Positivity for both triangulations of the same coherently lifted quad
proves that both diagonals cross in their relative interiors, hence the
quad is strictly convex.

Write (X,y*b) for a marked edge displacement. The squared-length gap to
a competitor displaced by m*h+n*g is
    G(W) = 2*X*(m+n/2)+(m+n/2)^2+W*(2*n*b+n^2).
For the displayed interpolation this is affine in W. Its slope is
nonnegative since |b_infty|<=1/2. The exact checker verifies all gaps
for -1<=m,n<=1, not both zero, at W=3/4; the minimum is 1/5.
Also |X|<1/2 and |b_hex|<2/3. At the endpoint, |n|>=2 gives a vertical
contribution strictly greater than (3/4)*(4-8/3)=1, whereas the horizontal
contribution is >=-X^2>-1/4. For n=0, +/-1 are enough by |X|<1/2.
For |n|=1, a nearest horizontal translate is among m=-1,0,1; the
other translates only increase the squared length. Thus all competitors
have strictly positive gaps at the endpoint, and nonnegative slopes
prove strict shortestness for every finite W>=3/4. In particular the
removed edge and the proposed inserted edge are both strictly shortest.

The exact standard-library checker [flip_intrinsic_exact.py](flip_intrinsic_exact.py)
passed for both rows. The minimum normalized face-area lower bounds
are 4/75 and 1/20. The data are purely intrinsic: they are not
three-dimensional origami witnesses.

## 7. A smaller, complete reconstruction on the spatial flip-ready locus

This reduction covers every embedded Type 6 realization in the published
marking which has one of the two strictly convex planar quadrilaterals,
including the exceptional linear charts below. It is not an equivalent
reformulation of arbitrary Type 4 existence.

Fix the intrinsic positions of the four quadrilateral vertices, using
coherent lifts A_a,A_b,A_c,A_d in R^2. Put the four spatial vertices at
(A_j,0) by a rigid motion. Every other vertex i has three or four
neighbors in the quadrilateral:

| Quad | 3-neighbor vertices | 4-neighbor vertices | Edges outside quad |
|---|---|---|---|
| 57 / 23 | 0,1 | 4,6 | 01,04,14,16,46 |
| 34 / 07 | 2,6 | 1,5 | 15,16,25,26,56 |

For i outside the quad let p_i be an intrinsic lift, and T_ji the
integer lattice translation making the marked edge from A_j to p_i
coherent. Put D_ji=|p_i+T_ji-A_j|^2. Pick any three anchor neighbors
j0,j1,j2. Strict convexity makes those three centers noncollinear.
Subtract the squared-distance equation at j0 from those at j1,j2:
    2 (A_j-A_j0) dot U_i = |A_j|^2-|A_j0|^2-D_ji+D_j0i.
The projection U_i of the spatial vertex onto the quad plane is uniquely
determined. The squared signed height is
    H_i = D_j0i-|U_i-A_j0|^2.
For each 4-neighbor vertex impose the same polarized equation for its
fourth neighbor. These two compatibility equations are linear in p_i
once the quad is fixed: the quadratic |p_i|^2 terms cancel.

**All four H_i are strictly positive in a genuine solution.** The
strict-K4 proof in global_attack_support.md applies without change to
Type 6: the checker verifies that every closed neighborhood in its
edge graph contains a K5. Thus no planar vertex star is possible; a
planar K4 would put one vertex strictly inside the opposite triangle,
force its flat spherical link into the same plane by equality in the
angular triangle inequalities, and contradict the K5. After the flip
the same proof applies to Type 4. For every outside vertex the checker
finds a triple of its quad neighbors forming a K4 with it in one of the
two triangulations. Hence none of these heights can vanish. This is
a strict statement, not a quantitative height lower bound.

For each of the five outside edges ij, write d_ij for its marked
intrinsic squared length and
    P_ij = (|U_i-U_j|^2+H_i+H_j-d_ij)/2.
Its metric equation is precisely z_i*z_j=P_ij for the actual signed
heights. Since all H_i>0, the necessary equations
    P_ij^2=H_i*H_j
are sufficient for the absolute values of the five products. It remains
to require that the product of P_ij on each of the two outside triangles
be strictly positive. The outside graph is K4 with one edge missing;
its two triangles form a cycle basis. Thus these sign tests are necessary
and sufficient for assigning signs to the four square roots. Choose a
positive square root at one root vertex and propagate along the graph.
All five products are correct, uniquely up to a common sign reversal.

The entire metric part now consists of **two linear compatibility
equations and five rational product equations** in 14 intrinsic
coordinates (quad translation gauged away), with H_i>0 and two sign
inequalities. No free spatial coordinate or radical variable is needed
for the metric search. The reconstructed height signs are unique up to
reflection. Intrinsic shortestness, orientations and degree, convexity
and complete spatial simplex nonintersection remain required. The
five equations alone do not imply these tests.

### Uniform 12-parameter bound, including exceptional charts

The quad has six real parameters. Use its intersection parameters
0<s,t<1 and the two diagonal vectors. Its unique affine dependence
has coefficients
    lambda=(1-s,s,-(1-t),-t)
in the order (a,b,c,d). A 4-neighbor compatibility equation is also
    sum_j lambda_j * (|p_i+T_ji-A_j|^2-|A_j|^2)=0.
The coefficient of p_i is 2*sum_j lambda_j*T_ji.

In the published marking, in units (h,g) and the indicated quad order,
the checker gives the relative shift tables
    quad 57/23, i=4: (0,0),(-1,0),(0,-1),(-1,0)
    quad 57/23, i=6: (0,0),(0,-1),(0,-1),(0,0)
    quad 34/07, i=1: (0,0),(0,-1),(0,0),(0,-1)
    quad 34/07, i=5: (0,0),(-1,0),(-1,1),(0,0).
A common translation of all four shifts has no effect on the coefficient.

For i=4 in the first quad and i=5 in the second, the g coefficient
is respectively -lambda_c and lambda_c, which is nonzero. For the
other 4-neighbor vertex the coefficient is a multiple of g: it
vanishes precisely at s+t=1 for the first quad, or s=t for the second.
Away from the exceptional equality each compatibility equation
eliminates one outside intrinsic coordinate. There are 6+8-2=12
independent real parameters before the five metric equalities. At the
exceptional equality one quad parameter is eliminated instead; retain
both intrinsic coordinates for that outside vertex and enforce the
remaining constant compatibility condition. The parameter count is still
at most 12. This is a finite collection of rational charts, by choosing
a nonzero coordinate of the linear coefficient and retaining the
exceptional strata. It requires no positive lower bound on a quad area,
coefficient, or height.

The reduction is uniform in y on the sharp ray, not a computation for
one approximate fixed configuration. It remains conditional on the
existence of a spatial flip-ready Type 6 embedding in this marking.

## 8. Initial hexagonal numerical attempts (not certificates)

Two exploratory computations at x=1/2, W=3/4 were made using SciPy
least_squares, double precision:

* Starting from the small-height Type 6 implicit-function seed in
  published labels, optimize the 24 fixed-period length residuals plus
  the three diagonal-intersection residuals, penalizing incorrect
  intrinsic areas, nearest-lift gaps and edge-face circuit signs.
  The best reported weighted residual norms were 3.83e-6 and 3.83e-6
  for the two flips; the candidates had 4 and 5 crossing edge-face pairs,
  respectively. These very small residuals approach degenerate
  configurations and are not embeddings. This was a constrained
  optimization from the seed, not a certified continuous deformation.
* A separate planar-anchor implementation enforced the quad
  parametrically, solved the three-anchor polarization equations for
  every outside projection, and kept four signed heights as auxiliary
  variables for numerical conditioning. Its 11 exact residuals were
  four radial, two compatibility and five outside-edge equations.
  All eight sign choices modulo reflection were tried for each flip
  from the exact intrinsic seeds above with small perturbations,
  up to 120 least-squares evaluations per branch. Positive numerical
  area, gap, separation and length margins were penalized; lower
  bounds on the diagonal fractions (0.02), normal component (0.02)
  and heights (0.005) were used for numerical conditioning, not as
  necessary conditions. Best weighted residual norms were 0.00160
  and 0.00245 respectively; their crossing counts were 5 and 23.
  No solution was certified. These are diagnostic optimization runs,
  not a complete search of the reduced chart or an infeasibility
  certificate.

The first diagnostic initialized four and two trials respectively
before the external computation limit; the second attempted all
sixteen sign branches. The exact rational checker in section 6 and
the geometric reconstruction proof, rather than either numerical
experiment, are the new reusable results. The remaining task is
to solve the coupled reduced metric-and-embedding equations with
strict geometric margins and validate a regular solution. No sharp-ray
Type 4 spatial witness, new Lean result, or full case exclusion is claimed.


## 9. The two flips are equivalent; a necessary supporting-plane theorem

**New global restriction.** In the published Type 6 marking the two
candidate flips are equivalent at every modulus. On the entire sharp
ray with y>=2, any flip-ready embedded flat realization in this marking
must have its convex flip quadrilateral on a supporting plane of the
whole torus. The hexagonal flip locus remains open.

### Symmetry

In the published labels the permutation
    p=(2,6,0,7,5,4,1,3)
preserves the Type 6 face set and exchanges old/new diagonals 57/23
with 34/07. If K is the published oriented cochain, set
    g=((0,0),(1,0),(0,0),(1,0),(0,1),(0,1),(1,0),(1,0)).
For every oriented old edge,
    -K[p(i),p(j)]-K[i,j]=g[j]-g[i].
Thus relabeling, central inversion of the lattice, and changing
intrinsic vertex lifts preserves the marked metric problem exactly.
Central inversion is an isometry for every lattice, not just the
hexagonal point group. It suffices to solve the flip 57 -> 23 in this
marking. The Type 4 relabeling after this flip is
    (0,3,2,5,4,1,6,7).

### Exhaustive geometric side dichotomy, including nongeneric embeddings

Use Q=(5,7,2,3), listed in diagonal order, and O=(0,1,4,6).
A strictly convex coplanar Q has a unique affine dependence with
sign parts {5,7} and {2,3}. All four vertices in O lie off its plane
by the strict-K4 argument in section 7.

For the old and new triangulations, the checker verifies a K5 in
every closed vertex neighborhood and a K4 through the vertex in
one of the two closed link arcs for every nonadjacent neighbor pair
(20 cases for each triangulation). These are precisely the finite
hypotheses used in global_attack_support.md. Flatness plus embeddedness
therefore gives strict neighbor support, strict K4s, and no antipodal
pair of neighbor directions in both triangulations.

Strict support puts the spherical link in an open hemisphere.
Central projection to a transverse plane gives a simple polygon.
If every edge of this polygon supports it (all other vertices on
one weak side), the polygon is convex. Its spherical perimeter is
then strictly less than 2*pi: the spherical Crofton formula gives
at most two intersections with almost every great circle, and zero
on an open set of great circles missing the compact hemisphere-contained
polygon. This contradicts flatness. Thus at every vertex some incident
face has other neighbors on both strict sides.

Perturb the four outside vertices, holding Q fixed. Every four-point
determinant other than Q can be made nonzero simultaneously, since
each triple in Q is noncollinear and each such determinant is a
nonzero polynomial in the free outside positions. Embeddedness of
both triangulations persists: each pair of disjoint simplices is
compact and positively separated, and the barycentric subtraction
argument reduces all excess intersections to such pairs. Strict
neighbor support and the strict mixed-side face witnesses persist
too. The perturbation need not preserve the flat metric. In particular,
generic orientation filtering is a necessary test even for actual
solutions with extra coplanarities.

The 69 nonzero brackets obey the three-term Grassmann--Pluecker signs
(retaining the two-term specializations involving the zero bracket),
the unique affine-dependence signs on each five-point set, forbidden
disjoint-simplex intersections and forbidden singleton-in-neighbor-hull
circuits for BOTH triangulations, and the mixed-face test at each vertex.
The explicit convex-Q dependence also determines the relative signs
of the four triples of Q with a common outside vertex. Modulo an
ambient reflection normalizing vertex 0 to the positive side,
the finite Boolean proof leaves precisely these two possible side
patterns in the order O:
    (+,+,+,+), or (+,-,+,-).
All six other side assignments are ruled out by independent exact
Boolean branching in flip_side_certificate.py. The SAT assignments
to the necessary orientation clauses are not assertions of geometric
or metric realizability.

### The mixed-side branch is impossible for y>=2

The disjoint directed triangles (1,7,5) and (3,6,4) in the old Type 6
graph both wind around the horizontal period (1,0). On every generic
mixed-side configuration satisfying the necessary clauses, edge 64
pierces the triangular disk 175 and edges 36 and 43 do not. Each of
the five-point sets in these three tests avoids the coplanar Q. The
checker proves the three claims by forcing the opposite Boolean
circuit conditions and replaying independent exhaustive branching;
no numerical geometry or real SMT result is used.

Thus the horizontal linking q(1,0) has magnitude one in this branch.
The linking number persists under the small perturbation described
above. For an embedded torus it is the linking number of two parallel
horizontal intrinsic geodesics. Every horizontal geodesic has
length one. If their linking is nonzero, their convex hulls intersect;
their diameters are strictly less than 1/2 by the equality case of
the arc-length bound. For arbitrary points on different horizontal
fibers, use a common point of their convex hulls to bound the distance
strictly below one; on a common fiber use its diameter. Compactness
gives extrinsic surface diameter strictly less than one.

After the flip, the four-edge cycle (1,3,2,4) has period (1,-2)
in the checked cochain. Its physical winding vector at tau=1/2+i*y
is (0,-2y). Its intrinsic length equals its sum of spatial edge
lengths. Consequently
    2y <= length(1324) < 4.
Hence the mixed branch necessarily has y<2. For y>=2 the only
remaining side pattern places all four other vertices strictly on
one side of the plane of Q, so Q is a convex supporting face of
the spatial convex hull. The proof includes y=2 and has no
nondegeneration lower bound on the quad's area or outside heights.

### Scope and numerical diagnostics

The exact orientation enumeration (optional libz3 replay) returns
325 necessary bracket sign assignments, 305 same-side and 20
mixed-side. Filtering by horizontal unlinking leaves 149 same-side
assignments for the long tail y>=2. These counts concern generic
orientation relaxations, not 325 metric cases or 176 geometric
exclusions. The side and mixed-link restrictions have a separate
pure-Python DPLL proof. Checking the broader homological linking
forms on 1,210 disjoint-cycle pairs of the two triangulations did
not prune the 325 hexagonal sign assignments.

A new numerical diagnostic used the plane-anchor parameterization,
19 remaining old-edge squared-distance residuals, intrinsic face
areas, nearest-lift gaps for both diagonals and all old edges,
nonedge chord bounds, and 69 signed-bracket penalties. Its analytic
Jacobian was checked against finite differences. The hexagonal
search prioritized all 20 mixed-side sign assignments, then
same-side ones in a seeded order. At least 241 local optimizations
completed before the external time limit. The best logged weighted
residual was about 0.00221 with a wrong bracket sign; no embedded
solution was found. These attempts had numerical margin and
parameter bounds and are not an exhaustive real search or a
nonexistence result.

Reproduce the finite theorem from the repository root:

    python3 research/type4_completion/flip_side_certificate.py

Optional projected counts:

    python3 research/type4_completion/flip_side_certificate.py --enumerate

The constituent side, symmetry, link, and cycle tests were executed
on the equivalent scratch implementation; the repository replay
and Lean formalization remain to be audited. No regular Type 4
spatial witness, full marking exclusion, or new Lean theorem is
claimed. The supporting-plane result reduces the constructive
long-tail target, while the hexagonal target still has two
geometric branches. This result is specific to a flip-ready
solution in the published marking; a Type 4 torus without this
flip is not excluded by it.
