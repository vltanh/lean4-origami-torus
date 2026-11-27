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
