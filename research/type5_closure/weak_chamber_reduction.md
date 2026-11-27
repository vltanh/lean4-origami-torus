# Type 5: complete weak-chamber tests with quadratic metric equations

This is an exact simplification of the remaining embedding tests. It does
**not** prove any new orientation chamber infeasible or finish Type 5
universality. It uses the actual archived sign representatives and the
inherited strict-support/K4 premises. The new finite checker uses integer
signs and set operations only.

## Result

Start with the 23 strict K4 brackets and make the other 47 bracket signs
weak, as required to retain nongeneric embeddings. The two propagation
rules below force between 61 and 69 brackets to be nonzero. Complete affine
circuit enumeration then gives:

| Historical orientation representatives | No additional intersection test | One test | Two tests |
|---|---:|---:|---:|
| All 751 archived representatives | 701 | 10 | 40 |
| After the previously proved final-polynomial exclusion | 700 | 10 | 40 |

Every remaining test involves exactly four points: two edges, or a vertex
and a face. No additional five-point edge–face test is needed. This does
not assert realizability of any of these sign conditions.

For the active **B1.1** family, all fourteen chambers need **zero** additional
intersection tests. Their numbers of forced nonzero brackets are, in the
existing ledger order,

    67, 66, 66, 67, 65, 66, 66, 67, 65, 65, 66, 66, 67, 67.

Consequently the exact B1.1 metric problem can be written with 29 real
variables, 21 quadratic metric equations, the intrinsic/shortestness
inequalities, and a disjunction of fourteen conjunctions of 70 cubic
bracket inequalities. The reconstructed high-degree affine coordinates and
the large separate intersection Boolean formula are unnecessary here.

## 1. Necessary propagation of strict brackets

Write `[ijkl]` for an ordered affine determinant of four spatial points.
Fix one archived sign string. Each bracket has that weak sign, and all K4
brackets are nonzero by the earlier geometric lemma. The algorithm adds a
strict bracket only by one of the following two arguments.

### Five-point cofactor rule

For five ordered labels `U=(u0,...,u4)`, the coefficients

    c_i = (-1)^i [U without u_i]

satisfy both `sum c_i=0` and `sum c_i r_i=0`.

Suppose the bracket on a quadruple `q` vanished. Adjoin a label `w` outside
`q`. If at least one of the other four cofactors is already strict, the
cofactor vector is nonzero and its coefficient at `w` is zero. Hence it
gives a nonzero affine relation supported on `q`. The prescribed signs
determine supersets of its actual positive and negative supports; some
weak coefficients may vanish.

Such a relation is impossible if all possible nonzero coefficients have
the same sign, or if the two sign supports are simplices of the torus:
normalizing the positive and negative sums would give an unintended
intersection of disjoint simplices. It is also impossible when one side
is a singleton vertex and every vertex on the other side is its neighbor.
That would put the vertex in the convex hull of its neighbors, contrary
to strict support. These conditions remain contradictions after deleting
zero coefficients. Thus the assumed zero bracket must be nonzero.

### Signed Grassmann–Plücker rule

For common labels `s,t` and four further labels `a,b,c,d`, use

    [stab][stcd] - [stac][stbd] + [stad][stbc] = 0.

In every archived sign pattern, one signed product is on one side and the
other two are on the other side. After taking the prescribed signs into
account this has the form `A+B=C`, with all three products nonnegative.
If either summand has two known nonzero factors, then `C>0`, so both
factors of `C` are nonzero. This rule uses no division, perturbation, or
genericity assumption.

Apply both rules until the strict set stops changing. The checked-in
script checks the GP sign axiom before using each identity.

## 2. Why the remaining circuit list is complete

The following argument supplies sufficiency, rather than merely another
necessary sign filter. A strict K4 supplies affine rank four for the
augmented point vectors `(1,r_i)`.

If two simplices intersect beyond their intended common simplex, cancel
common barycentric mass on shared labels. A conformally minimal remaining
affine dependence has disjoint positive and negative supports `A,B`, each
a simplex. Its support `S=A union B` has at most five points and augmented
rank `|S|-1`. This follows either by eliminating dependencies while
preserving coefficient signs, or by the elementary circuit property of a
rank-four vector configuration.

Extend an independent subset of these augmented vectors to a basis using
other vertex vectors. Exactly `5-|S|` additional labels suffice. This
produces a five-element set `U` of augmented rank four whose unique
cofactor relation has support **exactly** `S`.

The checker enumerates every such five-element `U` and every possible
support `S` of size two through five. It rejects a candidate support if:

1. a known strict cofactor would be required to vanish outside `S`;
2. `S` is contained in a known strict quadruple, hence is independent; or
3. the cofactor sign partition on `S` is not a pair of simplices.

Every actual unwanted intersection must survive these tests. Conversely,
if no candidates survive, the given weak signs and propagated strict
brackets exclude every unwanted simplex intersection. This includes
coincident vertices, collinear triples, coplanar quadruples and adjacent
faces meeting beyond their common simplex. The test does not silently
replace weak signs by generic signs.

If candidates remain, test the distinct simplex pairs in that list. In
this archive all have four-point support. On a coplanar quadruple of
affine rank three, one of the three two-coordinate projections has a
nonzero cofactor vector; its alternating three-point minors give the
exact sign test. Lower-rank unwanted circuits were already excluded by
the preceding enumeration. Thus at most two such direct four-point
circuit exclusions complete every historical chamber.

## 3. Complete metric generator

`compact_hex.py` keeps the intrinsic coordinates of vertices other than
1 (14 real variables). Move the spatial anchor face 125 to its intrinsic
lift and use 15 spatial coordinates for the other five vertices. Both
intrinsic and spatial coordinates use the squared norm

    X^2 + 3Y^2 + Z^2,

so all coefficients are rational. The fixed linear change
`(X,Y,Z) -> (X,sqrt(3)Y,Z)` converts this to ordinary Euclidean space and
preserves affine signs and intersections.

The five radial norm equalities and sixteen remaining inner-product
equalities are equivalent to all 24 prescribed edge lengths. They are
quadratic. Strict shortest-lift inequalities, the 16 negative intrinsic
face areas, and total double area `-1` enforce the same intrinsic marked
torus as in the existing fixed-hexagon systems. The necessary pairwise
diameter and nonedge contraction bounds are retained.

For each selected chamber the generator inserts its propagated strict
and remaining weak bracket conditions, together with exactly the
remaining circuit exclusions from section 2. Every affine determinant
uses the explicit spatial coordinates and has degree at most three.
Reflection is fixed by `[1253]>0`.

Within the selected chamber this is a complete metric-and-embedding
system under the inherited geometric premises. A solution supplies an
embedded intrinsically flat torus; every embedding covered by that
chamber satisfies the generated conditions. The proof of intrinsic
multiplicity one and the earlier marking/orientation enumeration are
inherited from the repository. This note does not re-audit those bridges.

## 4. Reproduction and limits

From the repository root:

    python research/type5_closure/verify_weak_chambers.py
    python research/type5_closure/compact_hex.py --b11 all --output /tmp/type5-b11.smt2
    python research/type5_closure/compact_hex.py --b11 1 --output /tmp/type5-b11-01.smt2
    python research/type5_focus/solve.py 300000 /tmp/type5-b11.smt2

`--orbit N` generates one historical orbit representative, with a
one-based index. It preserves the archive rather than deleting its one
previously excluded representative. That earlier exclusion remains the
separate final-polynomial proof.

The checker verifies the counts against actual repository inputs.
The solver experiments and their exact scope are recorded in
`verification.txt`. A timeout is not a chamber exclusion. In particular,
this reduction does not change the 0/14 B1.1 closure count, the 0/19
elongated branch count, or Type 5's open universality status.
