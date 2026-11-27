# Type 5 coverage audit and strict metric constraints

This checkpoint excludes no full elongated cell. It supplies an independently
recomputed cover and two necessary constraints that remain valid at arbitrarily
small positive scales.

## What is checked

`python research/type5_completion/verify_coverage.py` checks the stored
`coverage.json` against source hashes and an independent enumeration. The
archived faces, unique sharp marking, and all 24 shifts agree with the actual
Lean definitions. Half-turn incidence sets give 36 raw cells, 19 reflection
representatives, and the F1--F4 cover of sizes 5, 9, 9, 3. Every cap has a
primitive horizontal cycle. Both symmetry mates are included before taking
endpoint closures; F4 therefore includes `20022020`.

The checker verifies the rational numerical margins in the quantitative
localization argument. It does **not** formalize that argument or extract
lifted-face data from an arbitrary quotient realization. Existing Lean
theorems already prove shortestness from a compact face cover, winding
generation and unimodularity from coherent quotient data, and the finite
winding-orbit classification; those results are not new assumptions to prove
from scratch.

## Every triple except 067 is noncollinear

Assume an embedded, facewise isometric Type 5 realization of a flat torus.
Its spherical link at each vertex has total angular length `2*pi`.

If two neighboring rays at a vertex are opposite, their endpoints cannot
be adjacent: that edge would contain the central vertex. For each of the
21 remaining missing-pair/common-neighbor configurations, the manifest gives
a cyclic link arc `a,x,y,b` with both edges `a-y` and `x-b` present.

The two link arcs between opposite rays each have angular length at least
`pi`. Flatness makes both lengths exactly `pi`, so the selected arc lies on
a minimizing great semicircle, with the displayed rays in order. Translate
the central vertex to zero. The ordered rays give nonnegative cone
expressions `x = p*a + r*y` and `y = s*x + t*b`. Disjointness of the radial
edge `0-x` from `a-y` forces `p+r<1`: otherwise rescaling the expression by
`1/(p+r)` supplies an intersection. Likewise disjointness of `0-y` from
`x-b` forces `s+t<1`. Thus `r*s<1`. Taking components perpendicular to the
endpoint line gives `x_perp=r*y_perp` and `y_perp=s*x_perp`, hence `r*s=1`,
because these interior rays are distinct from both endpoint rays. This is
a contradiction. The forbidden crossing involves a radial edge and a
diagonal; the two diagonals alone need not cross for arbitrary radial
lengths. The generic existing lemma `impossible_minimal_arc_of_embedding`
formalizes this cone argument, and the checker verifies every Type 5
incidence and order hypothesis it requires.

Thus a common neighbor cannot lie between the endpoints of a missing pair.
The other two collinear orders place an endpoint on an incident edge and
also violate embeddedness. This proves noncollinearity for 21 nonclique
triples. The 34 clique triples are already noncollinear because the middle
vertex would lie on an edge. These account for all 55 triples other than
`067`; no condition is asserted for `067`.

For squared spatial distances `d`, noncollinearity of `v,i,j` is exactly

```
4*d[v,i]*d[v,j] - (d[v,i] + d[v,j] - d[i,j])^2 > 0.
```

This is four times the squared area of the parallelogram on the two vectors
from `v`, hence positive precisely when they are independent. The generator
adds the 21 constraints not already supplied by its clique conditions. It
does not impose a positive numerical margin.

## Discharging the strict K4 premise mathematically

The same checked antipodal obstructions supply the missing finite input to
the Type 2 strict-support proof. The existing generic theorem
`ordered_pair_or_triple_of_flat_link` says a flat link without strict support
has an antipodal pair or a positive dependence on three rays. The first case
has just been excluded. In the second case, equality in the angular triangle
inequalities forces every link ray into the plane of those three rays; this
is `link_is_planar_of_positive_triple`, also generic in the link.

Every Type 5 vertex belongs to a K5, with an explicit witness in the manifest.
Planarity of its star would put that K5 into a plane, contradicting the
embedded straight-edge K5 obstruction. Therefore every Type 5 flat star has
strict hemisphere support.

A planar K4 either has crossing disjoint edges, a collinear triple, or one
vertex in the triangle of its three neighbors. The first two alternatives
violate embeddedness and the third violates strict support. Consequently
all 23 clique tetrahedra are nondegenerate. This is a hand proof with checked
finite incidences, **not a new compiled Type 5 Lean theorem**. The existing
generic lemmas can be instantiated to formalize it.

## At most one lift can saturate contraction

Let `g` be the lifted periodic realization. It is globally distance
nonincreasing: subdivide an intrinsic segment into its finitely many face
pieces. Injectivity on the quotient means its fibers are exactly lattice
cosets.

If `|g(a)-g(b+k)| = |a-b-k|`, equality in the triangle inequality and strict
convexity of Euclidean space make `g` affine along that entire segment. If
two distinct lattice shifts `k,l` saturated the comparison, the points at
the same fraction `t` along the two intrinsic segments would have the same
image. Their difference is `t*(k-l)`, which must then be a lattice vector
for every `t` in `[0,1]`. A sufficiently small positive `t` contradicts
discreteness of the lattice.

Writing `N_k` for the intrinsic squared displacement and `d` for the spatial
squared distance therefore gives

```
N_k - d >= 0,  N_l - d >= 0,  N_k + N_l - 2*d > 0    (k != l).
```

The augmentation adds the last inequality for all 36 pairs of the nine
tested lifts, for each of the four missing edges. This allows one lift to
saturate and excludes only simultaneous saturation. Blanket strict
contraction for a nonedge is not justified: a missing diagonal may pass
straight through coplanar faces. The older cubic `--extra` conditions cover
only the three universal-star lifts for each missing pair.

## Reproduction and scope

Generate an augmented **full** cell without fixing any continuous variable:

```sh
python research/type5_completion/coverage_constraints.py /tmp/type5-strict 00120221
```

Omit the cell argument to generate all 19. The implementation preserves the
18 original variables and every original metric, cap, face, and
simplex-intersection condition, then adds 165 strict inequalities. The
reusable functions also accept other squared-distance units and formulations.
`--necessary` explicitly omits the original general intersection conditions
for comparison with the older necessary relaxation. Neither generation nor
the coverage replay is an infeasibility certificate.

The separate `--check-square` mode checks all 165 new strict inequalities
against the existing exact positive square realization, using that
certificate's 200-bit integer interval arithmetic. The augmented full
`00120221` file was also parsed by the existing solver wrapper; its 100 ms
probe returned `UNKNOWN (timeout)`, which changes no exclusion count.
