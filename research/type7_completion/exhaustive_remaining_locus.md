# The complete linear base of the ray-1/2 product limit

The bounded axis chart gives six product equations $tq=P(v)$, with all
variables bounded as $t\to0$. Their complete limiting base consists of
**six closed two-dimensional polygons**. Marked dihedral symmetries reduce
this to **two closed geometric families**. Every point has two projected
endpoint triangles of perimeter one, possibly degenerate.

All six product scales remain. Five exact identities linear in those
scales describe the entire algebraic graph closure, including component
intersections. These are necessary conditions, not an exclusion or a
statement that every real point of the locus lifts to an embedding.

The exact checker exhaustive_remaining_locus.py enumerates every factor
choice, checks the nearest-lift polygons, replays both marked dihedral
groups, and verifies the saturation calculation over the rationals. It
exposes the substitutions and scale relations for the metric reducer.

## 1. Six products and five universal identities

Use independent affine coordinates

$$
 f=2v_3-1,\quad a=v_1-v_3,\quad c=v_2-v_3,\quad d=v_3-v_4,\quad
 b=2v_3-2v_5-1,\quad e=2v_3-2v_7-1.
$$

In the order $(05,14,24,25,47,57)$, the six equations are

$$
 t(q_{05},q_{14},q_{24},q_{25},q_{47},q_{57})
 =(fb,-4ad,-4cd,-2c(b-1),(2d+1)e,be).
 \tag{1}
$$

Direct substitution proves these five identities for every $t>0$:

$$
\begin{aligned}
 a q_{24}-c q_{14}&=0,\\
 (1-b)q_{24}+2d q_{25}&=0,\\
 f q_{57}-e q_{05}&=0,\\
 2c(q_{47}-q_{57})+e(q_{24}-q_{25})&=0,\\
 (2d+1)q_{57}-b q_{47}&=0.
\end{aligned}
\tag{2}
$$

The checker performs this direct polynomial substitution independently
of the saturation calculation. Necessity of (2) therefore does not
depend on an elimination claim.

For algebraic completeness, introduce $u$ with $ut-1=0$, compute the
lexicographic Gröbner basis of (1) and this equation, and eliminate $u$.
Its 19-element basis is exactly the 19-element basis obtained from (1)
and (2). Thus these eleven equations generate the $t$-saturated graph
ideal. At $t=0$, the six base products and (2) give the whole algebraic
fiber, with no additional independent polynomial condition on $q$.
The apparently cubic relation

$$
 (b-1)q_{24}q_{57}-bq_{25}q_{47}+q_{25}q_{57}=0
$$

is already $-q_{57}$ times the second relation plus $q_{25}$ times the
fifth relation in (2).

## 2. Exact closed base components

Choose a zero factor from each of the six products at $t=0$. The
64 choices give 25 consistent choices, 18 distinct affine varieties,
and six maximal planes. Every other consistent variety lies in one
of these planes.

The table gives $(v_1,v_2,v_3,v_4,v_5,v_7)$; always
$v_0=0$ and $v_6=v_3-1/2$.

| Component | Coordinates | Exact parameter domain |
|---|---|---|
| $C_0$ | $(1/2,1/2,1/2,A,B,0)$ | $1/2\le A\le1$, $-1/2\le B\le0$ |
| $C_1$ | $(A,1/2,1/2,1/2,B,0)$ | $1/8\le A\le1/2$, $-1/2\le B\le0$ |
| $C_2$ | $(A,B,1/2,1/2,-1/2,0)$ | $1/8\le A\le1/2$, $0\le B\le1/2$ |
| $C_3$ | $(A+1/2,A+1/2,A+1/2,A+1,A,B)$ | $-3/8\le A\le0$, $0\le B-A\le1/2$ |
| $C_4$ | $(B+1/2,B+1/2,B+1/2,A,B,B)$ | $-3/8\le B\le0$, $1/2\le A-B\le1$ |
| $C_5$ | $(A,B+1/2,B+1/2,B+1/2,B,B)$ | $A\ge1/8$, $B\le0$, $A-B\le1/2$ |

These domains are exactly the intersections with all 48 closed vertical
nearest-lift inequalities and $v_1\ge1/8$. The first five are
quadrilaterals. The last is the triangle with vertices
$(1/8,-3/8),(1/8,0),(1/2,0)$.

The checker enumerates every intersection of two boundary lines and
compares the complete exact vertex sets. The original polytopes are
bounded because edges $0i$ bound $v_1,v_2,v_3,v_5,v_7$, and edge 34
bounds $v_4$. Comparing the complete vertex sets verifies both
inclusions, not only selected points.

The possible step supports are respectively

$$
 \{0,3,4,5\},\ \{0,1,4,5\},\ \{0,1,2,5\},\
 \{0,3,6,7\},\ \{0,3,4,7\},\ \{0,1,4,7\}.
$$

All zero boundaries remain. The middle step of a three-step component
may be negative.

## 3. Projected endpoint triangles, including the corners

The spatial baseline is

$$
 z=(0,v_1,v_2,v_3,2v_3-v_4,2v_3-v_5-1,v_3-1/2,v_7).
$$

For each component these two triples have constant levels separated by
$1/2$. The other two vertices lie in the intervening interval.

| Component | Lower triangle | Upper triangle | Other vertices |
|---|---|---|---|
| $C_0$ | 067 | 123 | 4,5 |
| $C_1$ | 067 | 234 | 1,5 |
| $C_2$ | 067 | 345 | 1,2 |
| $C_3$ | 456 | 123 | 0,7 |
| $C_4$ | 567 | 123 | 0,4 |
| $C_5$ | 567 | 234 | 0,1 |

Their intrinsic vertical edge displacements also vanish. The limit
metric is therefore $|P_j-P_i|^2=X_{ij}^2-q_{ij}$ on these triangles.
Most edges have $q=0$ by definition. The possible exceptions are edge
24 in $C_1$, edge 57 in $C_4$, and both in $C_5$. Relations (2) handle
them without an interior-only division:

- In $C_1$, $(A-1/2)q_{24}=0$ and $(1+2B)q_{24}=0$. Thus $q_{24}=0$
  except possibly at $(A,B)=(1/2,-1/2)$. This corner belongs to $C_0$,
  whose endpoint triangles contain no product edges.
- In $C_4$, $2Bq_{57}=0$ and $2(B+1-A)q_{57}=0$. The only possible
  exception is $(A,B)=(1,0)$, again a point of $C_0$.
- In $C_5$, the second and fifth relations are directly
  $q_{24}=q_{57}=0$ throughout the closed triangle.

Choose the alternate $C_0$ triangles at those two corners. Then every
triangle edge has projected length $|X_{ij}|$. Each triple is a
consecutive horizontal cycle of period $(-1,0)$; its three directed
horizontal edges have nonpositive limits and sum to $-1$. Its
projected perimeter is exactly one. Collinearity and zero sides remain
allowed.

The complete remaining metric constraints are the 24 limiting axis
equations together with (2), linear in seven axial corrections, $w$,
and six product scales. The triangle description is a consequence of
that system; it does not replace the other global compatibility
equations.

## 4. Two canonical geometric families

For $p(i)=r+\epsilon i\pmod8$, $\epsilon\in\{1,-1\}$, both markings
have integral vertex gauges satisfying

$$
 \epsilon K_{p(i),p(j)}-K_{ij}=g_j-g_i.
 \tag{3}
$$

The checker verifies (3) on every edge for all 32 marked
transformations. They preserve the oriented face list. When
$\epsilon=-1$, combine the relabeling with intrinsic torus inversion,
which preserves the fixed metric and marking. The cyclic steps become

$$
 b'_i=b_{i+r}\quad(\epsilon=1),\qquad
 b'_i=b_{r-i-1}\quad(\epsilon=-1).
$$

Components $C_0,C_2,C_3,C_5$ have a single step of value $1/2$.
Rotations by $0,5,3,4$, respectively, put it at index 0 and put the
other component in indices $3,4,5$. They reduce to $C_0$:

$$
 b=(1/2,0,0,A-1/2,1+B-A,-B,0,0).
 \tag{4}
$$

Its whole closed parameter rectangle remains. The intermediate levels
are $z_4=1-A$ and $z_5=-B$, without an assumed order.

Components $C_1,C_4$ have two pairs of consecutive steps. Rotate and,
if necessary, reflect so the larger member of one pair is its first
edge. That edge is at least $1/4$. This gives $C_1$ with the stronger
range $1/4\le A\le1/2$:

$$
 b=(A,1/2-A,0,0,1/2+B,-B,0,0).
 \tag{5}
$$

Its intermediate levels are $z_1=A$, $z_5=-B$. The checker verifies
the four piecewise transformations choosing the larger edge. All
endpoints and overlaps are retained.

This covers asymptotic limits after passing to a subsequence and
applying a marked symmetry. It does not replace the seven-mask
partition at a fixed finite height by an unproved two-branch claim.
After either limiting symmetry, the chosen step has limiting value at
least $1/4$, so its finite value is at least $1/8$ eventually. Reapply
the bounded axis chart and pass to a subsequence in those coordinates;
no direct substitution of the old axial corrections into a changed
axis is assumed.

## Reproduction

    python research/type7_completion/exhaustive_remaining_locus.py /tmp/type7-locus.json

The JSON contains every polygon, step vector, spatial level, endpoint
triangle, gauge table, and universal scale identity. It explicitly
records that no finite-height exclusion is claimed.
