# Exact local sign gates for the active Type 4 proof

This lemma applies to either five-vertex clique
`{1,2,4,5,6}` or `{1,3,4,5,6}`. It uses the established strict-support
and strict-K4 premises, together with nonintersection of the actual
Type 4 faces. It does not exclude a metric case.

Put `r4=0`, use `(r5,r1,r6)` as a basis, and write, for `i=2` or `3`,

\[
r_i=\lambda_5 r_5+\lambda_1 r_1+\lambda_6 r_6,
\qquad \lambda_4=1-\lambda_5-\lambda_1-\lambda_6.
\]

Every four vertices of this clique form a K4. Thus its five affine
determinants are nonzero, so **none of the four coefficients is zero**.
In particular no generic-position assumption or omitted zero stratum is
needed here. The determinant ratio is
`lambda6 = [451i]/[4516]`.

The unique affine dependence has coefficient `+1` at vertex `i` and
coefficient `-lambda_v` at each anchor. Its two sign parts form the Radon
partition. Affine balance rules out an empty part; strict support rules
out a singleton part, since all other clique vertices are neighbors.
The partition therefore has sizes two and three. If the three-vertex
part is an actual face, the complementary edge pierces it, violating
embeddedness. Consequently the three-vertex part must be a nonface
triangle of this clique.

This leaves exactly the following negative-coefficient subsets, among
the anchors `{1,4,5,6}`:

| Vertex | Allowed negative subsets | Corresponding nonface triangles |
|---|---|---|
| 2 | `{1}`, `{6}`, `{1,4}`, `{1,6}`, `{4,5}`, `{5,6}` | `456`, `145`, `124`, `126`, `245`, `256` |
| 3 | `{1}`, `{6}`, `{1,5}`, `{1,6}`, `{4,5}`, `{4,6}` | `456`, `145`, `135`, `136`, `345`, `346` |

For both vertices, a sole negative coefficient at `4` or `5` is
forbidden by the actual face `165` or `146`, respectively. For vertex 2,
the negative pairs `{1,5}` and `{4,6}` are forbidden by faces `152` and
`264`. For vertex 3, the negative pairs `{1,4}` and `{5,6}` are forbidden
by faces `134` and `356`.

Two useful consequences are therefore

\[
\boxed{\lambda_6^{(2)}<0\;\Longrightarrow\;\lambda_4^{(2)}>0},
\qquad
\boxed{\lambda_6^{(3)}<0\;\Longrightarrow\;\lambda_5^{(3)}>0}.
\]

These are necessary conditions for the entire core, including a cap
whose area or edge lengths become arbitrarily small. The next metric
gate would be to contradict these inequalities, or exclude all six
listed patterns for one vertex. The sign enumeration alone does neither.

For example, coefficients of vertex 2 with `lambda4,lambda6<0` and
`lambda1,lambda5>0` certify the crossing `15` with `264`. This rejection
does not require constructing vertex 3, 0, or 7. Separately, when all
three basis coefficients are positive and their sum exceeds one, edge
`i4` pierces face `165`; all three basis coefficients being negative
instead makes vertex 4 lie in the convex hull of the other four clique
vertices, contradicting strict support.

Replay all sixteen masks for each vertex with standard-library integer
and set operations:

    python3 research/type4_completion/core_signs.py
