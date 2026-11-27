# Type 5: a six-comparison final polynomial closing one full weak-sign chamber

**Actual exclusion.** The archived sign orbit with representative

    +----++-+-++++-+++--+++++++-+--------+-+----++-+--++-++++-+-------++--

is impossible for an embedded intrinsically flat Type 5 torus, regardless of metric, under the inherited strict local support and K4 nondegeneracy lemmas. This is the 512th orbit in the archived list (one-based), and chamber 15 of B1.5 (one-based). The proof covers all weak nonclique signs of this chamber, not just generic point configurations. No full marking or universality type is closed.

## 1. Force determinants to be nonzero without a genericity assumption

Write [ijkl] for the oriented affine determinant, in the indicated order, and use |ijkl| for its magnitude. Require every sorted bracket to have the weak sign of the representative, strict for all 23 cliques. Strict support is relative to graph neighbors.

Start with the 23 strictly nonzero clique brackets. For a four-set Q, suppose [Q]=0. Choose w outside Q so at least one other four-point bracket of C=Q union {w} has already been proved nonzero. The affine columns on C then have rank four. Their alternating-cofactor affine dependence is nonzero, with coefficient of w equal to zero. Every other coefficient has the weak prescribed sign. If the resulting prescribed positive and negative parts of Q are disjoint simplices, their convex hulls meet, contrary to embedding (zero coefficients may be removed). If either part is a singleton and the other part consists of its graph neighbors, strict local support rules out the relation. If all coefficients have the same weak sign, their sum cannot vanish. In any of these cases [Q] must be nonzero. This is the same cofactor propagation rule used in the Type 4 strict-chamber argument, now applied to this Type 5 sign string.

Exact finite propagation adds 33 brackets in the first round and four in the second. The resulting 60 strict brackets include all factors in the six comparisons below except 0347 and 0467; they also include 0125 and 0457. The checker implements the rule and verifies these facts directly from the face list and sign string.

## 2. Six Grassmann-Plucker identities

For any six distinct indices s,t,a,b,c,d, the identity
    [stab][stcd] - [stac][stbd] + [stad][stbc] = 0
holds for affine determinants. Substituting the prescribed weak signs, including sorting permutation parity, yields the following **equalities of nonnegative magnitudes** (not strict inequalities by assumption):

    |0145||0257| + |0125||0457| = |0157||0245|
    |0157||3457| + |0457||1357| = |0357||1457|
    |0245||0467| + |0246||0457| = |0247||0456|
    |0247||0357| + |0237||0457| = |0257||0347|
    |0347||4567| + |0457||3467| = |0467||3457|
    |0456||1457| + |0457||1456| = |0145||4567|

The fourth identity and strict 0247,0357 force 0347 nonzero. Then the fifth and strict 4567 force 0467 nonzero. Thus all twelve distinct factors occurring in the first summands and the right sides are nonzero. Each first summand is at most the right side; in the first identity it is strictly less because 0125 and 0457 are strict.

Multiply the six comparisons. The multiset of bracket factors on their left is exactly the multiset on their right. Both products are positive, so the result is P<P, a contradiction. This proves **infeasibility of the entire weak-sign chamber**, even when other nonclique determinants vanish. No perturbation is needed for this last proof. It transfers under every vertex relabeling preserving the triangulation and under reflection.

## 3. Exact coverage and remaining counts

The checker loads the actual archive, face list, sharp marking and B1 branch ledger, enumerates the six automorphisms and verifies the signed identities and factor cancellation. The impossible orbit contains six distinct labeled strings modulo reflection, of which four have zero short-direction linking in the sharp marking.

| Necessary orientation archive | Before | After this exclusion |
|---|---:|---:|
| Type 5 automorphism orbits | 751 | 750 |
| Labeled full sign models modulo reflection | 4506 | 4500 |
| Short-unlinked full sign models in sharp marking | 3004 | 3000 |
| B1 full chambers at hexagonal target | 236 | 235 |
| B1.5 full chambers | 42 | 41 |
| B1.1 full chambers | 14 | 14 |

These counts concern necessary sign chambers, not claims that remaining ones are geometrically realizable. No B1 clique pattern is fully excluded. None of the nineteen localized continuous elongated branches has been proved infeasible.

The geometric premises are the earlier strict-support and K4 lemmas; completeness of the remaining orientation reduction is inherited. The final polynomial itself is a metric-independent affine identity argument.

## 4. Search and negative results

The certificate was discovered by checking linear inequalities on logarithms of positive bracket magnitudes. A floating linear program over all 751 archive representatives found one infeasible case. Its dual certificate was first checked by integer cancellation of 34 weighted inequalities; integer optimization then found the six comparisons above. The final proof trusts no LP or MILP result. An extended search using longer four- and five-term Plucker identities and alternating affine cofactor-sum identities (whenever one signed term is alone on its side) did not eliminate further representatives. For each of the other 750 representatives, the log-inequality system was checked to have an integer strict solution obtained by rounding a scaled floating LP solution and rechecking every row. This certifies feasibility of this log relaxation only, not realizability of the signs. The local LP runs used a lossless delta transcription of the archive, with sorted-string SHA-256 c11b5b8e4f4b06e18e64d7d497796972b22185e97a2e8d23aa928666824800f4.

Also tested: the complete disjoint-cycle linking-number condition on all 534 disjoint simple-cycle pairs of lengths 3–5 (439 simple cycles total) is compatible with every one of the 751 archived representatives. The exact affine-circuit intrinsic halfplane sign filter, even when all circuits must use the same intrinsic ray order, excludes none of the 4506 labeled models. A short numerical continuation from the square witness did not produce a new certified modulus. None of these negative experiments is used as a proof premise.

## Reproduce the actual exclusion

    cd research/type5_focus
    node verify_final_polynomial.cjs

The exact checker passed on actual repository inputs via the connector. It needs only Node.js and the archived JSON files. The original archive and branch data are preserved for reproduction of the earlier SAT completeness checks rather than deleting the impossible strings from those historical inputs. For downstream exact chamber searches, skip the six proven impossible strings (and the one B1.5 representative explicitly identified above). B1.1 remains 0/14 excluded, and Type 5 universality remains unresolved.
