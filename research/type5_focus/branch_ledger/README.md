# Active branch ledger: Type 5 at the exact hexagonal metric

Target: prove nonuniversality by ruling out this one prescribed modulus. No other triangulation type is being attacked in this checkpoint. All prior geometric and marking reductions remain subject to independent audit.

The five signs refer to heights of vertices (0,3,4,6,7) over the face 125, with height 3 positive. The exact hexagonal isometry and automorphism check in `../verify_crossing_cycle.py` reduces the seven prior height families to two orbits:

| ID | Height signs | Clique sign patterns | Status |
|---|---|---:|---|
| B1 | ++--- | 6 | Active |
| B2 | +++++ | 102 | Deferred |

The exact SAT enumeration in `enumerate_split.py` exhausts the necessary Boolean relaxation for B1 and independently compares the result with the expansion of the previous 751 full-sign orbit archive. Both give 236 primary determinant assignments modulo reflection, distributed as follows. The strings refer to the fixed sorted clique list in `../clique_signs5.json`.

| Subbranch | Clique signs | Full Boolean sign models | Status |
|---|---|---:|---|
| B1.1 | +++-++++-+-+-++++-+-++- | 14 | Active, 0 excluded |
| B1.2 | +-------+-+-+----+-+--+ | 16 | Deferred |
| B1.3 | +--+-+--+-+-+----+-+--+ | 33 | Deferred |
| B1.4 | +-------+-+------+-+--- | 34 | Deferred |
| B1.5 | +--+-+--+-+------+-+--- | 42 | Deferred |
| B1.6 | +++-++++-+-++++++-+-+++ | 97 | Deferred |

For each generic Boolean sign model, use strict signs for the 23 clique determinants and weak signs for all other determinants. This is necessary for actual embedded flat realizations even with coplanar vertices: the earlier strict-support, K4 nondegeneracy and generic perturbation lemmas put any such realization in the closure of a generic necessary sign model with the same clique signs. Normalization by reflection is checked using the anchor orientation (the signed double-area sum is -1). The full generator retains degeneracy-complete simplex intersection tests; the relaxed generator omits them but retains projection cycle exclusions. The full systems are not simply strict generic chambers.

Reproduce from this directory (Python 3, SymPy, shared libz3):

```
python ../verify_crossing_cycle.py
python enumerate_split.py
python generate_chambers.py B1.1 0
python generate_chambers.py B1.1 1
python ../solve.py 3000 systems/B1.1_*_0.smt2
python ../solve.py 3000 systems/B1.1_*_1.smt2
```

All fourteen relaxed queries and all fourteen full queries returned unknown (timeout at 3000 ms per query). Zero chambers are certified infeasible; no embedded witness was obtained. This is a case decomposition, not a nonexistence proof. `branches.json` stores the precise finite case list; generated SMT systems are not archived. The next task is to obtain an exact infeasibility certificate for B1.1 (for instance by using the earlier eight-variable radical reconstruction and interval/positivity reasoning) or a verified embedded hexagonal witness. Do not advance to B1.2 merely because the solver times out. Excluding all B1.1 chambers would close B1.1, not B1 or Type 5. Excluding B1 and B2 would prove nonuniversality. A positive witness would instead require a new target metric or a global universality construction.
