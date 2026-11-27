# Palomar entries by triangulation

The seven configurations below share the Mathlib-only [Challenge](Challenge.lean) and the [Solution](Solution.lean). Each selects the exact declarations for one entry and has its own abstract and source attribution.

| Type | Comparison scope | Configuration | Metadata |
| --- | --- | --- | --- |
| 1 | Nonexistence by star collapse and the seven-vertex obstruction | [Comparator](Type1/comparator.json) | [Metadata](Type1/formalization.yaml) |
| 2 | Nonexistence and the finite sign obstruction | [Comparator](Type2/comparator.json) | [Metadata](Type2/formalization.yaml) |
| 3 | Universality for every rank-two lattice | [Comparator](Type3/comparator.json) | [Metadata](Type3/formalization.yaml) |
| 4 | Piecewise-isometric realization throughout the reduced strip with $x<1/2$ | [Comparator](Type4/comparator.json) | [Metadata](Type4/formalization.yaml) |
| 5 | Exact square and closed nonrectangular box | [Comparator](Type5/comparator.json) | [Metadata](Type5/formalization.yaml) |
| 6 | Universality with rank nine at the spatial embedding | [Comparator](Type6/comparator.json) | [Metadata](Type6/formalization.yaml) |
| 7 | Full reduced strip with $x<1/2$ and arbitrary-scale rectangular lattices | [Comparator](Type7/comparator.json) | [Metadata](Type7/formalization.yaml) |

The repository root is the Lake project for every entry. Palomar takes one Comparator path and one metadata path per submission, so the seven pairs can use the same pinned public commit. The repository needs a root license whose SPDX identifier matches each metadata file. [Palomar submission standard](https://github.com/PalomarRegistry/PalomarPolicy/blob/main/CONTRIBUTING.md#2-prepare-a-submission)

To run the Type 2 comparison locally, use the repository root.

    lake env lake comparator --config=palomar/OrigamiTorus/Type2/comparator.json

The [combined configuration](comparator.json) preserves the existing 13-declaration comparison, including the supporting results. The [verification guide](../../docs/VERIFICATION.md) describes the additional library results.
