# Palomar entries

Each entry has a standalone Mathlib-only Challenge and a Solution that calls the corresponding Lean proofs. Its configuration selects the declarations listed in its metadata.

| Entry | Comparison scope | Lean modules | Configuration | Metadata |
| --- | --- | --- | --- | --- |
| Seven vertices | Nonexistence for every seven-vertex triangulation | [Challenge](SevenVertex/Challenge.lean) · [Solution](SevenVertex/Solution.lean) | [Comparator](SevenVertex/comparator.json) | [Metadata](SevenVertex/formalization.yaml) |
| 1 | Nonexistence by star collapse and the seven-vertex obstruction | [Challenge](EightVertex/Type1/Challenge.lean) · [Solution](EightVertex/Type1/Solution.lean) | [Comparator](EightVertex/Type1/comparator.json) | [Metadata](EightVertex/Type1/formalization.yaml) |
| 2 | Nonexistence and the finite sign obstruction | [Challenge](EightVertex/Type2/Challenge.lean) · [Solution](EightVertex/Type2/Solution.lean) | [Comparator](EightVertex/Type2/comparator.json) | [Metadata](EightVertex/Type2/formalization.yaml) |
| 3 | Universality for every rank-two lattice | [Challenge](EightVertex/Type3/Challenge.lean) · [Solution](EightVertex/Type3/Solution.lean) | [Comparator](EightVertex/Type3/comparator.json) | [Metadata](EightVertex/Type3/formalization.yaml) |
| 4 | Piecewise-isometric realization throughout the reduced strip with $x<1/2$ | [Challenge](EightVertex/Type4/Challenge.lean) · [Solution](EightVertex/Type4/Solution.lean) | [Comparator](EightVertex/Type4/comparator.json) | [Metadata](EightVertex/Type4/formalization.yaml) |
| 5 | Dyadic-grid square and closed near-square box | [Challenge](EightVertex/Type5/Challenge.lean) · [Solution](EightVertex/Type5/Solution.lean) | [Comparator](EightVertex/Type5/comparator.json) | [Metadata](EightVertex/Type5/formalization.yaml) |
| 6 | Universality with rank nine at the spatial embedding | [Challenge](EightVertex/Type6/Challenge.lean) · [Solution](EightVertex/Type6/Solution.lean) | [Comparator](EightVertex/Type6/comparator.json) | [Metadata](EightVertex/Type6/formalization.yaml) |
| 7 | Full reduced strip with $x<1/2$ and arbitrary-scale rectangular lattices | [Challenge](EightVertex/Type7/Challenge.lean) · [Solution](EightVertex/Type7/Solution.lean) | [Comparator](EightVertex/Type7/comparator.json) | [Metadata](EightVertex/Type7/formalization.yaml) |

The repository root is the Lake project for every entry. Palomar takes one Comparator path and one metadata path per submission, so the entries can use the same pinned public commit. Each entry declares the repository's Apache-2.0 license. [License text](../../LICENSE) · [Palomar submission standard](https://github.com/PalomarRegistry/PalomarPolicy/blob/main/CONTRIBUTING.md#2-prepare-a-submission)

To run the Type 2 comparison locally, use the repository root.

    lake env lake comparator --config=palomar/OrigamiTorus/EightVertex/Type2/comparator.json

## Hosted preflight

Each entry has a manual GitHub Actions workflow pinned to Palomar's verifier. In Actions, select **Palomar preflight (Seven vertices)** or the workflow for the eight-vertex type you want to verify. The workflow checks the selected ref's commit and publishes its mechanical report as an artifact. [Workflow directory](../../.github/workflows) · [Palomar preflight documentation](https://github.com/PalomarRegistry/PalomarSubmission/blob/046554302064b2c83c2b924bea6db87fc5900c68/README.md#L62-L129)

The [verification guide](../../docs/VERIFICATION.md) describes the supporting results in the Lean library.
