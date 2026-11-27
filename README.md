# Origami tori in Lean 4

[![Lean Action CI](https://github.com/vltanh/lean4-origami-torus/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/vltanh/lean4-origami-torus/actions/workflows/lean_action_ci.yml)

An origami torus is a flat torus embedded in $\mathbb R^3$ by a map that is affine and isometric on each triangle. A triangulation is universal if it realizes every flat torus. Earlier work established universality with larger triangulations. This repository studies existence and universality at the minimum vertex count. [Related work](docs/RELATED_WORK.md)

## Seven vertices

Schwartz proved that seven vertices are impossible and that eight suffice. This repository formalizes the seven-vertex nonexistence theorem in Lean using a checked classification of the face sets and a determinant-sign refutation. [Schwartz, Theorems 1.1–1.2](https://arxiv.org/html/2507.14998v9#S1.SS1) · [Lean theorem](OrigamiTorus/SevenVertex/Nonexistence.lean) · [Proof notes](docs/SevenVertex/README.md)

## Eight vertices

**Types 1 and 2 admit no flat embedding. Each of Types 3–7 admits one, and Types 3 and 6 are universal.** The type numbers refer to the labeled face lists. In the table, a reduced modulus is $x+iy$ with $0\le x\le 1/2$, $y>0$, and $x^2+y^2\ge1$. Rank nine refers to the spatial map giving seven cone angles and the two real coordinates of the marked modulus.

| Type | Prior work | Contribution verified in this repository |
| --- | --- | --- |
| 1 | Lander deduced nonexistence from Schwartz’s lower bound by removing the degree-three star. [Lander, §6](https://arxiv.org/html/2609.10703v1#S6) | Lean verifies the star collapse and the determinant-sign obstruction on the collapsed face list. [Lean](OrigamiTorus/EightVertex/Type1/Nonexistence.lean) · [Proof notes](docs/EightVertex/Type1.md) |
| 2 | Lander conjectured nonexistence after numerical searches found no flat embedding. [Lander, §6](https://arxiv.org/html/2609.10703v1#S6) | **Resolves the conjecture** with a geometric reduction to determinant signs and a checked refutation. [Lean](OrigamiTorus/EightVertex/Type2/Nonexistence.lean) · [Proof notes](docs/EightVertex/Type2.md) |
| 3 | Lander proved the hexagonal case. Doyle, Lander, Schwartz, and Trettel proved universality. [Lander](https://arxiv.org/html/2609.10703v1) · [Doyle et al., Theorem 1.1](https://arxiv.org/html/2611.21909v1#S1.SS1) | Formalizes universality using the published planar families and height vectors, with fixed-period inflation and a proof of the quotient identification. [Lean](OrigamiTorus/EightVertex/Type3/Universal.lean) · [Proof notes](docs/EightVertex/Type3.md) |
| 4 | Lander reported numerical square realizations. [Lander, §6](https://arxiv.org/html/2609.10703v1#S6) | Gives regular embeddings for every reduced modulus with $x<1/2$, including every rectangle, and verifies rank nine. [Lean](OrigamiTorus/EightVertex/Type4/WideLift.lean) · [Proof notes](docs/EightVertex/Type4.md) |
| 5 | Lander reported numerical square realizations. [Lander, §6](https://arxiv.org/html/2609.10703v1#S6) | Gives exact radical coordinates for the unit square and a uniform construction over a closed box of nonrectangular moduli. [Square](OrigamiTorus/EightVertex/Type5/Periodic.lean) · [Box](OrigamiTorus/EightVertex/Type5/ContinuationTorus.lean) · [Proof notes](docs/EightVertex/Type5.md) |
| 6 | Lander reported numerical square realizations. [Lander, §6](https://arxiv.org/html/2609.10703v1#S6) | Identifies Type 6 by its full face list, constructs a realization for every rank-two lattice by a diagonal exchange on Type 3, and verifies rank nine at the resulting spatial embeddings. [Lean](OrigamiTorus/EightVertex/Type6/Universal.lean) · [Proof notes](docs/EightVertex/Type6.md) |
| 7 | Doyle and Schwartz proved near universality. Lander proved existence at the square and in a neighborhood of it. [Doyle and Schwartz](https://arxiv.org/abs/2510.12623v4) · [Lander](https://arxiv.org/html/2609.10703v1) | Extends coverage to the entire rectangular ray at arbitrary scale and verifies rank-nine embeddings throughout $x<1/2$. [Rectangles](OrigamiTorus/EightVertex/Type7/Tiling.lean) · [Strip](OrigamiTorus/EightVertex/Type7/WideLift.lean) · [Proof notes](docs/EightVertex/Type7.md) |

### Open coverage and attribution

The verified coverage for Types 4 and 7 leaves the sharp-rhombic ray $x=1/2$, including the hexagonal endpoint. Type 5 universality remains open. [Verification scope](docs/VERIFICATION.md)

The universality preprint gives the degree sequence $55666677$ for its second family. That sequence occurs on two different face complexes, so the identification of the preprint’s family with Type 4 or Type 6 remains unresolved. [Doyle et al., §6](https://arxiv.org/html/2611.21909v1#S6) · [Literature and attribution](docs/RELATED_WORK.md) · [Eight-vertex manuscript](docs/eight-vertex-origami-tori.pdf)

## Build and verify

With [Elan](https://lean-lang.org/install/) installed, the pinned toolchain and manifest select Lean 4 and Mathlib v4.36.0.

```sh
lake exe cache get
lake build
```

Import `OrigamiTorus.SevenVertex` for the seven-vertex result, `OrigamiTorus.EightVertex` for Types 1–7, or `OrigamiTorus` for the full library.

The seven-vertex result and each eight-vertex type have a standalone Palomar entry and an on-demand preflight workflow. Run Comparator with the configuration for the entry you want to check. [Palomar entries](palomar/OrigamiTorus/README.md) · [Verification scope](docs/VERIFICATION.md)

```sh
lake env lake comparator --config=palomar/OrigamiTorus/SevenVertex/comparator.json
```

## Credits

The-Anh Vu-Le leads and maintains the project. OpenAI Codex (GPT-6) contributed mathematical proof development, Lean formalization, separate proof reviews, and the manuscript draft. [Detailed credits](docs/CREDITS.md)

Exploratory calculations and earlier proof attempts are available on the [research branch](https://github.com/vltanh/lean4-origami-torus/tree/research/origami-torus-checkpoint).

## License

The project uses Apache-2.0. [License text](LICENSE)
