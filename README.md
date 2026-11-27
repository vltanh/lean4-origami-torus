# Eight-vertex origami tori in Lean 4

An origami torus is a flat torus embedded in $\mathbb R^3$ by a map that is affine and isometric on each triangle. This repository proves which of the seven eight-vertex torus triangulations admit such an embedding. **Types 1 and 2 are impossible. Types 3–7 are realizable, and Types 3 and 6 are universal.**

## Formalized results

The type numbers refer to the labeled face lists. Types 4 and 6 share a degree sequence and have different face complexes. A reduced modulus is $x+iy$ with $0\le x\le 1/2$, $y>0$, and $x^2+y^2\ge1$.

| Type | Lean theorem and scope | Mathematical proof |
| --- | --- | --- |
| 1 | [Nonexistence](OrigamiTorus/Type1/Nonexistence.lean) | [Star collapse and the seven-vertex obstruction](docs/Type1.md) |
| 2 | [Nonexistence](OrigamiTorus/Type2/Nonexistence.lean) | [Spherical links and the checked sign refutation](docs/Type2.md) |
| 3 | [Every rank-two lattice](OrigamiTorus/Type3/Universal.lean) | [Formalization of Doyle, Lander, Schwartz, and Trettel](docs/Type3.md) |
| 4 | [Every reduced modulus with $x<1/2$, with rank nine](OrigamiTorus/Type4/WideLift.lean) | [Diagonal exchange and trapezoidal charts](docs/Type4.md) |
| 5 | [Exact unit square](OrigamiTorus/Type5/Periodic.lean) and [closed nonrectangular box](OrigamiTorus/Type5/ContinuationTorus.lean) | [Radical constructions](docs/Type5.md) |
| 6 | [Every rank-two lattice, with rank nine](OrigamiTorus/Type6/Universal.lean) | [The Type 3 diagonal exchange and fixed-period inflation](docs/Type6.md) |
| 7 | [Every reduced modulus with $x<1/2$, with rank nine](OrigamiTorus/Type7/WideLift.lean), and [every rectangular lattice](OrigamiTorus/Type7/Tiling.lean) | [Rectangles and the full strip](docs/Type7.md) |

Universality remains open for Types 4, 5, and 7. For Types 4 and 7 the remaining coverage lies on the sharp-rhombic ray $x=1/2$, including the hexagonal endpoint. The [verification guide](docs/VERIFICATION.md) records the formal reductions and the scope of each theorem.

## Prior work

Schwartz established the eight-vertex minimum, and Lander deduced Type 1 nonexistence and posed Type 2 nonexistence as a conjecture. Doyle and Schwartz proved near universality for Type 7. Lander then proved the Type 7 square and Type 3 hexagonal cases. Doyle, Lander, Schwartz, and Trettel proved Type 3 universality and reported a second exactly checked family by a degree sequence shared by Types 4 and 6. This repository identifies its Type 6 construction by the full face list. [Literature and attribution](docs/RELATED_WORK.md)

## Build and verify

With [Elan](https://lean-lang.org/install/) installed, the pinned toolchain and manifest select Lean 4 and Mathlib v4.36.0.

```sh
lake exe cache get
lake build
lake env lake comparator --config=palomar/OrigamiTorus/comparator.json
```

The [Challenge](palomar/OrigamiTorus/Challenge.lean) states the comparison targets independently, and the [Solution](palomar/OrigamiTorus/Solution.lean) supplies the proofs. All 13 configured statements passed local Comparator replay with Lean and NanoDa. The library includes the Type 5 box and the Type 4 and 7 rank-nine strip theorems. [Verification scope](docs/VERIFICATION.md) · [Palomar metadata](palomar/OrigamiTorus/formalization.yaml)

## Credits

The-Anh Vu-Le leads and maintains the project. OpenAI Codex (GPT-6) contributed mathematical proof development, Lean formalization, separate proof reviews, and the manuscript draft. [Detailed credits](docs/CREDITS.md)

Exploratory calculations and earlier proof attempts are available on the [research branch](https://github.com/vltanh/lean4-origami-torus/tree/research/origami-torus-checkpoint).
