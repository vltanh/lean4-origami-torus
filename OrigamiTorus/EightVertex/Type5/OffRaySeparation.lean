module

public import OrigamiTorus.EightVertex.Type5.BracketEmbedding
import Mathlib.Tactic

/-! Seven planes separating the Type 5 faces in the off-ray construction. -/

@[expose] public section

namespace OrigamiTorus.Type5.OffRay

/-- The seventeen strict signs of the off-ray embedding family. -/
structure Signs (r : Vertex → Point3) : Prop where
  s1234 : bracket r 1 2 3 4 < 0
  s1235 : 0 < bracket r 1 2 3 5
  s1245 : bracket r 1 2 4 5 < 0
  s1345 : bracket r 1 3 4 5 < 0
  s2345 : 0 < bracket r 2 3 4 5
  s0125 : 0 < bracket r 0 1 2 5
  s0135 : bracket r 0 1 3 5 < 0
  s0234 : bracket r 0 2 3 4 < 0
  s0245 : 0 < bracket r 0 2 4 5
  s1236 : bracket r 1 2 3 6 < 0
  s1247 : 0 < bracket r 1 2 4 7
  s1357 : bracket r 1 3 5 7 < 0
  s2357 : bracket r 2 3 5 7 < 0
  s2456 : bracket r 2 4 5 6 < 0
  s0246 : 0 < bracket r 0 2 4 6
  s0456 : 0 < bracket r 0 4 5 6
  s2367 : bracket r 2 3 6 7 < 0

private def separators : List PlaneSeparator :=
  [⟨0, 5, 6, {4}, {1, 2, 3}⟩,
   ⟨1, 2, 4, {3, 7}, {0, 5, 6}⟩,
   ⟨1, 2, 5, {4, 6}, {0, 3}⟩,
   ⟨1, 3, 5, {0, 2, 4, 6}, {7}⟩,
   ⟨2, 3, 6, {0, 1, 5}, {4, 7}⟩,
   ⟨2, 4, 6, {1, 3, 5}, {0}⟩,
   ⟨3, 5, 6, {0, 2}, {1, 4, 7}⟩]

/-- Each row follows by the three-term determinant identity. The two summands of
known sign determine the third product, whose other factor has known sign. -/
private theorem separators_valid (r : Vertex → Point3) (h : Signs r) :
    ∀ s ∈ separators, s.Valid r := by
  have s2346 : 0 < bracket r 2 3 4 6 := by
    have eqn := bracket.plucker r 2 4 0 3 5 6
    simp (disch := decide) only [bracket.swapFirst, bracket.swapMiddle, bracket.swapLast, neg_mul, mul_neg, neg_neg] at eqn
    by_contra! opposite
    nlinarith only [eqn, mul_pos_of_neg_of_neg h.s0234 h.s2456,
      mul_nonpos_of_nonpos_of_nonneg opposite (le_of_lt h.s0245),
      mul_pos h.s0246 h.s2345]
  have s0235 : bracket r 0 2 3 5 < 0 := by
    have eqn := bracket.plucker r 2 5 0 1 3 4
    simp (disch := decide) only [bracket.swapFirst, bracket.swapMiddle, bracket.swapLast, neg_mul, mul_neg, neg_neg] at eqn
    by_contra! opposite
    nlinarith only [eqn, mul_pos h.s0125 h.s2345,
      mul_nonpos_of_nonneg_of_nonpos opposite (le_of_lt h.s1245),
      mul_pos h.s0245 h.s1235]
  have s1246 : bracket r 1 2 4 6 < 0 := by
    have eqn := bracket.plucker r 2 4 1 3 5 6
    simp (disch := decide) only [bracket.swapFirst, bracket.swapMiddle, bracket.swapLast, neg_mul, mul_neg, neg_neg] at eqn
    by_contra! opposite
    nlinarith only [eqn, mul_pos_of_neg_of_neg h.s1234 h.s2456,
      mul_neg_of_neg_of_pos h.s1245 s2346,
      mul_nonneg opposite (le_of_lt h.s2345)]
  have s0345 : 0 < bracket r 0 3 4 5 := by
    have eqn := bracket.plucker r 3 5 0 1 2 4
    simp (disch := decide) only [bracket.swapFirst, bracket.swapMiddle, bracket.swapLast, neg_mul, mul_neg, neg_neg] at eqn
    by_contra! opposite
    nlinarith only [eqn, mul_neg_of_neg_of_pos h.s0135 h.s2345,
      mul_pos_of_neg_of_neg s0235 h.s1345,
      mul_nonpos_of_nonpos_of_nonneg opposite (le_of_lt h.s1235)]
  have s1256 : 0 < bracket r 1 2 5 6 := by
    have eqn := bracket.plucker r 1 2 3 4 5 6
    by_contra! opposite
    nlinarith only [eqn, mul_nonneg_of_nonpos_of_nonpos opposite (le_of_lt h.s1234),
      mul_neg_of_pos_of_neg h.s1235 s1246,
      mul_pos_of_neg_of_neg h.s1236 h.s1245]
  have s3456 : bracket r 3 4 5 6 < 0 := by
    have eqn := bracket.plucker r 4 5 0 2 3 6
    simp (disch := decide) only [bracket.swapFirst, bracket.swapMiddle, bracket.swapLast, neg_neg] at eqn
    by_contra! opposite
    nlinarith only [eqn, mul_nonneg opposite (le_of_lt h.s0245),
      mul_neg_of_pos_of_neg s0345 h.s2456,
      mul_pos h.s0456 h.s2345]
  have s0124 : 0 < bracket r 0 1 2 4 := by
    have eqn := bracket.plucker r 2 4 0 1 3 6
    simp (disch := decide) only [bracket.swapFirst, bracket.swapMiddle, bracket.swapLast, neg_mul, mul_neg, neg_neg] at eqn
    by_contra! opposite
    nlinarith only [eqn, mul_nonpos_of_nonpos_of_nonneg opposite (le_of_lt s2346),
      mul_pos_of_neg_of_neg h.s0234 s1246,
      mul_neg_of_pos_of_neg h.s0246 h.s1234]
  have s2356 : bracket r 2 3 5 6 < 0 := by
    have eqn := bracket.plucker r 2 6 1 3 4 5
    simp (disch := decide) only [bracket.swapFirst, bracket.swapMiddle, bracket.swapLast, neg_mul, neg_neg] at eqn
    by_contra! opposite
    nlinarith only [eqn, mul_pos_of_neg_of_neg h.s1236 h.s2456,
      mul_nonpos_of_nonneg_of_nonpos opposite (le_of_lt s1246),
      mul_pos s1256 s2346]
  have s0236 : bracket r 0 2 3 6 < 0 := by
    have eqn := bracket.plucker r 2 3 0 4 5 6
    simp (disch := decide) only [bracket.swapFirst, bracket.swapMiddle, neg_neg] at eqn
    by_contra! opposite
    nlinarith only [eqn, mul_pos_of_neg_of_neg h.s0234 s2356,
      mul_neg_of_neg_of_pos s0235 s2346,
      mul_nonneg opposite (le_of_lt h.s2345)]
  have s0256 : bracket r 0 2 5 6 < 0 := by
    have eqn := bracket.plucker r 2 5 0 3 4 6
    simp (disch := decide) only [bracket.swapFirst, bracket.swapMiddle, bracket.swapLast, neg_mul, mul_neg, neg_neg] at eqn
    by_contra! opposite
    nlinarith only [eqn, mul_pos_of_neg_of_neg s0235 h.s2456,
      mul_neg_of_pos_of_neg h.s0245 s2356,
      mul_nonneg opposite (le_of_lt h.s2345)]
  have s0356 : bracket r 0 3 5 6 < 0 := by
    have eqn := bracket.plucker r 3 5 0 2 4 6
    simp (disch := decide) only [bracket.swapFirst, bracket.swapMiddle, bracket.swapLast, neg_mul, mul_neg, neg_neg] at eqn
    by_contra! opposite
    nlinarith only [eqn, mul_pos_of_neg_of_neg s0235 s3456,
      mul_neg_of_pos_of_neg s0345 s2356,
      mul_nonneg opposite (le_of_lt h.s2345)]
  have s1356 : 0 < bracket r 1 3 5 6 := by
    have eqn := bracket.plucker r 3 5 0 1 4 6
    simp (disch := decide) only [bracket.swapFirst, bracket.swapMiddle, bracket.swapLast, neg_mul, mul_neg, neg_neg] at eqn
    by_contra! opposite
    nlinarith only [eqn, mul_pos_of_neg_of_neg h.s0135 s3456,
      mul_nonpos_of_nonpos_of_nonneg opposite (le_of_lt s0345),
      mul_pos_of_neg_of_neg s0356 h.s1345]
  have s3567 : bracket r 3 5 6 7 < 0 := by
    have eqn := bracket.plucker r 3 5 1 2 6 7
    simp (disch := decide) only [bracket.swapFirst, bracket.swapMiddle, bracket.swapLast, neg_neg] at eqn
    by_contra! opposite
    nlinarith only [eqn, mul_nonneg opposite (le_of_lt h.s1235),
      mul_neg_of_pos_of_neg s1356 h.s2357,
      mul_pos_of_neg_of_neg h.s1357 s2356]
  have s0156 : bracket r 0 1 5 6 < 0 := by
    have eqn := bracket.plucker r 1 5 0 2 3 6
    simp (disch := decide) only [bracket.swapFirst, bracket.swapMiddle, bracket.swapLast, neg_mul, mul_neg, neg_neg] at eqn
    by_contra! opposite
    nlinarith only [eqn, mul_pos h.s0125 s1356,
      mul_neg_of_neg_of_pos h.s0135 s1256,
      mul_nonneg opposite (le_of_lt h.s1235)]
  change ∀ p ∈ separators,
    (∀ i ∈ p.above, 0 < bracket r p.a p.b p.c i) ∧
    (∀ i ∈ p.below, bracket r p.a p.b p.c i < 0)
  simp (disch := decide) only [separators, List.forall_mem_cons, Finset.forall_mem_insert,
    Finset.mem_singleton, forall_eq, bracket.swapFirst, bracket.swapMiddle, bracket.swapLast, neg_pos, neg_lt_zero, neg_neg]
  have s1234 := h.s1234
  have s1235 := h.s1235
  have s1245 := h.s1245
  have s1345 := h.s1345
  have s2345 := h.s2345
  have s0125 := h.s0125
  have s0135 := h.s0135
  have s0234 := h.s0234
  have s0245 := h.s0245
  have s1236 := h.s1236
  have s1247 := h.s1247
  have s1357 := h.s1357
  have s2357 := h.s2357
  have s2456 := h.s2456
  have s0246 := h.s0246
  have s0456 := h.s0456
  have s2367 := h.s2367
  repeat' first | assumption | constructor
  simp

/-- The seventeen signs alone suffice for a closed embedding. Unlisted brackets
may vanish. -/
theorem spatial_embedding {r : Vertex → Point3} (h : Signs r) :
    Topology.IsClosedEmbedding (evaluateTriangles faces r) := by
  apply isClosedEmbedding_of_plane_table separators (separators_valid r h)
  · decide +kernel
  · decide +kernel

end OrigamiTorus.Type5.OffRay
