module

public import OrigamiTorus.EightVertex.Type5.BracketEmbedding
import Mathlib.Tactic

/-! Seven planes separating the Type 5 faces in the open sharp-ray construction. -/

@[expose] public section

namespace OrigamiTorus.Type5.SharpRay

/-- The seventeen strict signs of the open sharp-ray embedding family. -/
structure Signs (r : Vertex → Point3) : Prop where
  s0125 : 0 < bracket r 0 1 2 5
  s0126 : 0 < bracket r 0 1 2 6
  s0134 : bracket r 0 1 3 4 < 0
  s0136 : bracket r 0 1 3 6 < 0
  s0234 : bracket r 0 2 3 4 < 0
  s1234 : 0 < bracket r 1 2 3 4
  s1236 : bracket r 1 2 3 6 < 0
  s1237 : 0 < bracket r 1 2 3 7
  s1245 : 0 < bracket r 1 2 4 5
  s1345 : bracket r 1 3 4 5 < 0
  s1356 : 0 < bracket r 1 3 5 6
  s1357 : bracket r 1 3 5 7 < 0
  s1456 : 0 < bracket r 1 4 5 6
  s2345 : 0 < bracket r 2 3 4 5
  s2347 : bracket r 2 3 4 7 < 0
  s2456 : bracket r 2 4 5 6 < 0
  s2467 : bracket r 2 4 6 7 < 0

private def separators : List PlaneSeparator :=
  [⟨1, 2, 6, {3, 4, 5, 7}, {0}⟩,
   ⟨1, 2, 7, {4}, {0, 3, 6}⟩,
   ⟨1, 3, 4, {0, 2, 6}, {5, 7}⟩,
   ⟨1, 3, 6, {0}, {2, 4, 5}⟩,
   ⟨1, 4, 5, {2, 6}, {3, 7}⟩,
   ⟨2, 3, 4, {0, 5}, {1, 6, 7}⟩,
   ⟨2, 4, 6, {1, 5}, {0, 3, 7}⟩]

/-- The affine Grassmann–Plücker identity and the alternating five-point sum yield
the strict sides required by the seven planes. -/
private theorem separators_valid (r : Vertex → Point3) (h : Signs r) :
    ∀ p ∈ separators, p.Valid r := by
  have s1235 : 0 < bracket r 1 2 3 5 := by
    have eqn := affineBracket_circuitSum (r 1) (r 2) (r 3) (r 4) (r 5)
    change bracket r 2 3 4 5 - bracket r 1 3 4 5 + bracket r 1 2 4 5 -
      bracket r 1 2 3 5 + bracket r 1 2 3 4 = 0 at eqn
    linarith only [eqn, h.s2345, h.s1345, h.s1245, h.s1234]
  have s1346 : 0 < bracket r 1 3 4 6 := by
    have eqn := bracket.plucker r 1 3 2 4 5 6
    simp (disch := decide) only [bracket.swapMiddle, neg_mul] at eqn
    by_contra! opposite
    nlinarith only [eqn, mul_pos h.s1234 h.s1356,
      mul_nonpos_of_nonpos_of_nonneg opposite (le_of_lt s1235),
      mul_pos_of_neg_of_neg h.s1236 h.s1345]
  have s1347 : bracket r 1 3 4 7 < 0 := by
    have eqn := bracket.plucker r 1 3 2 4 5 7
    simp (disch := decide) only [bracket.swapMiddle, neg_mul] at eqn
    by_contra! opposite
    nlinarith only [eqn, mul_neg_of_pos_of_neg h.s1234 h.s1357,
      mul_nonneg opposite (le_of_lt s1235),
      mul_neg_of_pos_of_neg h.s1237 h.s1345]
  have s0123 : 0 < bracket r 0 1 2 3 := by
    have eqn := bracket.plucker r 1 3 0 2 4 6
    simp (disch := decide) only [bracket.swapFirst, bracket.swapMiddle, bracket.swapLast, neg_mul, mul_neg, neg_neg] at eqn
    by_contra! opposite
    nlinarith only [eqn, mul_nonpos_of_nonpos_of_nonneg opposite (le_of_lt s1346),
      mul_pos_of_neg_of_neg h.s0134 h.s1236,
      mul_neg_of_neg_of_pos h.s0136 h.s1234]
  have s1256 : bracket r 1 2 5 6 < 0 := by
    have eqn := bracket.plucker r 1 2 0 3 5 6
    simp (disch := decide) only [bracket.swapFirst, bracket.swapMiddle, neg_neg] at eqn
    by_contra! opposite
    nlinarith only [eqn, mul_nonneg opposite (le_of_lt s0123),
      mul_neg_of_pos_of_neg h.s0125 h.s1236,
      mul_pos h.s0126 s1235]
  have s1246 : bracket r 1 2 4 6 < 0 := by
    have eqn := bracket.plucker r 1 2 3 4 5 6

    by_contra! opposite
    nlinarith only [eqn, mul_neg_of_pos_of_neg h.s1234 s1256,
      mul_nonneg opposite (le_of_lt s1235),
      mul_neg_of_neg_of_pos h.s1236 h.s1245]
  have s2346 : bracket r 2 3 4 6 < 0 := by
    have eqn := bracket.plucker r 2 4 1 3 5 6
    simp (disch := decide) only [bracket.swapFirst, bracket.swapMiddle, bracket.swapLast, neg_mul, mul_neg, neg_neg] at eqn
    by_contra! opposite
    nlinarith only [eqn, mul_neg_of_pos_of_neg h.s1234 h.s2456,
      mul_nonneg opposite (le_of_lt h.s1245),
      mul_neg_of_neg_of_pos s1246 h.s2345]
  have s1247 : bracket r 1 2 4 7 < 0 := by
    have eqn := bracket.plucker r 2 4 1 3 6 7
    simp (disch := decide) only [bracket.swapFirst, bracket.swapMiddle, bracket.swapLast, neg_mul, mul_neg, neg_neg] at eqn
    by_contra! opposite
    nlinarith only [eqn, mul_neg_of_pos_of_neg h.s1234 h.s2467,
      mul_pos_of_neg_of_neg s1246 h.s2347,
      mul_nonpos_of_nonneg_of_nonpos opposite (le_of_lt s2346)]
  have s1457 : bracket r 1 4 5 7 < 0 := by
    have eqn := bracket.plucker r 1 4 2 3 5 7
    simp (disch := decide) only [bracket.swapMiddle, bracket.swapLast, neg_mul, mul_neg, neg_neg] at eqn
    by_contra! opposite
    nlinarith only [eqn, mul_nonneg opposite (le_of_lt h.s1234),
      mul_neg_of_pos_of_neg h.s1245 s1347,
      mul_pos_of_neg_of_neg s1247 h.s1345]
  have s0124 : 0 < bracket r 0 1 2 4 := by
    have eqn := bracket.plucker r 1 2 0 4 5 6
    simp (disch := decide) only [bracket.swapFirst, bracket.swapMiddle, neg_neg] at eqn
    by_contra! opposite
    nlinarith only [eqn, mul_nonneg_of_nonpos_of_nonpos opposite (le_of_lt s1256),
      mul_neg_of_pos_of_neg h.s0125 s1246,
      mul_pos h.s0126 h.s1245]
  have s0246 : 0 < bracket r 0 2 4 6 := by
    have eqn := bracket.plucker r 2 4 0 1 3 6
    simp (disch := decide) only [bracket.swapFirst, bracket.swapMiddle, bracket.swapLast, neg_mul, mul_neg, neg_neg] at eqn
    by_contra! opposite
    nlinarith only [eqn, mul_neg_of_pos_of_neg s0124 s2346,
      mul_pos_of_neg_of_neg h.s0234 s1246,
      mul_nonpos_of_nonpos_of_nonneg opposite (le_of_lt h.s1234)]
  have s0127 : 0 < bracket r 0 1 2 7 := by
    have eqn := bracket.plucker r 1 2 0 3 4 7
    simp (disch := decide) only [bracket.swapFirst, bracket.swapMiddle, neg_neg] at eqn
    by_contra! opposite
    nlinarith only [eqn, mul_neg_of_pos_of_neg s0123 s1247,
      mul_pos s0124 h.s1237,
      mul_nonpos_of_nonpos_of_nonneg opposite (le_of_lt h.s1234)]
  have s1267 : 0 < bracket r 1 2 6 7 := by
    have eqn := bracket.plucker r 1 2 0 3 6 7
    simp (disch := decide) only [bracket.swapFirst, bracket.swapMiddle, neg_neg] at eqn
    by_contra! opposite
    nlinarith only [eqn, mul_nonpos_of_nonpos_of_nonneg opposite (le_of_lt s0123),
      mul_pos h.s0126 h.s1237,
      mul_neg_of_pos_of_neg s0127 h.s1236]
  change ∀ p ∈ separators,
    (∀ i ∈ p.above, 0 < bracket r p.a p.b p.c i) ∧
    (∀ i ∈ p.below, bracket r p.a p.b p.c i < 0)
  simp (disch := decide) only [separators, List.forall_mem_cons, List.not_mem_nil,
    Finset.forall_mem_insert, Finset.mem_singleton, forall_eq,
    bracket.swapFirst, bracket.swapMiddle, bracket.swapLast, neg_pos, neg_lt_zero, neg_neg]
  have s0125 := h.s0125
  have s0126 := h.s0126
  have s0134 := h.s0134
  have s0136 := h.s0136
  have s0234 := h.s0234
  have s1234 := h.s1234
  have s1236 := h.s1236
  have s1237 := h.s1237
  have s1245 := h.s1245
  have s1345 := h.s1345
  have s1356 := h.s1356
  have s1357 := h.s1357
  have s1456 := h.s1456
  have s2345 := h.s2345
  have s2347 := h.s2347
  have s2456 := h.s2456
  have s2467 := h.s2467
  repeat' first | assumption | constructor
  exact fun _ hfalse => hfalse.elim

/-- The seventeen sharp-ray signs suffice for a closed embedding. -/
theorem spatial_embedding {r : Vertex → Point3} (h : Signs r) :
    Topology.IsClosedEmbedding (evaluateTriangles faces r) := by
  apply isClosedEmbedding_of_plane_table separators (separators_valid r h)
  · decide +kernel
  · decide +kernel

end OrigamiTorus.Type5.SharpRay
