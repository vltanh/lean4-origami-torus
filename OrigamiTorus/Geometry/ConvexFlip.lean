module

public import OrigamiTorus.Defs
import OrigamiTorus.Type6.Signs
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.TriangleInequality
import Mathlib.Tactic

/-! Strict diagonal crossing and the splitting of Euclidean corner angles. -/

@[expose] public section

open scoped NNReal
open InnerProductGeometry

namespace OrigamiTorus

/-- Strict opposite sides for both diagonals give an intersection in the relative interior
of both of them. -/
theorem diagonal_intersection (p : Vertex → ℝ × ℝ) (a b c d : Vertex)
    (hc : 0 < area p a b c) (hd : area p a b d < 0)
    (ha : area p c d a < 0) (hb : 0 < area p c d b) :
    ∃ s t : ℝ, 0 < s ∧ s < 1 ∧ 0 < t ∧ t < 1 ∧
      (1-s) • p a+s • p b = (1-t) • p c+t • p d := by
  let Δ := area p a b c-area p a b d
  have hΔ : 0 < Δ := sub_pos.mpr (hd.trans hc)
  have he : area p c d b-area p c d a = Δ := by unfold Δ area; ring
  refine ⟨-area p c d a/Δ,area p a b c/Δ,div_pos (neg_pos.mpr ha) hΔ,
    (div_lt_one hΔ).mpr ?_,div_pos hc hΔ,(div_lt_one hΔ).mpr ?_,?_⟩
  · linarith only [hb,he]
  · dsimp only [Δ]
    linarith only [hd]
  apply Prod.ext
  · change (1-(-area p c d a/Δ))*(p a).1+(-area p c d a/Δ)*(p b).1 =
      (1-area p a b c/Δ)*(p c).1+(area p a b c/Δ)*(p d).1
    field_simp [hΔ.ne']
    unfold Δ area
    ring
  · change (1-(-area p c d a/Δ))*(p a).2+(-area p c d a/Δ)*(p b).2 =
      (1-area p a b c/Δ)*(p c).2+(area p a b c/Δ)*(p d).2
    field_simp [hΔ.ne']
    unfold Δ area
    ring

/-- At a corner, its diagonal splits the interior angle if it passes through a point
inside the opposite diagonal. This applies in any Euclidean ambient space. -/
theorem angle_split_at_diagonal {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (a b c d : E) (s t : ℝ) (hs : 0 < s) (ht : 0 ≤ t) (ht' : t ≤ 1)
    (hab : b ≠ a) (h : (1-s) • a+s • b = (1-t) • c+t • d) :
    angle (c-a) (d-a) = angle (c-a) (b-a)+angle (b-a) (d-a) := by
  apply (angle_eq_angle_add_angle_iff (sub_ne_zero.mpr hab)).mpr
  right
  apply Submodule.mem_span_pair.mpr
  refine ⟨⟨(1-t)/s,div_nonneg (sub_nonneg.mpr ht') hs.le⟩,
    ⟨t/s,div_nonneg ht hs.le⟩,?_⟩
  change ((1-t)/s) • (c-a)+(t/s) • (d-a) = b-a
  apply smul_right_injective E hs.ne'
  simp only [smul_add,smul_smul,mul_div_cancel₀,mul_comm s]
  have he : (1-t) • (c-a)+t • (d-a) = s • (b-a) := by
    linear_combination (norm := module) -h
  simpa only [div_mul_cancel₀ _ hs.ne'] using he

/-- The original and replacement Type 6 diagonals cross strictly in both charts. -/
theorem type6_diagonal_intersection (second : Bool) (x w : ℝ) (hd : chartDomain second x w) :
    let p := stripPoint second x w
    ∃ s t : ℝ, 0 < s ∧ s < 1 ∧ 0 < t ∧ t < 1 ∧
      (1-s) • p 1+s • p 2 = (1-t) • p 0+t • p 5 := by
  obtain ⟨h1,h2,h3,h4⟩ := type6_flipSigns second x w hd
  exact diagonal_intersection _ 1 2 0 5 h1 h2 h3 h4

end OrigamiTorus
