module

public import OrigamiTorus.Type5.Reconstruction
import Mathlib.Tactic

/-! A face with three matched side lengths has the same intrinsic affine metric. -/

@[expose] public section

namespace OrigamiTorus

open Type5 (Plane Space squared2 squared3 smul2 smul3)

theorem squared3_smul (r : ℝ) (p : ℝ × ℝ × ℝ) : squared3 (r • p) = r^2 * squared3 p := by
  have h : r • p = (r*p.1,r*p.2.1,r*p.2.2) := rfl
  simp only [h,squared3,squared2,Type5.horizontal,Type5.dot]
  ring

/-- Match the squared distance between any two affine points on the two triangles.
The coefficients are the differences of the second and third barycentric coordinates. -/
theorem triangle_squared_metric (a b c : Plane ℝ) (A B C : Space ℝ)
    (hab : squared3 (B-A) = squared2 (b-a)) (hac : squared3 (C-A) = squared2 (c-a))
    (hbc : squared3 (C-B) = squared2 (c-b)) (s t : ℝ) :
    squared3 (smul3 s (B-A) + smul3 t (C-A)) =
      squared2 (smul2 s (b-a) + smul2 t (c-a)) := by
  simp only [squared2,squared3,Type5.dot,Type5.horizontal,smul2,smul3,Type5.atHeight,
    Prod.fst_sub,Prod.snd_sub,Prod.fst_add,Prod.snd_add] at hab hac hbc ⊢
  linear_combination (s^2+s*t)*hab+(t^2+s*t)*hac-s*t*hbc

end OrigamiTorus
