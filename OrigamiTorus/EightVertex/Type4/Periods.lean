module

public import OrigamiTorus.EightVertex.Type4.Strips
public import OrigamiTorus.EightVertex.Type7.Periods
import Mathlib.Tactic

/-! Reflection formulas for the marking periods of the two trapezoidal families. -/

@[expose] public section

namespace OrigamiTorus.Type4

open Type5 (Plane smul2 cross)
open Type7 (reflectDirection)

/-- The two marking loops for a planar trapezoid after clearing its common denominator. -/
def trapezoidMarkingPeriods {R : Type*} [Field R] (x w c H : R) : Plane R × Plane R :=
  let p := polynomialPoints x w c H 1
  let D := H-1+H*x
  let r := (D,H)
  let n := (-w*H,D)
  ((p 2-p 4)+(p 3-p 2)+reflectDirection w r (p 4-p 3),
   (p 2-p 5)+(p 0-p 2)+reflectDirection w (smul2 x r+n) (p 5-p 0))

/-- Vectors along the two creases of the trapezoidal base. -/
theorem trapezoid_crease_axes (x w c H : ℝ) :
    let a := H*x
    let D := H-1+a
    let S := (a^2-a-(1-c)*H^2*w-D*(2*a-c*D-1))/(1-c)
    let r := (D,H)
    let n := (-w*H,D)
    let p := polynomialPoints x w c H 1
    p 3-p 6 = smul2 S r ∧ p 5-p 6 = smul2 (-H^2) (smul2 x r+n) := by
  dsimp only
  constructor
  · apply Prod.ext <;> norm_num [polynomialPoints,smul2] <;> apply mul_comm
  · apply Prod.ext <;> norm_num [polynomialPoints,smul2] <;> ring

set_option maxHeartbeats 1500000 in
theorem trapezoid_period_vectors (x w c H : ℝ) (hx : 0 ≤ x) (hw : 0 < w) (hH : 1 < H)
    (hc : 1-c ≠ 0) :
    let D := H-1+H*x
    let r := (D,H)
    let n := (-w*H,D)
    trapezoidMarkingPeriods x w c H = (smul2 (2*H^2) n, smul2 (2*H^2) (smul2 x n-smul2 w r)) := by
  let D := H-1+H*x
  have hH₀ : 0 < H := by linarith
  have hD : 0 < D := add_pos_of_pos_of_nonneg (sub_pos.mpr hH) (mul_nonneg hH₀.le hx)
  have hR : D*D+w*H*H ≠ 0 := by positivity
  have hS : (x*D+ - (w*H))*(x*D+ - (w*H))+w*(x*H+D)*(x*H+D) ≠ 0 := by
    have hh : 0 < x*H+D := add_pos_of_nonneg_of_pos (mul_nonneg hx hH₀.le) hD
    exact (add_pos_of_nonneg_of_pos (mul_self_nonneg _) (mul_pos (mul_pos hw hh) hh)).ne'
  dsimp only
  apply Prod.ext <;> apply Prod.ext <;>
    norm_num [trapezoidMarkingPeriods,polynomialPoints,reflectDirection,weightedSquare,weightedDot,smul2] <;>
    field_simp [hc,hR,hS] <;> ring

/-- The marked scaled ratios are x and one, giving the physical modulus x+i sqrt(w). -/
theorem trapezoid_period_ratios (x w c H : ℝ) (hx : 0 ≤ x) (hw : 0 < w) (hH : 1 < H)
    (hc : 1-c ≠ 0) :
    let (u,v) := trapezoidMarkingPeriods x w c H
    0 < weightedSquare w u ∧ weightedDot w u v = x*weightedSquare w u ∧ cross u v = weightedSquare w u := by
  rw [trapezoid_period_vectors x w c H hx hw hH hc]
  let D := H-1+H*x
  have hH₀ : 0 < H := by linarith
  have hD : 0 < D := add_pos_of_pos_of_nonneg (sub_pos.mpr hH) (mul_nonneg hH₀.le hx)
  change 0 < weightedSquare w (smul2 (2*H^2) (-w*H,D)) ∧ _ ∧ _
  refine ⟨?_,?_,?_⟩
  · simp only [weightedSquare,weightedDot,smul2]
    apply add_pos_of_nonneg_of_pos (mul_self_nonneg _)
    positivity
  · simp [weightedSquare,weightedDot,smul2]
    ring
  · simp [cross,weightedSquare,weightedDot,smul2]
    ring

end OrigamiTorus.Type4
