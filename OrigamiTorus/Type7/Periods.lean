module

public import OrigamiTorus.Type7.Rectangular
import Mathlib.Tactic

/-! The two marked periods of the rectangular family, computed by reflecting across two crease lines. -/

@[expose] public section

namespace OrigamiTorus.Type7

open Type5 (Plane smul2 cross)

/-- Reflection of a scaled planar edge direction across a line parallel to the axis. -/
def reflectDirection {R : Type*} [Field R] (w : R) (axis u : Plane R) : Plane R :=
  smul2 (2*weightedDot w axis u / weightedSquare w axis) axis-u

/-- Reflecting across an axis is an isometry in the physical scaled metric. -/
theorem reflectDirection_square (w : ℝ) (axis u : Plane ℝ) (h : weightedSquare w axis ≠ 0) :
    weightedSquare w (reflectDirection w axis u) = weightedSquare w u := by
  let k := 2*weightedDot w axis u / weightedSquare w axis
  have hk : k*weightedSquare w axis = 2*weightedDot w axis u := div_mul_cancel₀ _ h
  change weightedSquare w (smul2 k axis-u) = weightedSquare w u
  simp only [weightedSquare,weightedDot,smul2,Prod.fst_sub,Prod.snd_sub] at hk ⊢
  linear_combination k*hk

theorem reflectDirection_scale (w t : ℝ) (axis u : Plane ℝ) (ht : t ≠ 0)
    (ha : weightedSquare w axis ≠ 0) :
    reflectDirection w (smul2 t axis) u = reflectDirection w axis u := by
  have hn : t^2 * weightedSquare w axis ≠ 0 := mul_ne_zero (pow_ne_zero _ ht) ha
  have hsq : weightedSquare w (smul2 t axis) = t^2 * weightedSquare w axis := by
    simp [weightedSquare,weightedDot,smul2]
    ring
  rw [reflectDirection,reflectDirection,hsq]
  apply Prod.ext <;> simp [smul2,weightedDot] <;> field_simp [ht,ha]

/-- The two crease lines used to develop the marking loops are perpendicular. -/
theorem rectangular_crease_axes (w : ℝ) :
    let p := rectangularPoint w
    let q : ℝ := 33/13
    let H : ℝ := 33/20
    p 3-p 6 = smul2 (73/40-H*q*w) (1,q) ∧
      p 5-p 6 = smul2 (-q-H) (-w*q,1) ∧
      weightedDot w (1,q) (-w*q,1) = 0 := by
  dsimp only
  refine ⟨?_,?_,?_⟩
  · apply Prod.ext <;> norm_num [rectangularPoint,smul2] <;> ring
  · apply Prod.ext <;> norm_num [rectangularPoint,smul2] <;> ring
  · norm_num [weightedDot]

/-- Starting with the positively oriented face 325, use faces 524 and 356 with the
same linear map, and reflect across 36 to read edge 34 from face 364. For the
second loop use face 302 with the same linear map, and reflect across 56 to read
edge 05 from face 506. The coordinates keep the common scale of rectangularPoint. -/
def rectangularMarkingPeriods {R : Type*} [Field R] (w : R) : Plane R × Plane R :=
  let p := rectangularPoint w
  let q : R := 33/13
  let r := (1,q)
  let n := (-w*q,1)
  ((p 2-p 4)+(p 3-p 2)+reflectDirection w r (p 4-p 3),
   (p 2-p 5)+(p 0-p 2)+reflectDirection w n (p 5-p 0))

theorem rectangular_period_vectors (w : ℝ) (hw : 1 ≤ w) :
    let q : ℝ := 33/13
    let H : ℝ := 33/20
    let r := (1,q)
    let n := (-w*q,1)
    rectangularMarkingPeriods w = (smul2 (2*H*q) n,smul2 (-(2*H*q)*w) r) := by
  have hw' : 0 < w := by linarith
  have hD : 0 < 1+((33/13 : ℝ)^2)*w := by positivity
  have hD' : 0 < 1+(1089/169 : ℝ)*w := by norm_num at hD ⊢; exact hD
  have hN : 0 < w^2*(1089/169)+w := by positivity
  apply Prod.ext <;> apply Prod.ext <;>
    norm_num [rectangularMarkingPeriods,rectangularPoint,reflectDirection,weightedSquare,weightedDot,smul2] <;>
    field_simp [hw'.ne',hD'.ne',hN.ne'] <;> ring

/-- In scaled coordinates the period cross-product ratio is one and the dot-product
ratio is zero, so the physical modulus of this marking is i times the rectangle height. -/
theorem rectangular_period_ratios (w : ℝ) (hw : 1 ≤ w) :
    let (u,v) := rectangularMarkingPeriods w
    0 < weightedSquare w u ∧ weightedDot w u v = 0 ∧ cross u v = weightedSquare w u := by
  rw [rectangular_period_vectors w hw]
  have hw' : 0 < w := by linarith
  simp [weightedSquare,weightedDot,cross,smul2]
  refine ⟨by positivity, ?_, ?_⟩ <;> ring

end OrigamiTorus.Type7
