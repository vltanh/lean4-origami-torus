module

public import OrigamiTorus.Type5.Reconstruction
import Mathlib.Tactic

/-! Rational development of a triangle across an edge in scaled planar coordinates. -/

@[expose] public section

namespace OrigamiTorus

open Type5 (Plane cross smul2)

/-- The coordinates `(X,Y)` stand for physical coordinates `(X,y*Y)` with `w=y²`. -/
def weightedDot {R : Type*} [Ring R] (w : R) (u v : Plane R) : R :=
  u.1*v.1 + w*u.2*v.2

def weightedSquare {R : Type*} [Ring R] (w : R) (u : Plane R) : R :=
  weightedDot w u u

def scaledQuarterTurn {R : Type*} [Ring R] (w : R) (u : Plane R) : Plane R :=
  (-w*u.2,u.1)

/-- Develop a triangle with successive edges `u,v` from its first corner.
The developed first edge is `U`, and `σ` chooses its orientation relative to the source. -/
def developOffset {R : Type*} [Field R] (w σ : R) (u v U : Plane R) : Plane R :=
  smul2 (weightedDot w u v / weightedSquare w u) U +
    smul2 (σ * cross u v / weightedSquare w u) (scaledQuarterTurn w U)

theorem weighted_lagrange (w : ℝ) (u v : Plane ℝ) :
    weightedSquare w u * weightedSquare w v =
      (weightedDot w u v)^2 + w*(cross u v)^2 := by
  unfold weightedSquare weightedDot cross
  ring

private theorem scaledExpansion (w a b : ℝ) (U : Plane ℝ) :
    weightedSquare w (smul2 a U + smul2 b (scaledQuarterTurn w U)) =
      weightedSquare w U * (a^2 + w*b^2) := by
  simp [weightedSquare, weightedDot, smul2, scaledQuarterTurn]
  ring

private theorem scaledDifference (w a b : ℝ) (U : Plane ℝ) :
    smul2 a U + smul2 b (scaledQuarterTurn w U) - U =
      smul2 (a-1) U + smul2 b (scaledQuarterTurn w U) := by
  apply Prod.ext <;> simp [smul2,scaledQuarterTurn] <;> ring

/-- Development preserves the two remaining side lengths and gives the prescribed signed area. -/
theorem developOffset_spec (w σ : ℝ) (u v U : Plane ℝ)
    (hside : weightedSquare w U = weightedSquare w u)
    (hbase : weightedSquare w u ≠ 0) (hsign : σ^2 = 1) :
    let V := developOffset w σ u v U
    weightedSquare w V = weightedSquare w v ∧
      weightedSquare w (V-U) = weightedSquare w (v-u) ∧
      cross U V = σ*cross u v := by
  let D := weightedSquare w u
  let a := weightedDot w u v / D
  let b := σ*cross u v/D
  have h1 : weightedSquare w (smul2 a U + smul2 b (scaledQuarterTurn w U)) =
      weightedSquare w v := by
    rw [scaledExpansion, hside]
    change D*(a^2+w*b^2) = weightedSquare w v
    dsimp only [a,b]
    field_simp [show D ≠ 0 from hbase]
    have hl := weighted_lagrange w u v
    change D*weightedSquare w v = _ at hl
    linear_combination -hl + w*(cross u v)^2*hsign
  refine ⟨h1,?_,?_⟩
  · change weightedSquare w (smul2 a U + smul2 b (scaledQuarterTurn w U) - U) = _
    rw [scaledDifference, scaledExpansion]
    have ha : weightedSquare w U * a = weightedDot w u v := by
      rw [hside]
      change D*(weightedDot w u v / D) = _
      field_simp [show D ≠ 0 from hbase]
    rw [scaledExpansion] at h1
    have hdiff : weightedSquare w (v-u) =
        weightedSquare w v + weightedSquare w u - 2*weightedDot w u v := by
      simp [weightedSquare,weightedDot]
      ring
    rw [hdiff, ← hside]
    linear_combination h1 - 2*ha
  · change cross U (smul2 a U + smul2 b (scaledQuarterTurn w U)) = _
    have h : cross U (smul2 a U + smul2 b (scaledQuarterTurn w U)) = b*weightedSquare w U := by
      simp [cross, weightedSquare, weightedDot,smul2,scaledQuarterTurn]
      ring
    rw [h,hside]
    change σ*cross u v/D*D = _
    exact div_mul_cancel₀ _ hbase

end OrigamiTorus
