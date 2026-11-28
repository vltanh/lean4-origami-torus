module

public import OrigamiTorus.EightVertex.Type5.Geometry
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic

/-! Gram equations for placing both roots and all three leaves above face 125. -/

@[expose] public section

namespace OrigamiTorus.Type5.HexagonalMetric

/-- The mixed three-by-three minor obtained by bordering the anchor Gram matrix. -/
def residual (a b c : ℝ) (p q : Plane ℝ) (g : ℝ) : ℝ :=
  (a*c-b^2)*g - p.1*(c*q.1-b*q.2) - p.2*(a*q.2-b*q.1)

/-- In a spatial placement this minor is the product of the two heights
times the determinant of the horizontal anchor Gram matrix. -/
theorem residual_of_placement (u v x y : Plane ℝ) (h k : ℝ) :
    residual (dot u u) (dot u v) (dot v v) (dot u x, dot v x) (dot u y, dot v y)
      (dot x y + h*k) = (dot u u * dot v v - (dot u v)^2)*h*k := by
  simp only [residual, dot]
  ring

/-- The vanishing of a full five-point clique Gram determinant gives precisely
the quadratic relation between the two diagonal minors and the mixed minor. -/
theorem determinant_identity (a b c d e f : ℝ) (p q : Plane ℝ) :
    (a*c-b^2) * Matrix.det !![a,b,p.1,q.1; b,c,p.2,q.2; p.1,p.2,d,e; q.1,q.2,e,f] =
      residual a b c p p d * residual a b c q q f - (residual a b c p q e)^2 := by
  rw [Matrix.det_succ_row_zero]
  norm_num [Fin.sum_univ_succ, Matrix.det_fin_three, Matrix.submatrix_apply,
    Fin.succAbove, residual]
  ring

/-- All six root–leaf products can be realized simultaneously by positive
heights exactly when each positive mixed minor satisfies its squared equation. -/
theorem positive_heights_iff (D : Fin 2 → ℝ) (F : Fin 3 → ℝ) (M : Fin 2 → Fin 3 → ℝ)
    (hD : ∀ i, 0 < D i) (hF : ∀ j, 0 < F j) :
    (∃ h : Fin 2 → ℝ, ∃ k : Fin 3 → ℝ,
      (∀ i, 0 < h i ∧ h i ^ 2 = D i) ∧ (∀ j, 0 < k j ∧ k j ^ 2 = F j) ∧
        ∀ i j, h i * k j = M i j) ↔
    (∀ i j, 0 < M i j ∧ M i j ^ 2 = D i * F j) := by
  constructor
  · rintro ⟨h, k, hd, hf, hm⟩ i j
    rw [← hm, mul_pow, (hd i).2, (hf j).2]
    exact ⟨mul_pos (hd i).1 (hf j).1, rfl⟩
  · intro hm
    refine ⟨fun i => √(D i), fun j => √(F j),
      fun i => ⟨Real.sqrt_pos.2 (hD i), Real.sq_sqrt (hD i).le⟩,
      fun j => ⟨Real.sqrt_pos.2 (hF j), Real.sq_sqrt (hF j).le⟩, ?_⟩
    intro i j
    rw [← Real.sqrt_mul (hD i).le, ← (hm i j).2, Real.sqrt_sq (hm i j).1.le]

/-- Given the two anchors, their five pairs of prescribed inner products,
and squared norms and root–leaf inner products, the six clique determinants
and the strict minor signs suffice for a single spatial placement. -/
theorem realize_cliques (u v : Plane ℝ) (hc : cross u v ≠ 0)
    (p : Vertex → Plane ℝ) (d : Vertex → ℝ) (g : Vertex → Vertex → ℝ) :
    let a := dot u u
    let b := dot u v
    let c := dot v v
    let H := residual a b c
    (∀ i ∈ roots ++ leaves, 0 < H (p i) (p i) (d i)) →
    (∀ i ∈ roots, ∀ j ∈ leaves, 0 < H (p i) (p j) (g i j) ∧
      Matrix.det !![a,b,(p i).1,(p j).1; b,c,(p i).2,(p j).2;
        (p i).1,(p i).2,d i,g i j; (p j).1,(p j).2,g i j,d j] = 0) →
    ∃ r : Vertex → Space ℝ,
      (∀ i ∈ roots ++ leaves, 0 < (r i).2.2 ∧ squared3 (r i) = d i ∧
        dot u (horizontal (r i)) = (p i).1 ∧ dot v (horizontal (r i)) = (p i).2) ∧
      ∀ i ∈ roots, ∀ j ∈ leaves, dot3 (r i) (r j) = g i j := by
  intro a b c H hd he
  let Δ := a*c-b^2
  have hΔ : 0 < Δ := by
    have h : Δ = (cross u v)^2 := by dsimp [Δ,a,b,c,cross,dot]; ring
    rw [h]
    exact sq_pos_of_ne_zero hc
  let x := fun i => linearSolve u v (p i).1 (p i).2
  have hx (i : Vertex) : dot u (x i) = (p i).1 ∧ dot v (x i) = (p i).2 :=
    linearSolve_spec hc _ _
  have expand (i j : Vertex) (f : ℝ) :
      H (p i) (p j) f = Δ*(f-dot (x i) (x j)) := by
    have hz := residual_of_placement u v (x i) (x j) 0 0
    rw [(hx i).1, (hx i).2, (hx j).1, (hx j).2] at hz
    simp only [Prod.eta, mul_zero, add_zero] at hz
    dsimp [H,Δ,a,b,c,residual] at hz ⊢
    linear_combination hz
  let q := fun i => d i - dot (x i) (x i)
  have hq (i : Vertex) (hi : i ∈ roots ++ leaves) : 0 < q i := by
    have h := hd i hi
    rw [expand] at h
    exact (mul_pos_iff_of_pos_left hΔ).mp h
  refine ⟨fun i => atHeight (x i) (√(q i)), ?_, ?_⟩
  · intro i hi
    refine ⟨Real.sqrt_pos.2 (hq i hi), ?_, hx i⟩
    change dot (x i) (x i) + (√(q i))^2 = d i
    rw [Real.sq_sqrt (hq i hi).le]
    dsimp [q]
    ring
  · intro i hi j hj
    have qi := hq i (List.mem_append_left _ hi)
    have qj := hq j (List.mem_append_right _ hj)
    obtain ⟨hpos, hdet⟩ := he i hi j hj
    rw [expand] at hpos
    have hp := (mul_pos_iff_of_pos_left hΔ).mp hpos
    have heq := determinant_identity a b c (d i) (g i j) (d j) (p i) (p j)
    rw [hdet, mul_zero] at heq
    change 0 = H (p i) (p i) (d i) * H (p j) (p j) (d j) -
      (H (p i) (p j) (g i j))^2 at heq
    rw [expand, expand, expand] at heq
    have hm : (g i j-dot (x i) (x j))^2 = q i*q j := by
      apply mul_left_cancel₀ (sq_pos_of_pos hΔ).ne'
      dsimp [q]
      linear_combination heq
    change dot (x i) (x j) + √(q i)*√(q j) = g i j
    rw [← Real.sqrt_mul qi.le, ← hm, Real.sqrt_sq hp.le]
    ring

end OrigamiTorus.Type5.HexagonalMetric
