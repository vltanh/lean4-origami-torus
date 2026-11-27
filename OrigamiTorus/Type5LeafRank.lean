module

public import OrigamiTorus.TriangleMetric
public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.Matrix.Symmetric
public import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Tactic

/-! The Gram determinant in the Type 5 leaf-rank argument. -/

@[expose] public section

open scoped Matrix

namespace OrigamiTorus.Type5

def pentagonGram {R : Type*} [Zero R] (a b c d e : R) : Matrix (Fin 5) (Fin 5) R :=
  !![0,0,a,b,0;
    0,0,0,c,d;
    a,0,0,0,e;
    b,c,0,0,0;
    0,d,e,0,0]

theorem det_pentagonGram {R : Type*} [CommRing R] (a b c d e : R) :
    (pentagonGram a b c d e).det = 2*a*b*c*d*e := by
  simp only [pentagonGram,Matrix.det_succ_row_zero,Matrix.det_fin_zero,
    Matrix.submatrix_apply,Fin.sum_univ_succ,Fin.sum_univ_zero]
  simp +ground
  ring

/-- Five vectors with a singular symmetric Gram matrix, each orthogonal to
itself and its two cyclic neighbors, have a mutually orthogonal consecutive triple. -/
theorem pentagonGram_orthogonal_triple {G : Matrix (Fin 5) (Fin 5) ℝ}
    (hs : G.IsSymm) (hd : ∀ i, G i i = 0)
    (hc : ∀ i, G i (finRotate 5 i) = 0) (hdet : G.det = 0) :
    ∃ i, G i (finRotate 5 (finRotate 5 i)) = 0 := by
  have hG : G = pentagonGram (G 0 2) (G 0 3) (G 1 3) (G 1 4) (G 2 4) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [pentagonGram] <;>
      first | rfl | exact hd _ | exact hc _ | exact hs.apply _ _ |
        rw [hs.apply]; exact hc _
  by_contra! h
  have hn : 2*G 0 2*G 0 3*G 1 3*G 1 4*G 2 4 ≠ 0 := by
    have h03 : G 0 3 ≠ 0 := (hs.apply 0 3) ▸ h 3
    have h14 : G 1 4 ≠ 0 := (hs.apply 1 4) ▸ h 4
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero
      (h 0)) h03) (h 1)) h14) (h 2)
  exact hn ((det_pentagonGram ..).symm.trans ((congrArg Matrix.det hG).symm.trans hdet))

/-- A Gram matrix through a four-dimensional coordinate space is singular. -/
theorem pentagonGram_orthogonal_triple_of_factorization
    (A : Matrix (Fin 5) (Fin 4) ℝ) (B : Matrix (Fin 4) (Fin 5) ℝ)
    (hs : (A*B).IsSymm) (hd : ∀ i, (A*B) i i = 0)
    (hc : ∀ i, (A*B) i (finRotate 5 i) = 0) :
    ∃ i, (A*B) i (finRotate 5 (finRotate 5 i)) = 0 := by
  apply pentagonGram_orthogonal_triple hs hd hc
  by_contra h
  have h₁ := Matrix.rank_of_det_ne_zero h
  have h₂ := (Matrix.rank_mul_le_left A B).trans A.rank_le_card_width
  simp [h₁] at h₂

private theorem space_eq_zero_of_squared {v : Space ℝ} (h : squared3 v = 0) : v = 0 := by
  have h₁ := sq_nonneg v.1
  have h₂ := sq_nonneg v.2.1
  have h₃ := sq_nonneg v.2.2
  simp only [squared3,squared2,dot,horizontal, ← pow_two] at h
  exact Prod.ext (by nlinarith : v.1 = 0)
    (Prod.ext (by nlinarith : v.2.1 = 0) (by nlinarith : v.2.2 = 0))

private theorem space_coordinate_sum (r : Space ℝ) :
    r = r.1 • ((1,0,0) : Space ℝ) + r.2.1 • ((0,1,0) : Space ℝ) +
      r.2.2 • ((0,0,1) : Space ℝ) := by
  ext <;> simp

/-- If the five paired spatial and intrinsic neighbor vectors lie on the
graph of an affine map, cyclic length congruence forces an orthogonal triple.
The vanishing complementary entry is stated as equality of dot products. -/
theorem leafAffineRank_three (r : Fin 5 → Space ℝ) (s : Fin 5 → Plane ℝ)
    (L : Space ℝ →ₗ[ℝ] Plane ℝ) (b : Plane ℝ)
    (hL : ∀ i, s i = L (r i) + b)
    (hn : ∀ i, squared3 (r i) = squared2 (s i))
    (he : ∀ i, dot3 (r i) (r (finRotate 5 i)) = dot (s i) (s (finRotate 5 i))) :
    ∃ i, dot3 (r i) (r (finRotate 5 (finRotate 5 i))) =
      dot (s i) (s (finRotate 5 (finRotate 5 i))) := by
  let e₁ := L (1,0,0)
  let e₂ := L (0,1,0)
  let e₃ := L (0,0,1)
  let A : Matrix (Fin 5) (Fin 4) ℝ := fun i => ![(r i).1,(r i).2.1,(r i).2.2,1]
  let B : Matrix (Fin 4) (Fin 5) ℝ := fun k j =>
    ![(r j).1-dot e₁ (s j),(r j).2.1-dot e₂ (s j),(r j).2.2-dot e₃ (s j),-dot b (s j)] k
  have hrow (i : Fin 5) : s i = (r i).1 • e₁ + (r i).2.1 • e₂ + (r i).2.2 • e₃ + b := by
    rw [hL i]
    conv_lhs => rw [space_coordinate_sum (r i)]
    simp only [map_smul,map_add,e₁,e₂,e₃]
  have hGram (i j : Fin 5) : (A*B) i j = dot3 (r i) (r j)-dot (s i) (s j) := by
    rw [Matrix.mul_apply,hrow i]
    simp [A,B,Fin.sum_univ_succ,dot3,dot,horizontal]
    ring
  have hs : (A*B).IsSymm := by
    apply Matrix.IsSymm.ext
    intro i j
    rw [hGram,hGram]
    simp only [dot3,dot,horizontal]
    ring
  have hd (i : Fin 5) : (A*B) i i = 0 := by
    rw [hGram]
    simpa [dot3,dot,squared3,squared2,pow_two] using sub_eq_zero.mpr (hn i)
  have hc (i : Fin 5) : (A*B) i (finRotate 5 i) = 0 := by
    rw [hGram,he,sub_self]
  obtain ⟨i,hi⟩ := pentagonGram_orthogonal_triple_of_factorization A B hs hd hc
  exact ⟨i,sub_eq_zero.mp ((hGram _ _).symm.trans hi)⟩

private theorem squaredCombination_eq (r : Fin 3 → Space ℝ) (s : Fin 3 → Plane ℝ)
    (c : Fin 3 → ℝ) (hd : ∀ i, squared3 (r i) = squared2 (s i))
    (h01 : dot3 (r 0) (r 1) = dot (s 0) (s 1))
    (h12 : dot3 (r 1) (r 2) = dot (s 1) (s 2))
    (h02 : dot3 (r 0) (r 2) = dot (s 0) (s 2)) :
    squared3 (∑ i, c i • r i) = squared2 (∑ i, c i • s i) := by
  have h0 := hd 0
  have h1 := hd 1
  have h2 := hd 2
  have hr (a : ℝ) (v : Space ℝ) : a • v = smul3 a v := rfl
  have hs (a : ℝ) (v : Plane ℝ) : a • v = smul2 a v := rfl
  simp only [Fin.sum_univ_three,hr,hs,smul3,smul2,atHeight,squared3,squared2,dot3,dot,horizontal,
    Prod.fst_add,Prod.snd_add] at *
  linear_combination c 0^2*h0 + c 1^2*h1 + c 2^2*h2 +
    (2*c 0*c 1)*h01 + (2*c 1*c 2)*h12 + (2*c 0*c 2)*h02

/-- A nonzero affine offset forces a nontrivial affine dependence among three
consecutive spatial neighbors. The affine dependence uses the same weights
as a linear dependence among their two-dimensional intrinsic vectors. -/
theorem leafAffineRank_three_dependent (r : Fin 5 → Space ℝ) (s : Fin 5 → Plane ℝ)
    (L : Space ℝ →ₗ[ℝ] Plane ℝ) {b : Plane ℝ} (hb : b ≠ 0)
    (hL : ∀ i, s i = L (r i) + b)
    (hn : ∀ i, squared3 (r i) = squared2 (s i))
    (he : ∀ i, dot3 (r i) (r (finRotate 5 i)) = dot (s i) (s (finRotate 5 i))) :
    ∃ (i : Fin 5) (c : Fin 3 → ℝ), (∃ k, c k ≠ 0) ∧
      (∑ k, c k) = 0 ∧
      (∑ k, c k • (![r i,r (finRotate 5 i),r (finRotate 5 (finRotate 5 i))] : Fin 3 → Space ℝ) k) = 0 := by
  obtain ⟨i,hi⟩ := leafAffineRank_three r s L b hL hn he
  let p : Fin 3 → Fin 5 := ![i,finRotate 5 i,finRotate 5 (finRotate 5 i)]
  have hdim : Module.finrank ℝ (Plane ℝ) = 2 := by
    simp [Plane,Module.finrank_prod]
  have hdep : ¬LinearIndependent ℝ (s ∘ p) := by
    intro h
    have hle := h.fintype_card_le_finrank
    simp [hdim] at hle
  obtain ⟨c,hc,hcn⟩ := Fintype.not_linearIndependent_iff.mp hdep
  have heq := squaredCombination_eq (r ∘ p) (s ∘ p) c (fun j => hn (p j))
    (he i) (he (finRotate 5 i)) hi
  rw [hc] at heq
  let X := ∑ k, c k • (r ∘ p) k
  have hX : X = 0 :=
    space_eq_zero_of_squared (by simpa [X,squared2,dot] using heq)
  have hsum : (∑ k, c k) • b = 0 := by
    have h := hc
    simp only [Function.comp_apply,hL,smul_add,Finset.sum_add_distrib,← map_smul,← map_sum,
      ← Finset.sum_smul] at h
    change L X + (∑ k, c k) • b = 0 at h
    simpa [hX] using h
  refine ⟨i,c,hcn,(smul_eq_zero.mp hsum).resolve_right hb,?_⟩
  change (∑ k, c k • (![r i,r (finRotate 5 i),r (finRotate 5 (finRotate 5 i))] : Fin 3 → Space ℝ) k) = 0
  simpa [X,Fin.sum_univ_three,p] using hX

/-- A direction that preserves the norm and the two incident inner products
belongs to the spatial face plane. This is the facewise implication used
when a Type 5 leaf norm polynomial vanishes on its entire affine line. -/
theorem leafDirection_in_facePlane (r₁ r₂ e : Space ℝ) (s₁ s₂ d : Plane ℝ)
    (hi : cross s₁ s₂ ≠ 0)
    (h₁ : squared3 r₁ = squared2 s₁) (h₂ : squared3 r₂ = squared2 s₂)
    (h₁₂ : squared3 (r₂-r₁) = squared2 (s₂-s₁))
    (hn : squared3 e = squared2 d)
    (he₁ : dot3 e r₁ = dot d s₁) (he₂ : dot3 e r₂ = dot d s₂) :
    ∃ a c : ℝ, e = smul3 a r₁ + smul3 c r₂ := by
  let ac := linearSolve (s₁.1,s₂.1) (s₁.2,s₂.2) d.1 d.2
  have hrec : smul2 ac.1 s₁ + smul2 ac.2 s₂ = d := by
    obtain ⟨hx,hy⟩ := linearSolve_spec
      (show cross (s₁.1,s₂.1) (s₁.2,s₂.2) ≠ 0 by simpa [cross,mul_comm] using hi) d.1 d.2
    exact Prod.ext (by simpa [ac,smul2,dot,mul_comm] using hx)
      (by simpa [ac,smul2,dot,mul_comm] using hy)
  let v := smul3 ac.1 r₁ + smul3 ac.2 r₂
  have hv : squared3 v = squared2 d := by
    have h₁' : squared3 (r₁-0) = squared2 (s₁-0) := by simpa only [sub_zero]
    have h₂' : squared3 (r₂-0) = squared2 (s₂-0) := by simpa only [sub_zero]
    simpa only [sub_zero,hrec,v] using
      triangle_squared_metric 0 s₁ s₂ 0 r₁ r₂ h₁' h₂' h₁₂ ac.1 ac.2
  have hdot : dot3 e v = squared2 d := by
    rw [← hrec]
    simp only [v,dot3,dot,squared2,horizontal,smul3,smul2,atHeight,
      Prod.fst_add,Prod.snd_add] at he₁ he₂ ⊢
    have hh₁ := congrArg Prod.fst hrec
    have hh₂ := congrArg Prod.snd hrec
    simp only [smul2,Prod.fst_add,Prod.snd_add] at hh₁ hh₂
    simp_rw [hh₁,hh₂]
    linear_combination ac.1*he₁ + ac.2*he₂ + d.1*hh₁ + d.2*hh₂
  have hz : squared3 (e-v) = 0 := by
    simp only [squared3,squared2,dot3,dot,horizontal,Prod.fst_sub,Prod.snd_sub] at hn hv hdot ⊢
    linear_combination hn + hv - 2*hdot
  exact ⟨ac.1,ac.2,sub_eq_zero.mp (space_eq_zero_of_squared hz)⟩

end OrigamiTorus.Type5
