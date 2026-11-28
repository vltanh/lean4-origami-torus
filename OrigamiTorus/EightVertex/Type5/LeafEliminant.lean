module

public import OrigamiTorus.EightVertex.Type5.PositiveCycle
import all OrigamiTorus.EightVertex.Type5.PositiveCycle
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Tactic

/-! The mixed Gram identity for a plane containing a Type 5 leaf. -/

public section

open scoped Matrix

namespace OrigamiTorus.Type5

private theorem adjugate_mixedMetric : mixedMetric.adjugate = mixedMetric := by
  have involution : mixedMetric * mixedMetric = 1 := by
    rw [mixedMetric, Matrix.diagonal_mul_diagonal]
    apply congrArg Matrix.diagonal
    ext i
    fin_cases i <;> norm_num
  calc
    mixedMetric.adjugate = mixedMetric.adjugate * (mixedMetric * mixedMetric) := by rw [involution, mul_one]
    _ = (mixedMetric.adjugate * mixedMetric) * mixedMetric := (mul_assoc ..).symm
    _ = mixedMetric := by rw [Matrix.adjugate_mul, mixedMetric_det, one_smul, one_mul]

/-- For a matrix of five mixed row vectors, contracting the adjugate of their
Gram matrix against the five evaluations of a covector recovers its mixed
squared norm times the Gram determinant. -/
theorem mixedGram_covector (Y S : Matrix (Fin 5) (Fin 5) ℝ)
    (hS : ∀ i j, S i j = mixedDot (Y i) (Y j)) (n : MixedPoint) :
    dotProduct (Y *ᵥ n) (S.adjugate *ᵥ (Y *ᵥ n)) = S.det * mixedDot n n := by
  have factorization : S = Y * mixedMetric * Yᵀ :=
    Matrix.ext (fun i j => (hS i j).trans (row_pair Y Y i j).symm)
  have conjugation : Yᵀ * S.adjugate * Y = S.det • mixedMetric := by
    rw [factorization, Matrix.adjugate_mul_distrib, Matrix.adjugate_mul_distrib]
    calc
      _ = (Yᵀ * Yᵀ.adjugate) * mixedMetric.adjugate * (Y.adjugate * Y) := by
        simp only [Matrix.mul_assoc]
      _ = _ := by
        simp [Matrix.mul_adjugate, Matrix.adjugate_mul,
          Matrix.det_mul, Matrix.det_transpose, mixedMetric_det, smul_smul, adjugate_mixedMetric]
  have metric_value : dotProduct n (mixedMetric *ᵥ n) = mixedDot n n := by
    simp [mixedMetric, Matrix.mulVec_diagonal, dotProduct, Fin.sum_univ_succ, mixedDot]
    ring
  calc
    _ = dotProduct n (Yᵀ *ᵥ (S.adjugate *ᵥ (Y *ᵥ n))) := by
      rw [Matrix.dotProduct_transpose_mulVec, dotProduct_comm]
    _ = _ := by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, conjugation,
        Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, metric_value]

/-- The value of a spatial covector at the first three coordinates of a mixed point. -/
def leafPlaneValue (n : Fin 3 → ℝ) (p : MixedPoint) : ℝ :=
  n 0 * p 0 + n 1 * p 1 + n 2 * p 2

/-- Suppose the five mixed core points have squared distances encoded by S and
the leaf z completes all five null rays. If z belongs to the spatial plane
n · r = h, its five core offsets v satisfy the adjugate equation for this plane. -/
theorem leafPlane_eliminant_eq_zero (K : Fin 5 → MixedPoint) (z : MixedPoint)
    (S : Matrix (Fin 5) (Fin 5) ℝ)
    (hK : ∀ i j, mixedDot (K i-K j) (K i-K j) = -2*S i j)
    (hz : ∀ i, mixedDot (K i-z) (K i-z) = 0)
    (n : Fin 3 → ℝ) (h : ℝ) (plane : leafPlaneValue n z = h) :
    let v : Fin 5 → ℝ := fun i => leafPlaneValue n (K i) - h
    dotProduct v (S.adjugate *ᵥ v) - S.det * dotProduct n n = 0 := by
  let Y : Matrix (Fin 5) (Fin 5) ℝ := fun i => K i-z
  let N : MixedPoint := ![n 0,n 1,n 2,0,0]
  have gram (i j : Fin 5) : S i j = mixedDot (Y i) (Y j) := by
    have hd : Y i - Y j = K i - K j := by dsimp [Y]; abel
    have hp := mixed_difference (Y i) (Y j)
    rw [hd,hK,show mixedDot (Y i) (Y i) = 0 from hz i,
      show mixedDot (Y j) (Y j) = 0 from hz j] at hp
    linarith
  have offsets : Y *ᵥ N = fun i => leafPlaneValue n (K i) - h := by
    ext i
    rw [← plane]
    simp [Y,N,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,leafPlaneValue]
    ring
  have norm : mixedDot N N = dotProduct n n := by
    simp [N,mixedDot,dotProduct,Fin.sum_univ_succ, add_assoc]
  have identity := mixedGram_covector Y S gram N
  rw [offsets,norm] at identity
  exact sub_eq_zero.mpr identity

/-- The Gram matrix when the five positive deficits are indexed around their
support cycle. Its nonzero entries join consecutive indices. -/
def deficitCycle (w : Fin 5 → ℝ) : Matrix (Fin 5) (Fin 5) ℝ :=
  !![0,w 0,0,0,w 4;
     w 0,0,w 1,0,0;
     0,w 1,0,w 2,0;
     0,0,w 2,0,w 3;
     w 4,0,0,w 3,0]

def alternatingWeight (w : Fin 5 → ℝ) (i : Fin 5) : ℝ := w (i+1)*w (i+3)

def deficitCycleSign (i j : Fin 5) : ℝ := if i=j ∨ i+1=j ∨ j+1=i then 1 else -1

theorem deficitCycle_det (w : Fin 5 → ℝ) :
    (deficitCycle w).det = 2*w 0*w 1*w 2*w 3*w 4 := by
  let e : Fin 5 ≃ Fin 5 := {
    toFun := ![0,2,4,1,3]
    invFun := ![0,3,1,4,2]
    left_inv := by decide
    right_inv := by decide }
  have h : deficitCycle w = (pentagonGram (w 0) (w 4) (w 3) (w 2) (w 1)).submatrix e e := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [h,Matrix.det_submatrix_equiv_self,det_pentagonGram]
  ring

/-- The adjugate entry factors into two alternating weight products and a cyclic sign. -/
theorem deficitCycle_adjugate (w : Fin 5 → ℝ) (positive : ∀ i, 0 < w i) (i j : Fin 5) :
    (deficitCycle w).adjugate i j =
      deficitCycleSign i j * alternatingWeight w i * alternatingWeight w j := by
  let S := deficitCycle w
  let M : Matrix (Fin 5) (Fin 5) ℝ :=
    fun i j => deficitCycleSign i j * alternatingWeight w i * alternatingWeight w j
  have det : IsUnit S.det := isUnit_iff_ne_zero.mpr (by
    rw [show S.det = 2*w 0*w 1*w 2*w 3*w 4 from deficitCycle_det w]
    have h0 := positive 0
    have h1 := positive 1
    have h2 := positive 2
    have h3 := positive 3
    have h4 := positive 4
    positivity)
  have product : S*M = S.det • 1 := by
    ext i j
    rw [show S.det = 2*w 0*w 1*w 2*w 3*w 4 from deficitCycle_det w]
    rw [Matrix.mul_apply, Matrix.smul_apply]
    fin_cases i <;> fin_cases j <;>
      simp +decide [S,M,Fin.sum_univ_succ,Matrix.one_apply,
        deficitCycle,deficitCycleSign,alternatingWeight] <;> ring
  have same : S * S.adjugate = S * M := (Matrix.mul_adjugate _).trans product.symm
  apply_fun (fun P => S⁻¹*P) at same
  simp only [← Matrix.mul_assoc, Matrix.nonsing_inv_mul S det, Matrix.one_mul] at same
  exact congrFun (congrFun same i) j

/-- A covector vanishing at three core points has just two potentially nonzero
offsets. In their indices i,j its adjugate quadratic form is a single square. -/
theorem deficitCycle_two_offsets (w : Fin 5 → ℝ) (positive : ∀ i, 0 < w i) (i j : Fin 5) (s t : ℝ) :
    let v := Pi.single i s + Pi.single j t
    dotProduct v ((deficitCycle w).adjugate *ᵥ v) =
      (alternatingWeight w i*s + deficitCycleSign i j*alternatingWeight w j*t)^2 := by
  dsimp only
  simp only [Matrix.mulVec_add, add_dotProduct, single_dotProduct, Pi.add_apply,
    Matrix.mulVec_single]
  by_cases sign : i=j ∨ i+1=j ∨ j+1=i
  · have rev : j=i ∨ j+1=i ∨ i+1=j := by aesop
    simp [deficitCycle_adjugate w positive,deficitCycleSign,sign,rev]
    ring
  · have rev : ¬(j=i ∨ j+1=i ∨ i+1=j) := by aesop
    simp [deficitCycle_adjugate w positive,deficitCycleSign,sign,rev]
    ring

/-- The precise one-leaf eliminant used by the sign verifier. The sparse
offset hypothesis expresses incidence of the other three core vertices. -/
theorem singleLeaf_eliminant_eq_zero (K : Fin 5 → MixedPoint) (z : MixedPoint)
    (w : Fin 5 → ℝ) (positive : ∀ i, 0 < w i)
    (hK : ∀ i j, mixedDot (K i-K j) (K i-K j) = -2*deficitCycle w i j)
    (hz : ∀ i, mixedDot (K i-z) (K i-z) = 0) (n : Fin 3 → ℝ) (h : ℝ)
    (plane : leafPlaneValue n z = h) (i j : Fin 5) (s t : ℝ)
    (offsets : (fun k => leafPlaneValue n (K k) - h) = Pi.single i s + Pi.single j t) :
    (alternatingWeight w i*s + deficitCycleSign i j*alternatingWeight w j*t)^2 -
      (2*w 0*w 1*w 2*w 3*w 4) * dotProduct n n = 0 := by
  have identity := leafPlane_eliminant_eq_zero K z (deficitCycle w) hK hz n h plane
  dsimp only at identity
  rw [offsets,deficitCycle_two_offsets w positive,deficitCycle_det] at identity
  exact identity

/-- A common projective root of two binary quadratics forces their resultant to
vanish, including a direction with either coordinate zero. -/
theorem binaryQuadratic_resultant_eq_zero {A B C D E F s t : ℝ}
    (direction : s ≠ 0 ∨ t ≠ 0)
    (p : A*s^2 + B*s*t + C*t^2 = 0) (q : D*s^2 + E*s*t + F*t^2 = 0) :
    (A*F-C*D)^2 - (A*E-B*D)*(B*F-C*E) = 0 := by
  by_cases hs : s = 0
  · subst s
    have ht : t ≠ 0 := direction.resolve_left (not_not_intro rfl)
    simp [ht] at p q
    simp [p,q]
  by_cases ht : t = 0
  · subst t
    simp [hs] at p q
    simp [p,q]
  have l : t*((A*E-B*D)*s + (A*F-C*D)*t) = 0 := by linear_combination A*q-D*p
  have m : s*((A*F-C*D)*s + (B*F-C*E)*t) = 0 := by linear_combination F*p-C*q
  have hl := (mul_eq_zero.mp l).resolve_left ht
  have hm := (mul_eq_zero.mp m).resolve_left hs
  have eqn : t*((A*F-C*D)^2 - (A*E-B*D)*(B*F-C*E)) = 0 := by
    linear_combination (A*F-C*D)*hl - (A*E-B*D)*hm
  exact (mul_eq_zero.mp eqn).resolve_left ht

end OrigamiTorus.Type5
