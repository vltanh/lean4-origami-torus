module

public import OrigamiTorus.EightVertex.Type5.LeafRank
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Tactic
import Mathlib.Topology.Instances.Matrix

/-! Positive right-hand sides for the five-cycle Gram matrix of a Type 5 leaf. -/

public section

open scoped Matrix

namespace OrigamiTorus.Type5

private def cycleForm (a b c d e : ℝ) : ℝ :=
  (a+b+c+d+e)^2 - 4*(a*b+b*c+c*d+d*e+e*a)

private theorem cycleForm_rotate (a b c d e : ℝ) :
    cycleForm a b c d e = cycleForm b c d e a := by
  unfold cycleForm
  ring

/-- Removing a minimum coordinate leaves the path with edges AB, BC and CD. -/
private theorem cycleForm_last_min {a b c d t : ℝ} (ht : 0 < t)
    (ha : t ≤ a) (hb : t ≤ b) (hc : t ≤ c) (hd : t ≤ d) :
    0 < cycleForm a b c d t := by
  have h :
      cycleForm a b c d t =
      (a+c-b-d)^2 + 4*(a-t)*(d-t) + 2*t*((a-t)+(b-t)+(c-t)+(d-t)) + 5*t^2 := by
    unfold cycleForm
    ring
  rw [h]
  have := sub_nonneg.mpr ha
  have := sub_nonneg.mpr hb
  have := sub_nonneg.mpr hc
  have := sub_nonneg.mpr hd
  positivity

private theorem cycleForm_pos (v : Fin 5 → ℝ) (hv : ∀ i, 0 < v i) :
    0 < cycleForm (v 0) (v 1) (v 2) (v 3) (v 4) := by
  obtain ⟨k, _, hk⟩ := Finset.exists_min_image Finset.univ v Finset.univ_nonempty
  have hm (i : Fin 5) : v k ≤ v i := hk i (Finset.mem_univ i)
  fin_cases k
  · rw [cycleForm_rotate]
    exact cycleForm_last_min (hv 0) (hm 1) (hm 2) (hm 3) (hm 4)
  · rw [cycleForm_rotate, cycleForm_rotate (v 1)]
    exact cycleForm_last_min (hv 1) (hm 2) (hm 3) (hm 4) (hm 0)
  · rw [← cycleForm_rotate (v 4), ← cycleForm_rotate (v 3)]
    exact cycleForm_last_min (hv 2) (hm 3) (hm 4) (hm 0) (hm 1)
  · rw [← cycleForm_rotate (v 4)]
    exact cycleForm_last_min (hv 3) (hm 4) (hm 0) (hm 1) (hm 2)
  · exact cycleForm_last_min (hv 4) (hm 0) (hm 1) (hm 2) (hm 3)

/-- For the weighted complementary cycle, the inverse quadratic form is
strictly positive throughout the open positive orthant. -/
theorem pentagonGram_inv_positive {a b c d e : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (he : 0 < e)
    (v : Fin 5 → ℝ) (hv : ∀ i, 0 < v i) :
    0 < dotProduct v ((pentagonGram a b c d e)⁻¹ *ᵥ v) := by
  let S := pentagonGram a b c d e
  let P := 2*a*b*c*d*e
  let m : Fin 5 → ℝ := ![c*e,b*e,b*d,a*d,a*c]
  let y (i : Fin 5) := m i * v i
  let s := y 0 + y 1 + y 2 + y 3 + y 4
  let x : Fin 5 → ℝ := ![
    m 0 * (s-2*(y 4+y 1)), m 1 * (s-2*(y 0+y 2)), m 2 * (s-2*(y 1+y 3)),
    m 3 * (s-2*(y 2+y 4)), m 4 * (s-2*(y 3+y 0))]
  have hP : 0 < P := by dsimp [P]; positivity
  have hdet : IsUnit S.det := isUnit_iff_ne_zero.mpr <|
    (show S.det = P from det_pentagonGram ..) ▸ hP.ne'
  have hx : S *ᵥ x = P • v := by
    funext i
    fin_cases i <;> simp [S, pentagonGram, x, s, y, m, P, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ] <;> ring
  have hx' : x = P • (S⁻¹ *ᵥ v) := by
    calc
      x = S⁻¹ *ᵥ (S *ᵥ x) := by rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hdet,
                                      Matrix.one_mulVec]
      _ = P • (S⁻¹ *ᵥ v) := by rw [hx, Matrix.mulVec_smul]
  have hq : dotProduct v x = cycleForm (y 0) (y 1) (y 2) (y 3) (y 4) := by
    simp [dotProduct, Fin.sum_univ_succ, x, cycleForm, s, y, m]
    ring
  have hy (i : Fin 5) : 0 < y i := by
    have hm : 0 < m i := by fin_cases i <;> simp [m] <;> positivity
    exact mul_pos hm (hv i)
  have hp : 0 < dotProduct v x := hq.symm ▸ cycleForm_pos y hy
  rw [hx', dotProduct_smul, smul_eq_mul] at hp
  exact pos_of_mul_pos_right hp hP.le


/-- Three spatial coordinates followed by the two intrinsic coordinates. -/
abbrev MixedPoint := Fin 5 → ℝ

@[expose] def mixedDot (u v : MixedPoint) : ℝ :=
  u 0*v 0 + u 1*v 1 + u 2*v 2 - u 3*v 3 - u 4*v 4

private def mixedMetric : Matrix (Fin 5) (Fin 5) ℝ := Matrix.diagonal ![1,1,1,-1,-1]

private theorem mixedMetric_det : mixedMetric.det = 1 := by
  simp [mixedMetric, Matrix.det_diagonal, Fin.prod_univ_succ]

private theorem row_pair {m n : Type*} (U : Matrix m (Fin 5) ℝ)
    (V : Matrix n (Fin 5) ℝ) (i : m) (j : n) :
    (U * mixedMetric * Vᵀ) i j = mixedDot (U i) (V j) := by
  simp [mixedMetric, Matrix.mul_apply, Fin.sum_univ_succ, mixedDot]
  ring

private theorem row_dot {m : Type*} (U : Matrix m (Fin 5) ℝ) (v : MixedPoint) (i : m) :
    ((U * mixedMetric) *ᵥ v) i = mixedDot (U i) v := by
  simp [mixedMetric, Matrix.mulVec, dotProduct, Matrix.mul_diagonal, Fin.sum_univ_succ, mixedDot]
  ring

private theorem mixed_comm (u v : MixedPoint) : mixedDot u v = mixedDot v u := by
  dsimp [mixedDot]
  ring

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1700000 in
private theorem normal_line (U : Matrix (Fin 4) (Fin 5) ℝ)
    (hG : 0 < (U * mixedMetric * Uᵀ).det) :
    ∃ n : MixedPoint, 0 < mixedDot n n ∧ (∀ i, mixedDot (U i) n = 0) ∧
      ∀ v : MixedPoint, (∀ i, mixedDot (U i) v = 0) → ∃ c : ℝ, v = c • n := by
  let G := U * mixedMetric * Uᵀ
  let L := U * mixedMetric
  let A : Matrix (Fin 5) (Fin 5) ℝ := Fin.cons (0 : MixedPoint) L
  have hA0 (j : Fin 5) : A 0 j = 0 := rfl
  have hA : A.det = 0 := by rw [Matrix.det_succ_row_zero]; simp [hA0]
  obtain ⟨n, hn, hAn⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hA
  have horth (i : Fin 4) : mixedDot (U i) n = 0 := by
    rw [← row_dot]; exact congrFun hAn i.succ
  let W : Matrix (Fin 5) (Fin 5) ℝ := Fin.cons n U
  have hW : W.det ≠ 0 := by
    intro hz
    have ht : Wᵀ.det = 0 := by rw [Matrix.det_transpose,hz]
    obtain ⟨v, hv, hzero⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr ht
    let t : Fin 4 → ℝ := Fin.tail v
    have hcomb : v 0 • n + Uᵀ *ᵥ t = 0 := by
      funext j
      have := congrFun hzero j
      change (∑ k, W k j * v k) = 0 at this
      rw [Fin.sum_univ_succ] at this
      change v 0 * n j + ∑ k : Fin 4, U k j * v k.succ = 0
      rwa [mul_comm (v 0)]
    have hLn : L *ᵥ n = 0 := funext <| fun i => (row_dot U n i).trans (horth i)
    have hGt : G *ᵥ t = 0 := by
      have h := congrArg (fun u => L *ᵥ u) hcomb
      simpa only [Matrix.mulVec_add, Matrix.mulVec_smul, hLn, smul_zero, zero_add,
        Matrix.mulVec_mulVec, Matrix.mulVec_zero, L, G] using h
    have ht' := Matrix.eq_zero_of_mulVec_eq_zero hG.ne' hGt
    rw [ht', Matrix.mulVec_zero, add_zero] at hcomb
    have h0 := (smul_eq_zero.mp hcomb).resolve_right hn
    apply hv
    funext i
    refine Fin.cases h0 (fun k => ?_) i
    exact congrFun ht' k
  let H := W * mixedMetric * Wᵀ
  have hH : 0 < H.det := by
    simp only [H, Matrix.det_mul, mixedMetric_det, mul_one, Matrix.det_transpose]
    exact mul_self_pos.mpr hW
  have htop : H 0 0 = mixedDot n n := row_pair W W 0 0
  have hrow (j : Fin 4) : H 0 j.succ = 0 :=
    (row_pair W W 0 j.succ).trans ((mixed_comm n (U j)).trans (horth j))
  have hblock : H.submatrix Fin.succ Fin.succ = G := by
    ext i j
    exact (row_pair W W i.succ j.succ).trans (row_pair U U i j).symm
  have hdet : H.det = mixedDot n n * G.det := by
    rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ]
    simp [hrow, htop, hblock]
  have hnn : 0 < mixedDot n n := pos_of_mul_pos_left (hdet ▸ hH) hG.le
  refine ⟨n, hnn, horth, ?_⟩
  intro v hv
  let c := mixedDot n v / mixedDot n n
  refine ⟨c, ?_⟩
  have hWM := Matrix.mulVec_injective_iff_isUnit.mpr <|
    (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr (show (W*mixedMetric).det ≠ 0 by
      simpa [Matrix.det_mul,mixedMetric_det] using hW))
  apply hWM
  rw [Matrix.mulVec_smul]
  funext i
  simp only [Pi.smul_apply, smul_eq_mul, row_dot]
  refine Fin.cases ?_ (fun k => ?_) i
  · change mixedDot n v = c * mixedDot n n
    simp [c, hnn.ne']
  · change mixedDot (U k) v = c * mixedDot (U k) n
    rw [hv k,horth k,mul_zero]


private def diffGram (a b c d e : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![0,-d,a-e,b;
    -d,-2*d,-d-e,c-d;
    a-e,-d-e,-2*e,-e;
    b,c-d,-e,0]

private theorem diffGram_det_pos {a b c d e : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (he : 0 < e) :
    0 < (diffGram a b c d e).det := by
  let m : Fin 5 → ℝ := ![c*e,b*e,b*d,a*d,a*c]
  have hm (i : Fin 5) : 0 < m i := by fin_cases i <;> simp [m] <;> positivity
  have h : (diffGram a b c d e).det = cycleForm (m 0) (m 1) (m 2) (m 3) (m 4) := by
    rw [Matrix.det_succ_row_zero]
    simp [Fin.sum_univ_succ, Matrix.det_fin_three, Matrix.submatrix_apply, Fin.succAbove, diffGram, m, cycleForm]
    ring
  rw [h]
  exact cycleForm_pos m hm

private theorem diffGram_eq (a b c d e : ℝ) (i j : Fin 4) :
    diffGram a b c d e i j = pentagonGram a b c d e i.castSucc j.castSucc -
      pentagonGram a b c d e i.castSucc 4 - pentagonGram a b c d e j.castSucc 4 := by
  fin_cases i <;> fin_cases j <;> simp [diffGram, pentagonGram] <;> ring

private theorem center_weights {a b c d e : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (he : 0 < e) :
    let f : Fin 4 → ℝ := ![0,-d,-e,0]
    ∃ w : Fin 4 → ℝ, diffGram a b c d e *ᵥ w = f ∧ dotProduct w f < 0 := by
  intro f
  let S := pentagonGram a b c d e
  let x := S⁻¹ *ᵥ (1 : Fin 5 → ℝ)
  let τ := dotProduct (1 : Fin 5 → ℝ) x
  have hτ : 0 < τ := pentagonGram_inv_positive ha hb hc hd he 1 (fun _ => by simp)
  have hdet : IsUnit S.det := isUnit_iff_ne_zero.mpr (show 0 < S.det by
    rw [show S.det = 2*a*b*c*d*e from det_pentagonGram ..]; positivity).ne'
  have hi : S *ᵥ x = 1 := by
    rw [show x = S⁻¹ *ᵥ 1 from rfl, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet,
      Matrix.one_mulVec]
  have h (i : Fin 5) := congrFun hi i
  have A := h 0
  have B := h 1
  have C := h 2
  have D := h 3
  have E := h 4
  simp [S,pentagonGram, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] at A B C D E
  have hsum : τ = x 0 + x 1 + x 2 + x 3 + x 4 := by
    simp [τ, dotProduct,Fin.sum_univ_succ]; ring
  refine ⟨fun i => x i.castSucc / τ, ?_, ?_⟩
  · funext i
    fin_cases i <;> simp [diffGram, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, f] <;>
      field_simp [hτ.ne'] <;> rw [hsum] <;> linarith
  · have hneg : dotProduct (fun i : Fin 4 => x i.castSucc / τ) f = -1/τ := by
      simp [f, dotProduct, Fin.sum_univ_succ]
      field_simp [hτ.ne']
      linarith
    rw [hneg]
    exact div_neg_of_neg_of_pos (by norm_num) hτ

private theorem mixed_add_right (u v w : MixedPoint) :
    mixedDot u (v+w) = mixedDot u v + mixedDot u w := by dsimp [mixedDot]; ring

private theorem mixed_smul_right (u v : MixedPoint) (s : ℝ) :
    mixedDot u (s • v) = s * mixedDot u v := by dsimp [mixedDot]; ring

private theorem mixed_sub_right (u v w : MixedPoint) :
    mixedDot u (v-w) = mixedDot u v - mixedDot u w := by dsimp [mixedDot]; ring

private theorem mixed_difference (u v : MixedPoint) :
    mixedDot (u-v) (u-v) = mixedDot u u + mixedDot v v - 2*mixedDot u v := by
  dsimp [mixedDot]
  ring

private theorem mixed_line (u n : MixedPoint) (t : ℝ) :
    mixedDot (u+t • n) (u+t • n) =
      mixedDot u u + 2*t*mixedDot u n + t^2*mixedDot n n := by
  dsimp [mixedDot]
  ring

private theorem mixed_combination (U : Matrix (Fin 4) (Fin 5) ℝ) (w : Fin 4 → ℝ)
    (v : MixedPoint) :
    mixedDot (Uᵀ *ᵥ w) v = dotProduct w ((U*mixedMetric) *ᵥ v) := by
  have h (x : MixedPoint) : mixedDot x v = dotProduct x (mixedMetric *ᵥ v) := by
    simp [mixedMetric, Matrix.mulVec_diagonal, dotProduct, Fin.sum_univ_succ, mixedDot]
    ring
  rw [h, dotProduct_comm, Matrix.dotProduct_transpose_mulVec, Matrix.mulVec_mulVec]

private def leafRows (K : Fin 5 → MixedPoint) : Matrix (Fin 4) (Fin 5) ℝ :=
  fun i => K i.castSucc - K 4

private def leafGram (K : Fin 5 → MixedPoint) := leafRows K * mixedMetric * (leafRows K)ᵀ

private def leafNormal (U : Matrix (Fin 4) (Fin 5) ℝ) : MixedPoint :=
  fun j => (-1)^j.val * ((U*mixedMetric).submatrix id j.succAbove).det

private theorem cofactor_pair (U : Matrix (Fin 4) (Fin 5) ℝ) (v : MixedPoint) :
    dotProduct v (leafNormal U) = Matrix.det (Fin.cons v (U*mixedMetric)) := by
  let V : Matrix (Fin 5) (Fin 5) ℝ := Fin.cons v (U*mixedMetric)
  change dotProduct v (leafNormal U) = V.det
  rw [Matrix.det_succ_row_zero]
  apply Finset.sum_congr rfl
  intro i _
  change v i * ((-1)^i.val * _) = (-1)^i.val * v i * _
  have hh : (U * mixedMetric).submatrix id i.succAbove = V.submatrix Fin.succ i.succAbove := rfl
  rw [hh]; ring

private theorem canonical_normal (U : Matrix (Fin 4) (Fin 5) ℝ)
    (hG : 0 < (U*mixedMetric*Uᵀ).det) :
    0 < mixedDot (leafNormal U) (leafNormal U) ∧ (∀ i, mixedDot (U i) (leafNormal U) = 0) ∧
      ∀ v : MixedPoint, (∀ i, mixedDot (U i) v = 0) → ∃ c : ℝ, v = c • leafNormal U := by
  let L := U * mixedMetric
  let N := leafNormal U
  have horth (i : Fin 4) : mixedDot (U i) N = 0 := by
    rw [← row_dot]
    change dotProduct (L i) (leafNormal U) = 0
    rw [cofactor_pair]
    apply Matrix.det_zero_of_row_eq (Fin.succ_ne_zero i).symm
    rfl
  obtain ⟨n,hq,hn,hspan⟩ := normal_line U hG
  obtain ⟨s,hs⟩ := hspan N horth
  have hN : N ≠ 0 := by
    intro hz
    let W : Matrix (Fin 5) (Fin 5) ℝ := Fin.cons n U
    let H := W * mixedMetric * Wᵀ
    have hrow (i : Fin 4) : H 0 i.succ = 0 :=
      (row_pair W W 0 i.succ).trans ((mixed_comm n (U i)).trans (hn i))
    have hblock : H.submatrix Fin.succ Fin.succ = U*mixedMetric*Uᵀ := by
      ext i j
      exact (row_pair W W i.succ j.succ).trans (row_pair U U i j).symm
    have hh : 0 < H.det := by
      rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ]
      simpa [hrow, hblock, show H 0 0 = mixedDot n n from row_pair W W 0 0] using mul_pos hq hG
    let WJ := W*mixedMetric
    have hEq : Fin.cons (WJ 0) L = WJ := by
      funext i j
      refine Fin.cases rfl (fun k => ?_) i
      rfl
    have hd : WJ.det = 0 := by
      rw [← hEq, ← cofactor_pair]
      change dotProduct _ N = 0
      rw [hz, dotProduct_zero]
    exact hh.ne' (by rw [show H = WJ * Wᵀ from rfl, Matrix.det_mul, hd, zero_mul])
  have hs0 : s ≠ 0 := fun hh => hN (by rw [hs,hh,zero_smul])
  refine ⟨?_,horth,?_⟩
  · change 0 < mixedDot N N
    rw [hs, mixed_smul_right, mixed_comm, mixed_smul_right, ← mul_assoc]
    exact mul_pos (mul_self_pos.mpr hs0) hq
  · intro v hv
    obtain ⟨t,ht⟩ := hspan v hv
    refine ⟨t/s,?_⟩
    change v = (t/s) • N
    rw [hs, smul_smul, div_mul_cancel₀ _ hs0,ht]

private noncomputable def leafRhs (K : Fin 5 → MixedPoint) : Fin 4 → ℝ :=
  fun i => mixedDot (leafRows K i) (leafRows K i) / 2

private noncomputable def leafOffset (K : Fin 5 → MixedPoint) : MixedPoint :=
  (leafRows K)ᵀ *ᵥ ((leafGram K)⁻¹ *ᵥ leafRhs K)

/-- Either sign gives a global choice of a root of the five squared-distance equations. -/
noncomputable def leafBranch (K : Fin 5 → MixedPoint) (positive : Bool) : MixedPoint :=
  let u := leafOffset K
  let n := leafNormal (leafRows K)
  let t := Real.sqrt (-mixedDot u u / mixedDot n n)
  K 4 + (u + (if positive then t else -t) • n)

private theorem leafGram_eq (K : Fin 5 → MixedPoint) {a b c d e : ℝ}
    (hK : ∀ i j, mixedDot (K i-K j) (K i-K j) = -2*pentagonGram a b c d e i j) :
    leafGram K = diffGram a b c d e := by
  ext i j
  rw [leafGram, row_pair, diffGram_eq]
  have hij : leafRows K i - leafRows K j = K i.castSucc - K j.castSucc := by dsimp [leafRows]; abel
  have h := mixed_difference (leafRows K i) (leafRows K j)
  rw [hij, hK] at h
  dsimp [leafRows] at h ⊢
  rw [hK, hK] at h
  linarith

/-- When the five squared-distance deficits form a positive five-cycle,
exactly two simultaneous intrinsic and spatial leaf positions realize
all five distances. Their first three coordinates are spatial, the last two intrinsic. -/
theorem leafBranch_spec (K : Fin 5 → MixedPoint) {a b c d e : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (he : 0 < e)
    (hK : ∀ i j, mixedDot (K i-K j) (K i-K j) = -2*pentagonGram a b c d e i j) :
    leafBranch K true ≠ leafBranch K false ∧ ∀ z : MixedPoint,
      (∀ i, mixedDot (K i-z) (K i-z) = 0) ↔ z = leafBranch K true ∨ z = leafBranch K false := by
  let U : Matrix (Fin 4) (Fin 5) ℝ := fun i => K i.castSucc - K 4
  let f : Fin 4 → ℝ := ![0,-d,-e,0]
  have hG : U*mixedMetric*Uᵀ = diffGram a b c d e := leafGram_eq K hK
  have hdiag (i : Fin 4) : mixedDot (U i) (U i) = 2*f i := by
    rw [← row_pair U U, hG]
    fin_cases i <;> simp [diffGram, f]
  obtain ⟨w, hw, hn⟩ := center_weights ha hb hc hd he
  have hGpos : 0 < (U*mixedMetric*Uᵀ).det := by rw [hG]; exact diffGram_det_pos ha hb hc hd he
  have hw' : (leafGram K)⁻¹ *ᵥ leafRhs K = w := by
    have hf : leafRhs K = f := by
      funext i
      change mixedDot (U i) (U i) / 2 = _
      rw [hdiag]; ring
    change diffGram a b c d e *ᵥ w = f at hw
    rw [hf, ← hw, ← hG]
    change (U*mixedMetric*Uᵀ)⁻¹ *ᵥ ((U*mixedMetric*Uᵀ) *ᵥ w) = w
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hGpos.ne'), Matrix.one_mulVec]
  let u := Uᵀ *ᵥ w
  have hUu : (U*mixedMetric) *ᵥ u = f := by
    rw [show u = Uᵀ *ᵥ w from rfl, Matrix.mulVec_mulVec, hG]
    exact hw
  have huf (i : Fin 4) : mixedDot (U i) u = f i := (row_dot U u i).symm.trans (congrFun hUu i)
  have hu : mixedDot u u < 0 := by
    rw [show mixedDot u u = dotProduct w ((U*mixedMetric) *ᵥ u) from mixed_combination U w u, hUu]
    exact hn
  let n := leafNormal U
  obtain ⟨hpos,hperp,hspan⟩ := canonical_normal U hGpos
  have hp : mixedDot u n = 0 := by
    have h : (U*mixedMetric) *ᵥ n = 0 := funext (fun i => (row_dot U n i).trans (hperp i))
    rw [show mixedDot u n = _ from mixed_combination U w n, h, dotProduct_zero]
  let t := Real.sqrt (-mixedDot u u / mixedDot n n)
  have ht0 : 0 < -mixedDot u u / mixedDot n n := div_pos (neg_pos.mpr hu) hpos
  have ht : 0 < t := Real.sqrt_pos.mpr ht0
  have ht2 : t^2 * mixedDot n n = -mixedDot u u := by
    rw [show t^2 = _ from Real.sq_sqrt ht0.le, div_mul_cancel₀ _ hpos.ne']
  let z (s : ℝ) := K 4 + (u + s • n)
  have zinj : Function.Injective z := by
    intro s v hh
    have hsm : s • n = v • n := add_left_cancel (add_left_cancel hh)
    have h := congrArg (mixedDot n) hsm
    rw [mixed_smul_right,mixed_smul_right] at h
    exact mul_right_cancel₀ hpos.ne' h
  have hroot (b : Bool) : leafBranch K b = z (if b then t else -t) := by
    simp only [leafBranch, leafOffset, hw']
    rfl
  rw [hroot,hroot]
  refine ⟨zinj.ne (by simp; linarith), ?_⟩
  intro p
  let y := p - K 4
  have test : (∀ i, mixedDot (K i-p) (K i-p) = 0) ↔
      mixedDot y y = 0 ∧ ∀ i, mixedDot (U i) y = f i := by
    have h₄ : K 4-p = -y := neg_sub _ _ |>.symm
    have hq₄ : mixedDot (K 4-p) (K 4-p) = mixedDot y y := by
      rw [h₄]; dsimp [mixedDot]; ring
    have hi (i : Fin 4) : mixedDot (K i.castSucc-p) (K i.castSucc-p) =
        2*f i + mixedDot y y - 2*mixedDot (U i) y := by
      have heq : K i.castSucc-p = U i - y := by dsimp [U,y]; abel
      rw [heq, mixed_difference, hdiag]
    constructor
    · intro h
      have h4 := h 4
      rw [hq₄] at h4
      refine ⟨h4, fun i => ?_⟩
      have h1 := h i.castSucc
      rw [hi, h4] at h1
      linarith
    · rintro ⟨h4,hf⟩ i
      refine Fin.lastCases ?_ (fun k => ?_) i
      · exact hq₄.trans h4
      · rw [hi, hf, h4]; ring
  rw [test]
  constructor
  · rintro ⟨hy,hf⟩
    obtain ⟨s,hs⟩ := hspan (y-u) (fun i => by rw [mixed_sub_right, hf, huf, sub_self])
    have hyu : y = u + s • n := by rw [← hs]; abel
    have hz : p = z s := by dsimp [z]; rw [← hyu]; dsimp [y]; abel
    rw [hyu, mixed_line, hp, mul_zero, add_zero] at hy
    have hsq : s^2 = t^2 := by
      apply mul_right_cancel₀ hpos.ne' (b := mixedDot n n)
      linarith
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h | h
    · exact Or.inl (h ▸ hz)
    · exact Or.inr (h ▸ hz)
  · intro h
    have hgood (s : ℝ) (hs : s^2 = t^2) (hz : p = z s) :
        mixedDot y y = 0 ∧ ∀ i, mixedDot (U i) y = f i := by
      have hy : y = u + s • n := by change p - K 4 = _; rw [hz]; dsimp [z]; abel
      rw [hy, mixed_line, hp, hs]
      refine ⟨by linarith, fun i => ?_⟩
      rw [mixed_add_right, mixed_smul_right, huf, hperp, mul_zero, add_zero]
    exact h.elim (hgood t rfl) (hgood (-t) (by ring))


/-- Exactly two mixed positions solve the five leaf equations. -/
theorem positive_cycle_completions (K : Fin 5 → MixedPoint) {a b c d e : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (he : 0 < e)
    (hK : ∀ i j, mixedDot (K i-K j) (K i-K j) = -2*pentagonGram a b c d e i j) :
    ∃ p q : MixedPoint, p ≠ q ∧ ∀ z : MixedPoint,
      (∀ i, mixedDot (K i-z) (K i-z) = 0) ↔ z = p ∨ z = q :=
  ⟨_, _,leafBranch_spec K ha hb hc hd he hK⟩

/-- The five null rays at either completion of a positive cycle form a basis
of the mixed coordinate space. -/
theorem positive_cycle_rays_independent (K : Fin 5 → MixedPoint) (z : MixedPoint)
    {a b c d e : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (he : 0 < e)
    (hK : ∀ i j, mixedDot (K i-K j) (K i-K j) = -2*pentagonGram a b c d e i j)
    (hz : ∀ i, mixedDot (K i-z) (K i-z) = 0) :
    LinearIndependent ℝ (fun i => K i-z) := by
  let Y : Matrix (Fin 5) (Fin 5) ℝ := fun i => K i-z
  have hY : Y * mixedMetric * Yᵀ = pentagonGram a b c d e := by
    ext i j
    rw [row_pair]
    have heq : Y i - Y j = K i - K j := by dsimp [Y]; abel
    have h := mixed_difference (Y i) (Y j)
    rw [heq,hK,show mixedDot (Y i) (Y i) = 0 from hz i,
      show mixedDot (Y j) (Y j) = 0 from hz j] at h
    linarith
  have hdet := congrArg Matrix.det hY
  rw [Matrix.det_mul, Matrix.det_mul, mixedMetric_det, mul_one, Matrix.det_transpose,
    det_pentagonGram] at hdet
  have hn : Y.det ≠ 0 := by
    intro h
    rw [h,zero_mul] at hdet
    have : 0 < 2*a*b*c*d*e := by positivity
    linarith
  exact Matrix.linearIndependent_rows_of_isUnit ((Matrix.isUnit_iff_isUnit_det _).mpr
    (isUnit_iff_ne_zero.mpr hn))

def mixedIntrinsic (u : MixedPoint) : Plane ℝ := (u 3,u 4)

/-- A pair of independent, mutually orthogonal null rays in signature (3,2)
projects to a nondegenerate intrinsic triangle. -/
theorem null_pair_intrinsic_cross {u v : MixedPoint}
    (hu : mixedDot u u = 0) (hv : mixedDot v v = 0) (ho : mixedDot u v = 0)
    (hi : LinearIndependent ℝ ![u,v]) : cross (mixedIntrinsic u) (mixedIntrinsic v) ≠ 0 := by
  have eq (s t : ℝ) (h₃ : s*u 3 + t*v 3 = 0) (h₄ : s*u 4 + t*v 4 = 0) :
      s = 0 ∧ t = 0 := by
    let w := s • u + t • v
    have hw : mixedDot w w = s^2*mixedDot u u + 2*s*t*mixedDot u v + t^2*mixedDot v v := by
      dsimp [w, mixedDot]; ring
    rw [hu,hv,ho] at hw
    have h : (w 0)^2 + (w 1)^2 + (w 2)^2 = 0 := by
      change w 3 = 0 at h₃
      change w 4 = 0 at h₄
      simpa [mixedDot, h₃, h₄, sq, add_assoc] using hw
    apply LinearIndependent.pair_iff.mp hi
    change w = 0
    funext i
    have h0 := sq_nonneg (w 0)
    have h1 := sq_nonneg (w 1)
    have h2 := sq_nonneg (w 2)
    fin_cases i
    · change w 0 = 0; nlinarith only [h,h1,h2]
    · change w 1 = 0; nlinarith only [h,h0,h2]
    · change w 2 = 0; nlinarith only [h,h0,h1]
    · exact h₃
    · exact h₄
  intro h
  change u 3*v 4-u 4*v 3 = 0 at h
  obtain ⟨h₄,h₄'⟩ := eq (v 4) (-u 4) (by linear_combination h) (by ring)
  obtain ⟨h₃,h₃'⟩ := eq (v 3) (-u 3) (by ring) (by linear_combination -h)
  have h3 : u 3 = 0 := neg_eq_zero.mp h₃'
  have h4 : u 4 = 0 := neg_eq_zero.mp h₄'
  exact one_ne_zero (eq 1 0 (by simp [h3]) (by simp [h4])).1

/-- Every intrinsic leaf face stays nondegenerate on either completion.
The zero entry is the length-matching condition for the link edge. -/
theorem positive_cycle_face_nondegenerate (K : Fin 5 → MixedPoint) (z : MixedPoint)
    {a b c d e : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (he : 0 < e)
    (hK : ∀ i j, mixedDot (K i-K j) (K i-K j) = -2*pentagonGram a b c d e i j)
    (hz : ∀ i, mixedDot (K i-z) (K i-z) = 0)
    {i j : Fin 5} (hne : i ≠ j) (hedge : pentagonGram a b c d e i j = 0) :
    cross (mixedIntrinsic (K i-z)) (mixedIntrinsic (K j-z)) ≠ 0 := by
  have hlin := positive_cycle_rays_independent K z ha hb hc hd he hK hz
  have inj : Function.Injective (![i,j] : Fin 2 → Fin 5) := by
    intro k l h; fin_cases k <;> fin_cases l <;> simp_all
  have hf : (fun k => K k-z) ∘ (![i,j] : Fin 2 → Fin 5) = ![K i-z,K j-z] := by
    funext k; fin_cases k <;> rfl
  have hp := hlin.comp _ inj
  rw [hf] at hp
  apply null_pair_intrinsic_cross (hz i) (hz j) _ hp
  have h := mixed_difference (K i-z) (K j-z)
  rw [show (K i-z)-(K j-z) = K i-K j by abel, hK, hedge, hz, hz] at h
  linarith

/-- In a continuous family of cores with positive five-cycle deficits,
both choices of the leaf are continuous on the whole parameter space. -/
theorem continuous_leafBranch {X : Type*} [TopologicalSpace X] (K : X → Fin 5 → MixedPoint)
    (hc : Continuous K)
    (hK : ∀ x, ∃ a b c d e : ℝ, 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d ∧ 0 < e ∧
      ∀ i j, mixedDot (K x i-K x j) (K x i-K x j) = -2*pentagonGram a b c d e i j)
    (b : Bool) : Continuous fun x => leafBranch (K x) b := by
  have hG (x : X) : 0 < (leafGram (K x)).det := by
    obtain ⟨a,b,c,d,e,ha,hb,hc,hd,he,h⟩ := hK x
    rw [leafGram_eq _ h]
    exact diffGram_det_pos ha hb hc hd he
  have cU : Continuous fun x => leafRows (K x) :=
    continuous_matrix fun i j => (hc.matrix_elem i.castSucc j).sub (hc.matrix_elem 4 j)
  have cL : Continuous fun x => leafRows (K x)*mixedMetric := cU.matrix_mul continuous_const
  have cG : Continuous fun x => leafGram (K x) := cL.matrix_mul cU.matrix_transpose
  have cI : Continuous fun x => (leafGram (K x))⁻¹ := by
    apply continuous_iff_continuousAt.mpr
    intro x
    apply (continuousAt_matrix_inv _ ?_).comp cG.continuousAt
    rw [show (Ring.inverse : ℝ → ℝ) = Inv.inv by funext t; exact Ring.inverse_eq_inv t]
    exact continuousAt_inv₀ (hG x).ne'
  have cN : Continuous fun x => leafNormal (leafRows (K x)) := by
    apply continuous_pi
    intro j
    apply continuous_const.mul
    exact (continuous_matrix fun i k => cL.matrix_elem i (j.succAbove k)).matrix_det
  have cQ {A : X → MixedPoint} (h : Continuous A) :
      Continuous fun x => mixedDot (A x) (A x) := by unfold mixedDot; fun_prop
  have cf : Continuous fun x => leafRhs (K x) := by
    apply continuous_pi
    intro i
    exact (cQ ((continuous_apply i).comp cU)).div_const _
  have co : Continuous fun x => leafOffset (K x) :=
    cU.matrix_transpose.matrix_mulVec (cI.matrix_mulVec cf)
  have ct : Continuous fun x => Real.sqrt
      (-mixedDot (leafOffset (K x)) (leafOffset (K x)) /
        mixedDot (leafNormal (leafRows (K x))) (leafNormal (leafRows (K x)))) :=
    Real.continuous_sqrt.comp ((cQ co).neg.div (cQ cN)
      (fun x => (canonical_normal _ (hG x)).1.ne'))
  cases b
  · exact ((continuous_apply 4).comp hc).add (co.add (ct.neg.smul cN))
  · exact ((continuous_apply 4).comp hc).add (co.add (ct.smul cN))

end OrigamiTorus.Type5
