module

public import OrigamiTorus.Winding.HexagonalTiling
import OrigamiTorus.Certificates.StripPolynomial
import OrigamiTorus.EightVertex.Type5.Geometry
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Tactic

/-! The six five-vertex cliques obstruct a spatial realization of the
unweighted harmonic placement for every positive definite period metric. -/

public section

namespace OrigamiTorus.Type5

open Winding Winding.Hexagonal
open scoped RealInnerProductSpace

private abbrev Poly := StripPolynomial.Coefficients
open StripPolynomial (C T H eval)
local infixl:65 " +ₚ " => StripPolynomial.add
local infixl:65 " -ₚ " => StripPolynomial.sub
local infixl:70 " *ₚ " => StripPolynomial.mul

/-- With the first basis vector of squared length one, the Gram matrix has
entries `1,t,h`. The coefficients use ascending powers of `t` and `h`. -/
private def lengthPoly (i j : Vertex) : Poly :=
  let (x,y) := markedDisplacement .type5 periodIdentity i j
  [[x*x,y*y],[2*x*y]]

private theorem eval_length (i j : Vertex) (t h : ℝ) :
    let d := markedDisplacement .type5 periodIdentity i j
    eval (lengthPoly i j) t h =
      (d.1 : ℝ)^2 + 2*t*d.1*d.2 + h*(d.2 : ℝ)^2 := by
  simp [lengthPoly,StripPolynomial.eval,StripPolynomial.evalRow,StripPolynomial.evalSeries]
  ring

private def pairs : Fin 6 → Vertex × Vertex := ![(3,0),(3,6),(3,7),(4,0),(4,6),(4,7)]

private def basisLabels (k : Fin 6) : Fin 4 → Vertex := ![2,5,(pairs k).1,(pairs k).2]

private def gramEntry (k : Fin 6) (i j : Fin 4) : Poly :=
  let a := basisLabels k i
  let b := basisLabels k j
  C (1/2) *ₚ (lengthPoly 1 a +ₚ lengthPoly 1 b -ₚ lengthPoly a b)

private def detThree (m : Fin 3 → Fin 3 → Poly) : Poly :=
  m 0 0 *ₚ m 1 1 *ₚ m 2 2 -ₚ m 0 0 *ₚ m 1 2 *ₚ m 2 1 -ₚ m 0 1 *ₚ m 1 0 *ₚ m 2 2
    +ₚ m 0 1 *ₚ m 1 2 *ₚ m 2 0 +ₚ m 0 2 *ₚ m 1 0 *ₚ m 2 1 -ₚ m 0 2 *ₚ m 1 1 *ₚ m 2 0

private def gramDet (k : Fin 6) : Poly :=
  let m := gramEntry k
  let term (j : Fin 4) := m 0 j *ₚ detThree (fun i l => m i.succ (j.succAbove l))
  term 0 -ₚ term 1 +ₚ term 2 -ₚ term 3

private theorem eval_gramDet (k : Fin 6) (t h : ℝ) :
    eval (gramDet k) t h =
      (Matrix.of fun i j => eval (gramEntry k i j) t h).det := by
  rw [Matrix.det_succ_row_zero]
  norm_num [gramDet,detThree,Fin.sum_univ_succ,Matrix.det_fin_three,Matrix.submatrix_apply,Fin.succAbove]
  ring

/-- An integer linear combination of the six quartics, with quadratic
multipliers, gives a nonzero multiple of the cube of the period determinant.
Use `u,v,w` for the squared lengths of the first, second, and difference
periods. Permuting them permutes the six clique determinants. -/
private def multiplier (u v w : Poly) : Poly :=
  C 607196 *ₚ u *ₚ u +ₚ C 880957 *ₚ v *ₚ v -ₚ C 2088318 *ₚ w *ₚ w
    -ₚ C 5053317 *ₚ u *ₚ v +ₚ C 2018978 *ₚ u *ₚ w +ₚ C 3727249 *ₚ v *ₚ w

private def weight (k : Fin 6) : Poly :=
  let u := C 1
  let v := H
  let w := C 1 +ₚ H -ₚ C 2 *ₚ T
  ![multiplier u v w, multiplier v w u, multiplier w u v,
    multiplier w v u, multiplier u w v, multiplier v u w] k

private def combination : Poly :=
  ((List.finRange 6).map (fun k => weight k *ₚ gramDet k)).foldr StripPolynomial.add []

private def target : Poly :=
  C (35057610 * 64 / 14745600) *ₚ StripPolynomial.pow (H -ₚ T *ₚ T) 3

private def allZero (p : Poly) : Bool := p.all fun row => row.all (· == 0)

private theorem eval_zero {p : Poly} (hz : allZero p = true) (t h : ℝ) : eval p t h = 0 := by
  have row_zero (r : List ℚ) (hr : r.all (· == 0) = true) : StripPolynomial.evalRow h r = 0 := by
    induction r with
    | nil => rfl
    | cons a r ih =>
      simp only [List.all_cons,Bool.and_eq_true,beq_iff_eq] at hr
      change (a : ℝ) + h * StripPolynomial.evalRow h r = 0
      simp [hr.1,ih hr.2]
  induction p with
  | nil => rfl
  | cons r p ih =>
    change (r.all (· == 0) && allZero p) = true at hz
    simp only [Bool.and_eq_true] at hz
    obtain ⟨hr,hp⟩ := hz
    change StripPolynomial.evalRow h r + t * eval p t h = 0
    simp [row_zero r hr,ih hp]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem coefficient_check : allZero (combination -ₚ target) = true := by decide +kernel

private theorem incompatible {t h : ℝ} (hpos : t^2 < h)
    (hz : ∀ k, eval (gramDet k) t h = 0) : False := by
  have hc (l : List (Fin 6)) :
      eval ((l.map (fun k => weight k *ₚ gramDet k)).foldr StripPolynomial.add []) t h = 0 := by
    induction l with
    | nil => rfl
    | cons k l ih => simp [hz,ih]
  have he := eval_zero coefficient_check t h
  rw [StripPolynomial.eval_sub,show eval combination t h = 0 from hc _] at he
  norm_num [target] at he
  nlinarith

/-- The harmonic representatives in the dual cycle basis have no spatial
placement with their 24 edge lengths, for any positive definite Gram matrix
`[[A,B],[B,C]]` on that basis. No spatial embedding assumption is needed. -/
theorem harmonic_lengths_impossible (A B C' : ℝ) (hA : 0 < A) (hdet : B^2 < A*C') :
    ¬ ∃ q : Vertex → EuclideanSpace ℝ (Fin 3), ∀ i j, Type2.Adjacent faces i j →
      let d := markedDisplacement .type5 periodIdentity i j
      dist (q i) (q j)^2 = A*(d.1 : ℝ)^2 + 2*B*d.1*d.2 + C'*(d.2 : ℝ)^2 := by
  rintro ⟨q,hq⟩
  let t := B/A
  let h := C'/A
  have hpos : t^2 < h := by
    dsimp [t,h]
    rw [div_pow, div_lt_div_iff₀ (sq_pos_of_pos hA) hA]
    nlinarith only [mul_lt_mul_of_pos_right hdet hA]
  apply incompatible hpos
  intro k
  let b := basisLabels k
  let v (i : Fin 4) := q (b i) - q 1
  have ed (i j : Vertex) (hij : i = j ∨ Type2.Adjacent faces i j) :
      dist (q i) (q j)^2 = A * eval (lengthPoly i j) t h := by
    rw [eval_length]
    rcases hij with rfl | he
    · have hh : ∀ i : Vertex, markedDisplacement .type5 periodIdentity i i = 0 := by decide +kernel
      simp [hh]
    · rw [hq _ _ he]
      dsimp [t,h]
      field_simp
  have ec (i : Fin 4) : Type2.Adjacent faces 1 (b i) := by
    rw [adjacency_test]
    change edgeList.contains (orderedEdge 1 (basisLabels k i)) = true
    revert k i
    decide +kernel
  have ep (i j : Fin 4) : b i = b j ∨ Type2.Adjacent faces (b i) (b j) := by
    rw [adjacency_test]
    change basisLabels k i = basisLabels k j ∨
      edgeList.contains (orderedEdge (basisLabels k i) (basisLabels k j)) = true
    clear ec
    revert k i j
    decide +kernel
  have hg : Matrix.gram ℝ v = A • Matrix.of (fun i j => eval (gramEntry k i j) t h) := by
    ext i j
    rw [Matrix.gram_apply,real_inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two]
    have hd (i : Fin 4) : ‖v i‖ = dist (q 1) (q (b i)) := (dist_eq_norm_sub' _ _).symm
    have hd' : ‖v i-v j‖ = dist (q (b i)) (q (b j)) := by simp [v,dist_eq_norm]
    simp only [← sq,hd,hd',ed _ _ (Or.inr (ec i)),ed _ _ (Or.inr (ec j)),ed _ _ (ep i j),
      Matrix.smul_apply,Matrix.of_apply,smul_eq_mul,gramEntry,StripPolynomial.eval_mul,
      StripPolynomial.eval_C,StripPolynomial.eval_add,StripPolynomial.eval_sub,Rat.cast_div,
      Rat.cast_one,Rat.cast_ofNat,b]
    ring
  have hzero : (Matrix.gram ℝ v).det = 0 := by
    by_contra hn
    have hc := (Matrix.linearIndependent_of_det_gram_ne_zero hn).fintype_card_le_finrank
    simp at hc
  rw [hg,Matrix.det_smul,← eval_gramDet] at hzero
  exact (mul_eq_zero.mp hzero).resolve_left (pow_ne_zero _ hA.ne')

private theorem displace_in_marking (M : PeriodMatrix) (i j : Vertex) :
    markedDisplacement .type5 M i j =
      mapPeriodRat M (markedDisplacement .type5 periodIdentity i j) := by
  ext <;> simp [markedDisplacement,placement,markedShift,rationalPeriod,mapPeriod,mapPeriodRat,
    periodIdentity] <;> ring

/-- In the coordinates of the quotient construction, changing the marked
period basis still gives no spatial realization of the harmonic sheet. -/
theorem harmonic_marked_lengths_impossible (M : PeriodMatrix) (hM : periodDet M ≠ 0)
    (x y : ℝ) (hy : y ≠ 0) :
    ¬ ∃ q : Vertex → EuclideanSpace ℝ (Fin 3), ∀ i j, Type2.Adjacent faces i j →
      dist (q i) (q j)^2 = metricSq x y (asReal (markedDisplacement .type5 M i j)) := by
  let U : Plane ℝ := ((M.1.1 : ℝ) + x*M.1.2, y*M.1.2)
  let V : Plane ℝ := ((M.2.1 : ℝ) + x*M.2.2, y*M.2.2)
  have hn : cross U V ≠ 0 := by
    have h : cross U V = y*(periodDet M : ℝ) := by
      simp [U,V,cross,periodDet]
      ring
    exact h ▸ mul_ne_zero hy (Int.cast_ne_zero.mpr hM)
  have hd : dot U V ^ 2 < squared2 U * squared2 V := by
    have h : squared2 U * squared2 V - dot U V ^ 2 = cross U V ^ 2 := by
      simp [squared2,dot,cross]
      ring
    linarith [sq_pos_of_ne_zero hn]
  have hU : 0 < squared2 U := by
    by_contra! h
    have hV : 0 ≤ squared2 V := add_nonneg (mul_self_nonneg _) (mul_self_nonneg _)
    linarith [mul_nonpos_of_nonpos_of_nonneg h hV,sq_nonneg (dot U V)]
  rintro ⟨q,hq⟩
  apply harmonic_lengths_impossible _ _ _ hU hd
  refine ⟨q, fun i j hij => ?_⟩
  rw [hq i j hij,displace_in_marking M i j]
  simp [metricSq,asReal,mapPeriodRat,squared2,dot,U,V]
  ring

end OrigamiTorus.Type5
