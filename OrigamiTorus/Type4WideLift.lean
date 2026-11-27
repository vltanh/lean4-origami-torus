module

public import OrigamiTorus.Type4LiftWideCell0
public import OrigamiTorus.Type4LiftWideCell1
public import OrigamiTorus.Type4LiftWideCell2
public import OrigamiTorus.Type4LiftWideCell3
public import OrigamiTorus.Type4LiftWideCell4
public import OrigamiTorus.Type4StripLift
import Mathlib.Tactic

/-! The five height cells on the first Type 4 chart and the open-strip theorem. -/

@[expose] public section

namespace OrigamiTorus.Type4.StripLift

open StripPolynomial (Coefficients eval)

private theorem signClosed_cases (p : Coefficients) :
    signClosed p = 1 ∨ signClosed p = -1 ∨ signClosed p = 0 := by
  unfold signClosed
  split
  · exact Or.inl rfl
  · split
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)

private theorem signClosed_pos (p : Coefficients) {t h : ℝ} (ht : 0 ≤ t) (ht' : t ≤ 1)
    (hh : 0 ≤ h) (hp : signClosed p = 1) : 0 < eval p t h := by
  apply StripPolynomial.eval_pos_of_strictOnClosed p ht ht' hh
  unfold signClosed at hp
  split at hp
  · assumption
  · split at hp <;> norm_num at hp

private theorem signClosed_neg (p : Coefficients) {t h : ℝ} (ht : 0 ≤ t) (ht' : t ≤ 1)
    (hh : 0 ≤ h) (hp : signClosed p = -1) : eval p t h < 0 := by
  apply neg_pos.mp
  rw [← StripPolynomial.eval_neg]
  apply StripPolynomial.eval_pos_of_strictOnClosed _ ht ht' hh
  unfold signClosed at hp
  split at hp
  · norm_num at hp
  · split at hp
    · assumption
    · norm_num at hp

theorem signClosed_mul_pos (p q : Coefficients) {t h : ℝ} (ht : 0 ≤ t) (ht' : t ≤ 1)
    (hh : 0 ≤ h) (hp : 0 < signClosed p*signClosed q) : 0 < eval p t h*eval q t h := by
  rcases signClosed_cases p with hp' | hp' | hp' <;>
    rcases signClosed_cases q with hq' | hq' | hq' <;> norm_num [hp',hq'] at hp
  · exact mul_pos (signClosed_pos p ht ht' hh hp') (signClosed_pos q ht ht' hh hq')
  · exact mul_pos_of_neg_of_neg (signClosed_neg p ht ht' hh hp') (signClosed_neg q ht ht' hh hq')

theorem signClosed_mul_neg (p q : Coefficients) {t h : ℝ} (ht : 0 ≤ t) (ht' : t ≤ 1)
    (hh : 0 ≤ h) (hp : signClosed p*signClosed q < 0) : eval p t h*eval q t h < 0 := by
  rcases signClosed_cases p with hp' | hp' | hp' <;>
    rcases signClosed_cases q with hq' | hq' | hq' <;> norm_num [hp',hq'] at hp
  · exact mul_neg_of_pos_of_neg (signClosed_pos p ht ht' hh hp') (signClosed_neg q ht ht' hh hq')
  · exact mul_neg_of_neg_of_pos (signClosed_neg p ht ht' hh hp') (signClosed_pos q ht ht' hh hq')

theorem signClosed_nonzero (p : Coefficients) {t h : ℝ} (ht : 0 ≤ t) (ht' : t ≤ 1)
    (hh : 0 ≤ h) (hp : signClosed p ≠ 0) : eval p t h ≠ 0 := by
  rcases signClosed_cases p with h | h | h
  · exact (signClosed_pos p ht ht' hh h).ne'
  · exact (signClosed_neg p ht ht' hh h).ne
  · exact (hp h).elim

private theorem allWidePairs (i : Fin 5) : (Type7.disjointPairs Type7.flippedFaces).all (pairCheckWide i) = true := by
  rw [← (show (List.finRange 28).flatMap pairChunk = Type7.disjointPairs Type7.flippedFaces by decide +kernel)]
  apply List.all_eq_true.mpr
  intro q hq
  obtain ⟨j,_,hjq⟩ := List.mem_flatMap.mp hq
  have hc : (pairChunk j).all (pairCheckWide i) = true := by
    fin_cases i
    · exact widePairChunks0 j
    · exact widePairChunks1 j
    · exact widePairChunks2 j
    · exact widePairChunks3 j
    · exact widePairChunks4 j
  exact (List.all_eq_true.mp hc) q hjq

private theorem allWideAreas (i : Fin 5) : quads.all (areaCheckWide i) = true := by
  rw [← tetrahedronChunks_cover]
  apply List.all_eq_true.mpr
  intro q hq
  obtain ⟨j,_,hjq⟩ := List.mem_flatMap.mp hq
  have hc : (tetrahedronChunk j).all (areaCheckWide i) = true := by
    fin_cases i
    · exact wideAreaChunks0 j
    · exact wideAreaChunks1 j
    · exact wideAreaChunks2 j
    · exact wideAreaChunks3 j
    · exact wideAreaChunks4 j
  exact (List.all_eq_true.mp hc) q hjq

private theorem wide_area_noncollinear (i : Fin 5) {t h : ℝ} (ht : 0 ≤ t) (ht' : t ≤ 1) (hh : 0 ≤ h)
    (a b c d : Vertex) (hab : a < b) (hbc : b < c) (hcd : c < d) :
    let p := fun k => (eval (wideP i k).1 t h,eval (wideP i k).2 t h)
    area p b c d ≠ 0 ∨ area p a c d ≠ 0 ∨ area p a b d ≠ 0 ∨ area p a b c ≠ 0 := by
  have hm : (a,b,c,d) ∈ quads := by simp [quads,hab,hbc,hcd]
  have hc := (List.all_eq_true.mp (allWideAreas i)) _ hm
  simp only [areaCheckWide,List.any_cons,List.any_nil,Bool.or_false,Bool.or_eq_true,bne_iff_ne] at hc
  dsimp only
  simp only [← eval_areaCoeffs]
  rcases hc with hc | hc | hc | hc
  · exact Or.inl (signClosed_nonzero _ ht ht' hh hc)
  · exact Or.inr (Or.inl (signClosed_nonzero _ ht ht' hh hc))
  · exact Or.inr (Or.inr (Or.inl (signClosed_nonzero _ ht ht' hh hc)))
  · exact Or.inr (Or.inr (Or.inr (signClosed_nonzero _ ht ht' hh hc)))

private theorem wide_separation (i : Fin 5) {t h : ℝ} (ht : 0 ≤ t) (ht' : t ≤ 1) (hh : 0 ≤ h)
    (q : Edge × Triangle) (hq : q ∈ Type7.disjointPairs Type7.flippedFaces) :
    isSeparated (fun k => (eval (wideP i k).1 t h,eval (wideP i k).2 t h))
      (fun k => eval (wideZ i k) t h) q := by
  have hc := (List.all_eq_true.mp (allWidePairs i)) _ hq
  rcases q with ⟨⟨a,b⟩,c,d,e⟩
  simp only [pairCheckWide,decide_eq_true_eq] at hc
  simp only [isSeparated,separates,← eval_volumeCoeffs]
  rcases hc with hc | hc | hc | hc
  · exact Or.inl (signClosed_mul_pos _ _ ht ht' hh hc)
  · exact Or.inr (Or.inl (signClosed_mul_pos _ _ ht ht' hh hc))
  · exact Or.inr (Or.inr (Or.inl (signClosed_mul_pos _ _ ht ht' hh hc)))
  · exact Or.inr (Or.inr (Or.inr (signClosed_mul_neg _ _ ht ht' hh hc)))

theorem chart_scale (x w c H J : ℝ) (hj : J ≠ 0) (v : Vertex) :
    let a := polynomialPoints x w c (H/J) 1 v
    polynomialPoints x w c H J v = (J^3*a.1,J^3*a.2) := by
  fin_cases v <;> apply Prod.ext <;>
    norm_num [polynomialPoints] <;> field_simp [hj] <;> ring

private theorem wide_cell_cover {x w : ℝ} (hd : domain false x w) :
    ∃ i : Fin 5, ((wideBounds i).1 : ℝ) ≤ x ∧ x ≤ ((wideBounds i).2 : ℝ) := by
  have hlo : 0 ≤ x := hd.1
  have hh : x ≤ (9/20 : ℝ) := hd.2.1
  by_cases h₀ : x ≤ (1/10 : ℝ)
  · exact ⟨0,by norm_num [wideBounds]; exact hlo,by norm_num [wideBounds]; exact h₀⟩
  by_cases h₁ : x ≤ (1/5 : ℝ)
  · refine ⟨1,?_,?_⟩ <;> norm_num [wideBounds] <;> linarith
  by_cases h₂ : x ≤ (3/10 : ℝ)
  · refine ⟨2,?_,?_⟩ <;> norm_num [wideBounds] <;> linarith
  by_cases h₃ : x ≤ (2/5 : ℝ)
  · refine ⟨3,?_,?_⟩ <;> norm_num [wideBounds] <;> linarith
  · refine ⟨4,?_,?_⟩ <;> norm_num [wideBounds] <;> linarith

theorem wide_cell_embedded_lift_of_separation (flipped : Bool) (i : Fin 5)
    (Z : Vertex → Coefficients) {x w : ℝ} (hd : domain false x w)
    (hlo : ((wideBounds i).1 : ℝ) ≤ x) (hhi : x ≤ ((wideBounds i).2 : ℝ))
    (hsep : ∀ {t h : ℝ}, 0 ≤ t → t ≤ 1 → 0 ≤ h →
      ∀ q ∈ Type7.disjointPairs (Type7.faceChoice flipped),
        isSeparated (fun k => (eval (wideP i k).1 t h,eval (wideP i k).2 t h))
          (fun k => eval (Z k) t h) q) :
    ∃ z : Vertex → ℝ, Function.Injective
      (evaluateTriangles (Type7.faceChoice flipped) (angleLift (stripBase false x w) z 1)) := by
  let a : ℝ := (wideBounds i).1
  let b : ℝ := (wideBounds i).2
  let t := (x-a)/(b-a)
  let h := w+x^2-1
  have hab : 0 < b-a := by fin_cases i <;> norm_num [a,b,wideBounds]
  have ht : 0 ≤ t := div_nonneg (sub_nonneg.mpr hlo) hab.le
  have ht' : t ≤ 1 := (div_le_iff₀ hab).mpr (by linarith only [hhi])
  have hh : 0 ≤ h := by dsimp [h]; linarith only [hd.2.2]
  have hX : eval (wideX i) t h = x := by
    simp only [wideX,StripPolynomial.eval_add,StripPolynomial.eval_mul,StripPolynomial.eval_C,
      StripPolynomial.eval_T,Rat.cast_sub]
    change a+(b-a)*t = x
    dsimp only [t]
    field_simp [hab.ne'] <;> ring
  have hW : 1-x^2+h = w := by dsimp [h]; ring
  let p (k : Vertex) := (eval (wideP i k).1 t h,eval (wideP i k).2 t h)
  let J := 20+26*x
  have hJ : J ≠ 0 := by have hx : 0 ≤ x := hd.1; dsimp [J]; positivity
  have hp (k : Vertex) : p k = (J^3*(stripPoints false x w k).1,J^3*(stripPoints false x w k).2) := by
    have he : p k = polynomialPoints x w (1/3) 33 J k := by
      simpa only [p,wideP,eval_pointCoeffs,StripPolynomial.eval_add,StripPolynomial.eval_sub,
        StripPolynomial.eval_pow,StripPolynomial.eval_C,StripPolynomial.eval_H,Rat.cast_one,
        hX,hW,heightNumerator,heightDenominator,Bool.false_eq_true,ite_false,J]
    rw [he]
    exact chart_scale x w (1/3) 33 J hJ k
  exact chart_embedded_lift_of_height_witness flipped hd p (fun k => eval (Z k) t h) (J^3)
    (pow_ne_zero _ hJ) hp (wide_area_noncollinear i ht ht' hh) (hsep ht ht' hh)

theorem wide_strip_embedded_lift {x w : ℝ} (hd : domain false x w) :
    ∃ z : Vertex → ℝ, Function.Injective
      (evaluateTriangles Type7.flippedFaces (angleLift (stripBase false x w) z 1)) := by
  obtain ⟨i,hlo,hhi⟩ := wide_cell_cover hd
  exact wide_cell_embedded_lift_of_separation true i (wideZ i) hd hlo hhi
    (fun ht ht' hh => wide_separation i ht ht' hh)

end OrigamiTorus.Type4.StripLift

namespace OrigamiTorus.Type4

/-- Every reduced modulus in the Type 4 open strip admits a piecewise-isometric
embedding whose spatial angle and modulus map has rank nine. -/
theorem open_strip_regular_realizes {x w : ℝ} (hx : 0 ≤ x) (hx' : x < 1/2) (hw : 1-x^2 ≤ w) :
    Type7.ChartRealizesWith true 1 (x+Real.sqrt w*Complex.I) SpatiallyRegular := by
  obtain ⟨second,hd⟩ := domain_covers x w hx hx' hw
  have hlift : ∃ h : Vertex → ℝ, Function.Injective
      (evaluateTriangles Type7.flippedFaces (angleLift (stripBase second x w) h 1)) := by
    cases second
    · exact StripLift.wide_strip_embedded_lift hd
    · exact end_strip_embedded_lift hd
  obtain ⟨h,hemb⟩ := hlift
  have he : complexSimilarity 1 false = id := by funext p; simp [complexSimilarity]
  exact strip_regular_realizes_of_lift hd h hemb 1 _ 1 false one_ne_zero (by rw [he,Set.image_id])

/-- Type 4 realizes every reduced modulus in the open strip. -/
theorem open_strip_realizes {x w : ℝ} (hx : 0 ≤ x) (hx' : x < 1/2) (hw : 1-x^2 ≤ w) :
    Type7.ChartRealizes true 1 (x+Real.sqrt w*Complex.I) :=
  (open_strip_regular_realizes hx hx' hw).realizes

end OrigamiTorus.Type4
