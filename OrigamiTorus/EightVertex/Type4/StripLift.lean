module

public import OrigamiTorus.EightVertex.Type4.LiftData
public import OrigamiTorus.EightVertex.Type4.StripInflation
public import OrigamiTorus.EightVertex.Type6.Lift
import Mathlib.Tactic

/-! Exact height lift on the Type 4 chart adjacent to the open endpoint. -/

@[expose] public section

namespace OrigamiTorus.Type4

namespace StripLift

open StripPolynomial (Coefficients C T H eval)

private theorem eval_zero (t h : ℝ) : eval [] t h = 0 := rfl

theorem eval_pointCoeffs (second : Bool) (x w : Coefficients) (t h : ℝ) (v : Vertex) :
    ((eval (pointCoeffs second x w v).1 t h), eval (pointCoeffs second x w v).2 t h) =
      polynomialPoints (eval x t h) (eval w t h) (if second then 2/3 else 1/3)
        (heightNumerator second (eval x t h)) (heightDenominator second (eval x t h)) v := by
  cases second <;> fin_cases v <;>
    apply Prod.ext <;> norm_num [pointCoeffs,polynomialPoints,heightNumerator,heightDenominator,
      eval_zero] <;> ring <;> simp

theorem eval_areaCoeffs (p : Vertex → Coefficients × Coefficients)
    (a b c : Vertex) (t h : ℝ) :
    eval (areaCoeffs p a b c) t h =
      area (fun i => (eval (p i).1 t h,eval (p i).2 t h)) a b c := by
  simp [areaCoeffs,area]

theorem eval_volumeCoeffs (p : Vertex → Coefficients × Coefficients) (z : Vertex → Coefficients)
    (a b c d : Vertex) (t h : ℝ) :
    eval (volumeCoeffs p z a b c d) t h =
      volume (fun i => (eval (p i).1 t h,eval (p i).2 t h)) (fun i => eval (z i) t h) a b c d := by
  simp [volumeCoeffs,volume,eval_areaCoeffs]

private theorem sign_cases (p : Coefficients) :
    sgn p = 1 ∨ sgn p = -1 ∨ sgn p = 0 := by
  unfold sgn
  split
  · exact Or.inl rfl
  · split
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)

private theorem sign_pos (p : Coefficients) {t h : ℝ} (ht : 0 ≤ t) (ht' : t < 1)
    (hh : 0 ≤ h) (hp : sgn p = 1) : 0 < eval p t h := by
  apply StripPolynomial.eval_pos_of_strictOnOpen p ht ht' hh
  unfold sgn at hp
  split at hp
  · assumption
  · split at hp <;> norm_num at hp

private theorem sign_neg (p : Coefficients) {t h : ℝ} (ht : 0 ≤ t) (ht' : t < 1)
    (hh : 0 ≤ h) (hp : sgn p = -1) : eval p t h < 0 := by
  apply neg_pos.mp
  rw [← StripPolynomial.eval_neg]
  apply StripPolynomial.eval_pos_of_strictOnOpen _ ht ht' hh
  unfold sgn at hp
  split at hp
  · norm_num at hp
  · split at hp
    · assumption
    · norm_num at hp

theorem sign_mul_pos (p q : Coefficients) {t h : ℝ} (ht : 0 ≤ t) (ht' : t < 1)
    (hh : 0 ≤ h) (hp : 0 < sgn p*sgn q) : 0 < eval p t h*eval q t h := by
  rcases sign_cases p with hp' | hp' | hp' <;>
    rcases sign_cases q with hq' | hq' | hq' <;> norm_num [hp',hq'] at hp
  · exact mul_pos (sign_pos p ht ht' hh hp') (sign_pos q ht ht' hh hq')
  · exact mul_pos_of_neg_of_neg (sign_neg p ht ht' hh hp') (sign_neg q ht ht' hh hq')

theorem sign_mul_neg (p q : Coefficients) {t h : ℝ} (ht : 0 ≤ t) (ht' : t < 1)
    (hh : 0 ≤ h) (hp : sgn p*sgn q < 0) : eval p t h*eval q t h < 0 := by
  rcases sign_cases p with hp' | hp' | hp' <;>
    rcases sign_cases q with hq' | hq' | hq' <;> norm_num [hp',hq'] at hp
  · exact mul_neg_of_pos_of_neg (sign_pos p ht ht' hh hp') (sign_neg q ht ht' hh hq')
  · exact mul_neg_of_neg_of_pos (sign_neg p ht ht' hh hp') (sign_pos q ht ht' hh hq')

private theorem sign_nonzero (p : Coefficients) {t h : ℝ} (ht : 0 ≤ t) (ht' : t < 1)
    (hh : 0 ≤ h) (hp : sgn p ≠ 0) : eval p t h ≠ 0 := by
  rcases sign_cases p with h | h | h
  · exact (sign_pos p ht ht' hh h).ne'
  · exact (sign_neg p ht ht' hh h).ne
  · exact (hp h).elim

def areaCheck (q : Vertex × Vertex × Vertex × Vertex) : Bool :=
  let (a,b,c,d) := q
  [areaCoeffs endP b c d,areaCoeffs endP a c d,areaCoeffs endP a b d,areaCoeffs endP a b c].any
    (fun p => sgn p != 0)

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem allAreas : quads.all areaCheck = true := by decide +kernel

private theorem evaluated_area_noncollinear {t h : ℝ} (ht : 0 ≤ t) (ht' : t < 1) (hh : 0 ≤ h)
    (a b c d : Vertex) (hab : a < b) (hbc : b < c) (hcd : c < d) :
    let p := fun i => (eval (endP i).1 t h, eval (endP i).2 t h)
    area p b c d ≠ 0 ∨ area p a c d ≠ 0 ∨ area p a b d ≠ 0 ∨ area p a b c ≠ 0 := by
  have hm : (a,b,c,d) ∈ quads := by simp [quads,hab,hbc,hcd]
  have hc := (List.all_eq_true.mp allAreas) _ hm
  simp only [areaCheck,List.any_cons,List.any_nil, Bool.or_false,Bool.or_eq_true,bne_iff_ne] at hc
  dsimp only
  simp only [← eval_areaCoeffs]
  rcases hc with hc | hc | hc | hc
  · exact Or.inl (sign_nonzero _ ht ht' hh hc)
  · exact Or.inr (Or.inl (sign_nonzero _ ht ht' hh hc))
  · exact Or.inr (Or.inr (Or.inl (sign_nonzero _ ht ht' hh hc)))
  · exact Or.inr (Or.inr (Or.inr (sign_nonzero _ ht ht' hh hc)))

private theorem evaluated_separation {t h : ℝ} (ht : 0 ≤ t) (ht' : t < 1) (hh : 0 ≤ h)
    (q : Edge × Triangle) (hq : q ∈ Type7.disjointPairs Type7.flippedFaces) :
    isSeparated (fun i => (eval (endP i).1 t h,eval (endP i).2 t h)) (fun i => eval (endZ i) t h) q := by
  have hc := (List.all_eq_true.mp allPairs) _ hq
  rcases q with ⟨⟨a,b⟩,c,d,e⟩
  simp only [pairCheck,decide_eq_true_eq] at hc
  simp only [isSeparated,separates,← eval_volumeCoeffs]
  rcases hc with hc | hc | hc | hc
  · exact Or.inl (sign_mul_pos _ _ ht ht' hh hc)
  · exact Or.inr (Or.inl (sign_mul_pos _ _ ht ht' hh hc))
  · exact Or.inr (Or.inr (Or.inl (sign_mul_pos _ _ ht ht' hh hc)))
  · exact Or.inr (Or.inr (Or.inr (sign_mul_neg _ _ ht ht' hh hc)))

private theorem endP_eq {x w : ℝ} (t h : ℝ)
    (hx : 9/20+1/20*t = x) (hw : 1-x^2+h = w) :
    (fun i => (eval (endP i).1 t h,eval (endP i).2 t h)) = stripPoints true x w := by
  have hX : eval endX t h = x := by simpa [endX] using hx
  funext i
  simpa only [endP,eval_pointCoeffs,StripPolynomial.eval_add,StripPolynomial.eval_sub,
    StripPolynomial.eval_pow,StripPolynomial.eval_C,StripPolynomial.eval_H,Rat.cast_one,hX,hw,
    heightNumerator,heightDenominator,trapezoidHeight,stripPoints,ite_true]

end StripLift

open StripLift (endP endZ)
open StripPolynomial (eval)

/-- A common horizontal scale preserves injectivity of the spatial lift. -/
theorem chart_embedded_lift_of_height_witness (flipped : Bool) {second : Bool} {x w : ℝ} (hd : domain second x w)
    (p : Vertex → ℝ × ℝ) (z₀ : Vertex → ℝ) (κ : ℝ) (hκ : κ ≠ 0)
    (hp : ∀ i, p i = (κ*(stripPoints second x w i).1,κ*(stripPoints second x w i).2))
    (hnc : ∀ a b c d : Vertex, a < b → b < c → c < d →
      area p b c d ≠ 0 ∨ area p a c d ≠ 0 ∨ area p a b d ≠ 0 ∨ area p a b c ≠ 0)
    (hsep : ∀ q ∈ Type7.disjointPairs (Type7.faceChoice flipped), isSeparated p z₀ q) :
    ∃ z : Vertex → ℝ, Function.Injective
      (evaluateTriangles (Type7.faceChoice flipped) (angleLift (stripBase second x w) z 1)) := by
  obtain ⟨z',hz'⟩ := exists_generic_lift_of_noncollinear p hnc
  obtain ⟨z,hg,hs⟩ := exists_generic_separating_lift p z₀ z'
    (Type7.disjointPairs (Type7.faceChoice flipped)) hz' hsep
  have he := spatialTriangles_isClosedEmbedding p z _ hg
    (Type7.rectangular_edgeTriangleSeparated flipped p z hg hs)
  let y := Real.sqrt w
  have hy : y ≠ 0 := (Real.sqrt_pos.mpr (domain_bounds hd).2.2).ne'
  let L : Point3 →ₗ[ℝ] Point3 :=
    { toFun := fun p => (κ⁻¹*p.1,y*κ⁻¹*p.2.1,p.2.2)
      map_add' := by intro a b; ext <;> simp [mul_add]
      map_smul' := by intro r p; ext <;> simp [mul_comm r,← mul_assoc] }
  have hL : Function.Injective L := by
    intro a b hab
    change (κ⁻¹*a.1,y*κ⁻¹*a.2.1,a.2.2) = (κ⁻¹*b.1,y*κ⁻¹*b.2.1,b.2.2) at hab
    obtain ⟨h₁,h₂,h₃⟩ := Prod.mk.inj hab |>.imp_right Prod.mk.inj
    exact Prod.ext (mul_left_cancel₀ (inv_ne_zero hκ) h₁)
      (Prod.ext (mul_left_cancel₀ (mul_ne_zero hy (inv_ne_zero hκ)) h₂) h₃)
  let P (i : Vertex) : Point3 := ((p i).1,(p i).2,z i)
  have hEq : L ∘ P = angleLift (stripBase second x w) z 1 := by
    funext i
    dsimp [L,P,angleLift,stripBase,Type7.physicalComplex]
    rw [hp i]
    congr 2 <;> field_simp [hκ] <;> ring
  refine ⟨z,?_⟩
  rw [← hEq,evaluateTriangles_comp_linear]
  exact hL.comp he.injective

theorem embedded_lift_of_height_witness {second : Bool} {x w : ℝ} (hd : domain second x w)
    (p : Vertex → ℝ × ℝ) (z₀ : Vertex → ℝ) (κ : ℝ) (hκ : κ ≠ 0)
    (hp : ∀ i, p i = (κ*(stripPoints second x w i).1,κ*(stripPoints second x w i).2))
    (hnc : ∀ a b c d : Vertex, a < b → b < c → c < d →
      area p b c d ≠ 0 ∨ area p a c d ≠ 0 ∨ area p a b d ≠ 0 ∨ area p a b c ≠ 0)
    (hsep : ∀ q ∈ Type7.disjointPairs Type7.flippedFaces, isSeparated p z₀ q) :
    ∃ z : Vertex → ℝ, Function.Injective
      (evaluateTriangles Type7.flippedFaces (angleLift (stripBase second x w) z 1)) :=
  chart_embedded_lift_of_height_witness true hd p z₀ κ hκ hp hnc hsep

theorem end_strip_embedded_lift_of_separation (flipped : Bool) {x w : ℝ} (hd : domain true x w)
    (hsep : ∀ {t h : ℝ}, 0 ≤ t → t < 1 → 0 ≤ h →
      ∀ q ∈ Type7.disjointPairs (Type7.faceChoice flipped),
        isSeparated (fun i => (eval (endP i).1 t h,eval (endP i).2 t h)) (fun i => eval (endZ i) t h) q) :
    ∃ z : Vertex → ℝ, Function.Injective
      (evaluateTriangles (Type7.faceChoice flipped) (angleLift (stripBase true x w) z 1)) := by
  let t := 20*x-9
  let h := w+x^2-1
  have ht : 0 ≤ t := by
    have hx : (9/20 : ℝ) ≤ x := hd.1
    dsimp [t]
    linarith
  have ht' : t < 1 := by
    have hx : x < (1/2 : ℝ) := hd.2.1
    dsimp [t]
    linarith
  have hh : 0 ≤ h := by dsimp [h]; linarith only [hd.2.2]
  have hP : (fun i => (eval (endP i).1 t h,eval (endP i).2 t h)) = stripPoints true x w :=
    StripLift.endP_eq t h (by dsimp [t]; ring) (by dsimp [h]; ring)
  have hnc := StripLift.evaluated_area_noncollinear ht ht' hh
  rw [hP] at hnc
  have hs := hsep ht ht' hh
  rw [hP] at hs
  refine chart_embedded_lift_of_height_witness flipped hd (stripPoints true x w) (fun i => eval (endZ i) t h)
    1 one_ne_zero ?_ hnc hs
  intro i
  simp

theorem end_strip_embedded_lift {x w : ℝ} (hd : domain true x w) :
    ∃ z : Vertex → ℝ, Function.Injective
      (evaluateTriangles Type7.flippedFaces (angleLift (stripBase true x w) z 1)) :=
  end_strip_embedded_lift_of_separation true hd (fun ht ht' hh => StripLift.evaluated_separation ht ht' hh)

/-- The chart adjoining (x=1/2) has an embedded piecewise-isometric Type 4
realization at every included modulus. -/
theorem end_strip_realizes {x w : ℝ} (hd : domain true x w) :
    Type7.ChartRealizes true 1 (x+Real.sqrt w*Complex.I) := by
  obtain ⟨h,hemb⟩ := end_strip_embedded_lift hd
  have he : complexSimilarity 1 false = id := by funext p; simp [complexSimilarity]
  exact strip_realizes_of_lift hd h hemb 1 _ 1 false one_ne_zero (by rw [he,Set.image_id])


end OrigamiTorus.Type4
