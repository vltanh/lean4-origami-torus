module

public import OrigamiTorus.Type4.WideLift
public import OrigamiTorus.Type7.LiftData
import Mathlib.Tactic

/-! Exact height certificate for the unflipped Type 7 chart near rectangles. -/

@[expose] public section

namespace OrigamiTorus.Type7

open Type4 (polynomialPoints stripBase stripPoints)
open Type4.StripLift
open StripPolynomial (Coefficients C T H eval)

def stripX : Coefficients := StripPolynomial.mul (C (1/20)) T

def stripP : Vertex → Coefficients × Coefficients :=
  pointCoeffs false stripX (StripPolynomial.add (StripPolynomial.sub (C 1) (StripPolynomial.pow stripX 2)) H)

def stripHeight (i : Vertex) : Coefficients := C ((![3/13,-3/8,-3/7,12/13,1,-1,1,0] : Vertex → ℚ) i)

def stripPairCheck := separationCheck stripP stripHeight signClosed

def stripAreaCheck (q : Vertex × Vertex × Vertex × Vertex) : Bool :=
  let (a,b,c,d) := q
  [areaCoeffs stripP b c d,areaCoeffs stripP a c d,areaCoeffs stripP a b d,areaCoeffs stripP a b c].any
    (fun p => signClosed p != 0)

set_option maxHeartbeats 0 in
check_wide_chunks stripPairChunks for 29 using stripPairChunk with stripPairCheck
set_option maxHeartbeats 0 in
check_wide_chunks stripAreaChunks for 14 using tetrahedronChunk with stripAreaCheck

theorem separation_checks_of_chunks (check : Edge × Triangle → Bool)
    (hc : ∀ i, (stripPairChunk i).all check = true) : (disjointPairs faces).all check = true := by
  rw [← (show (List.finRange 29).flatMap stripPairChunk = disjointPairs faces by decide +kernel)]
  apply List.all_eq_true.mpr
  intro p hp
  obtain ⟨i,_,hi⟩ := List.mem_flatMap.mp hp
  exact (List.all_eq_true.mp (hc i)) p hi

private theorem strip_areas_checked : quads.all stripAreaCheck = true := by
  rw [← tetrahedronChunks_cover]
  apply List.all_eq_true.mpr
  intro p hp
  obtain ⟨i,_,hi⟩ := List.mem_flatMap.mp hp
  exact (List.all_eq_true.mp (stripAreaChunks i)) p hi

private theorem strip_area_noncollinear {t h : ℝ} (ht : 0 ≤ t) (ht' : t ≤ 1) (hh : 0 ≤ h)
    (a b c d : Vertex) (hab : a < b) (hbc : b < c) (hcd : c < d) :
    let p := fun k => (eval (stripP k).1 t h,eval (stripP k).2 t h)
    area p b c d ≠ 0 ∨ area p a c d ≠ 0 ∨ area p a b d ≠ 0 ∨ area p a b c ≠ 0 := by
  have hm : (a,b,c,d) ∈ quads := by simp [quads,hab,hbc,hcd]
  have hc := (List.all_eq_true.mp strip_areas_checked) _ hm
  simp only [stripAreaCheck,List.any_cons,List.any_nil,Bool.or_false,Bool.or_eq_true,bne_iff_ne] at hc
  dsimp only
  simp only [← eval_areaCoeffs]
  rcases hc with hc | hc | hc | hc
  · exact Or.inl (signClosed_nonzero _ ht ht' hh hc)
  · exact Or.inr (Or.inl (signClosed_nonzero _ ht ht' hh hc))
  · exact Or.inr (Or.inr (Or.inl (signClosed_nonzero _ ht ht' hh hc)))
  · exact Or.inr (Or.inr (Or.inr (signClosed_nonzero _ ht ht' hh hc)))

theorem separation_of_check {t h : ℝ} {sign : Coefficients → ℤ}
    {P : Vertex → Coefficients × Coefficients} {Z : Vertex → Coefficients}
    (hpos : ∀ a b, 0 < sign a*sign b → 0 < eval a t h*eval b t h)
    (hneg : ∀ a b, sign a*sign b < 0 → eval a t h*eval b t h < 0)
    (q : Edge × Triangle) (hc : separationCheck P Z sign q = true) :
    isSeparated (fun k => (eval (P k).1 t h,eval (P k).2 t h)) (fun k => eval (Z k) t h) q := by
  rcases q with ⟨⟨a,b⟩,c,d,e⟩
  simp only [separationCheck,decide_eq_true_eq] at hc
  simp only [isSeparated,separates,← eval_volumeCoeffs]
  rcases hc with hc | hc | hc | hc
  · exact Or.inl (hpos _ _ hc)
  · exact Or.inr (Or.inl (hpos _ _ hc))
  · exact Or.inr (Or.inr (Or.inl (hpos _ _ hc)))
  · exact Or.inr (Or.inr (Or.inr (hneg _ _ hc)))

private theorem strip_separation {t h : ℝ} (ht : 0 ≤ t) (ht' : t ≤ 1) (hh : 0 ≤ h)
    (q : Edge × Triangle) (hq : q ∈ disjointPairs faces) :
    isSeparated (fun k => (eval (stripP k).1 t h,eval (stripP k).2 t h))
      (fun k => eval (stripHeight k) t h) q :=
  separation_of_check (fun a b => signClosed_mul_pos a b ht ht' hh)
    (fun a b => signClosed_mul_neg a b ht ht' hh) q
    ((List.all_eq_true.mp (separation_checks_of_chunks stripPairCheck stripPairChunks)) q hq)

theorem strip_embedded_lift {x w : ℝ} (hx : 0 ≤ x) (hx' : x ≤ 1/20) (hw : 1-x^2 ≤ w) :
    ∃ z : Vertex → ℝ, Function.Injective (evaluateTriangles faces (angleLift (stripBase false x w) z 1)) := by
  have hd : Type4.domain false x w := ⟨hx,by change x ≤ 9/20; linarith,hw⟩
  let t := 20*x
  let h := w+x^2-1
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have ht' : t ≤ 1 := by dsimp [t]; linarith
  have hh : 0 ≤ h := by dsimp [h]; linarith only [hw]
  have hX : eval stripX t h = x := by
    simp [stripX,t]
  have hW : 1-x^2+h = w := by dsimp [h]; ring
  let p (k : Vertex) := (eval (stripP k).1 t h,eval (stripP k).2 t h)
  let J := 20+26*x
  have hJ : J ≠ 0 := by dsimp [J]; positivity
  have hp (k : Vertex) : p k = (J^3*(stripPoints false x w k).1,J^3*(stripPoints false x w k).2) := by
    have he : p k = polynomialPoints x w (1/3) 33 J k := by
      simpa only [p,stripP,eval_pointCoeffs,StripPolynomial.eval_add,StripPolynomial.eval_sub,
        StripPolynomial.eval_pow,StripPolynomial.eval_C,StripPolynomial.eval_H,Rat.cast_one,
        hX,hW,Type4.heightNumerator,Type4.heightDenominator,Bool.false_eq_true,ite_false,J]
    rw [he]
    exact chart_scale x w (1/3) 33 J hJ k
  exact Type4.chart_embedded_lift_of_height_witness false hd p (fun k => eval (stripHeight k) t h)
    (J^3) (pow_ne_zero _ hJ) hp (strip_area_noncollinear ht ht' hh) (strip_separation ht ht' hh)

end OrigamiTorus.Type7
