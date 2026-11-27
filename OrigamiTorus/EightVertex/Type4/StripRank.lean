module

public import OrigamiTorus.EightVertex.Type4.Rank
public import OrigamiTorus.EightVertex.Type4.MarkedShape
import Mathlib.Analysis.Calculus.TangentCone.Prod
import Mathlib.Tactic

/-! At the chart boundary the two independent shape directions are obtained
from the parameters `x` and `w + x² - 1`. -/

@[expose] public section

noncomputable section

open Filter Set
open scoped Topology

namespace OrigamiTorus.Type4

open Type7 (planarEdgeSq)

def stripPoints (second : Bool) (x w : ℝ) : Vertex → ℝ × ℝ :=
  polynomialPoints x w (if second then 2/3 else 1/3) (trapezoidHeight second x) 1

def stripBase (second : Bool) (x w : ℝ) : Vertex → ℂ :=
  Type7.physicalComplex w ∘ stripPoints second x w

theorem strip_markingChartValid {second : Bool} {x w : ℝ} (hd : domain second x w) :
    MarkingChartValid (stripBase second x w) := by
  obtain ⟨h356,h352,h623,h625⟩ := poly_chart_flipSigns hd
  exact markingChartValid_of_areas (stripPoints second x w) w (domain_bounds hd).2.2
    (poly_chart_face_signs hd) h356 h352 h623 h625

theorem strip_flipped_face_orientation {second : Bool} {x w : ℝ} (hd : domain second x w)
    (f : Triangle × Bool) (hf : f ∈ Type7.orientedFlippedFaces) :
    let p := stripPoints second x w
    if f.2 then 0 < area p f.1.1 f.1.2.1 f.1.2.2 else area p f.1.1 f.1.2.1 f.1.2.2 < 0 := by
  rw [Type7.orientedFlippedFaces,List.mem_append] at hf
  obtain ⟨_,_,h623,h625⟩ := poly_chart_flipSigns hd
  rcases hf with hm | hm
  · have hs := poly_chart_face_signs hd f (List.mem_filter.mp hm).1
    cases h : f.2
    · simpa [h,stripPoints,neg_pos] using hs
    · simpa [h,stripPoints] using hs
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl
    · change 0 < area (stripPoints second x w) 6 3 2
      have he : area (stripPoints second x w) 6 3 2 = -area (stripPoints second x w) 6 2 3 := by
        unfold area
        ring
      exact he ▸ neg_pos.mpr h623
    · exact h625

theorem strip_flipped_corners_nondegenerate {second : Bool} {x w : ℝ} (hd : domain second x w) :
    let z := stripBase second x w
    ∀ f ∈ Type7.flippedFaces, ∀ v a b, cornerRays v f = some (a,b) →
      z a ≠ z v ∧ z b ≠ z v ∧ 0 < InnerProductGeometry.angle (z a-z v) (z b-z v) ∧
        InnerProductGeometry.angle (z a-z v) (z b-z v) < Real.pi := by
  have hf : Type7.orientedFlippedFaces.map Prod.fst = Type7.flippedFaces := by decide +kernel
  rw [← hf]
  exact planarCorners_nondegenerate_of_face_areas Type7.orientedFlippedFaces (stripPoints second x w) w
    (domain_bounds hd).2.2 (strip_flipped_face_orientation hd)

private def parameterSquare (q : ℝ × ℝ) : ℝ := 1-q.1^2+q.2

private def parameterRegion (second : Bool) : Set (ℝ × ℝ) :=
  (if second then Ico (9/20) (1/2) else Icc 0 (9/20)) ×ˢ Ici 0

private theorem mem_parameterRegion_iff (second : Bool) (q : ℝ × ℝ) :
    q ∈ parameterRegion second ↔ domain second q.1 (parameterSquare q) := by
  cases second <;> simp [parameterRegion,domain,parameterSquare,and_assoc]

private theorem uniqueDiffWithinAt_parameterRegion {second : Bool} {q : ℝ × ℝ}
    (hq : q ∈ parameterRegion second) : UniqueDiffWithinAt ℝ (parameterRegion second) q := by
  have h := uniqueDiffOn_Ici (0 : ℝ) q.2 hq.2
  cases second
  · exact ((uniqueDiffOn_Icc (by norm_num : (0 : ℝ) < 9/20)) q.1 hq.1).prod h
  · exact ((uniqueDiffOn_Ico (9/20 : ℝ) (1/2)) q.1 hq.1).prod h

private theorem contDiffAt_stripExtension {second : Bool} {x w : ℝ} (hd : domain second x w) :
    let b : ℝ × ℝ := (x,w+x^2-1)
    ContDiffAt ℝ 1 (fun q : ℝ × ℝ => stripBase second q.1 (parameterSquare q)) b := by
  let b : ℝ × ℝ := (x,w+x^2-1)
  let H (q : ℝ × ℝ) := trapezoidHeight second q.1
  have hb : parameterSquare b = w := by unfold parameterSquare b; dsimp only; ring
  have hH : ContDiffAt ℝ 1 H b := by
    cases second
    · change ContDiffAt ℝ 1 (fun q : ℝ × ℝ => 33/(20+26*q.1)) b
      refine contDiffAt_const.div (by fun_prop) ?_
      have hx := (domain_bounds hd).1
      change 20+26*x ≠ 0
      linarith
    · change ContDiffAt ℝ 1 (fun q : ℝ × ℝ => 1+(3/2)*(1-2*q.1)^2) b
      fun_prop
  have hW : ContDiffAt ℝ 1 parameterSquare b := by unfold parameterSquare; fun_prop
  have hy := (Real.contDiffAt_sqrt (n := 1) ((domain_bounds hd).2.2.ne' : w ≠ 0))
  rw [← hb] at hy
  have hY := hy.comp b hW
  let c : ℝ := if second then 2/3 else 1/3
  have hc : 1-c ≠ 0 := by cases second <;> norm_num [c]
  let P (q : ℝ × ℝ) (i : Vertex) := polynomialPoints q.1 (parameterSquare q) c (H q) 1 i
  have hP (i : Vertex) : ContDiffAt ℝ 1 (fun q => P q i) b := by
    fin_cases i <;> simp [P,polynomialPoints] <;> fun_prop
  apply contDiffAt_pi.mpr
  intro i
  have h₁ := (Complex.ofRealCLM.contDiff.contDiffAt.comp b (hP i).fst)
  have h₂ := (Complex.ofRealCLM.contDiff.contDiffAt.comp b (hY.mul (hP i).snd))
  convert h₁.add (h₂.mul (contDiffAt_const (c := Complex.I))) using 1
  funext q
  apply Complex.ext <;>
    simp [stripBase,stripPoints,Type7.physicalComplex,P,H,c,Function.comp_apply,
      Complex.ofRealCLM_apply,Complex.mul_re,Complex.mul_im,Complex.add_re,Complex.add_im]

private def stripAngleShape (z : Vertex → ℂ) : (Fin 7 → ℝ) × ℂ :=
  (sevenConeAngles Type7.flippedFaces z,flippedMarkedShape (planarEdgeSq z))

private theorem contDiffAt_stripAngleShape {second : Bool} {x w : ℝ} (hd : domain second x w) :
    ContDiffAt ℝ 1 stripAngleShape (stripBase second x w) := by
  let z := stripBase second x w
  have hcd := contDiffAt_coneAngles (n := 1) Type7.flippedFaces z (strip_flipped_corners_nondegenerate hd)
  have hflat : ContDiffAt ℝ 1 (sevenConeAngles Type7.flippedFaces : (Vertex → ℂ) → Fin 7 → ℝ) z :=
    contDiffAt_pi.mpr (fun i => (contDiffAt_pi.mp hcd) i.succ)
  have hU : (flippedMarkingDisplacements (planarEdgeSq z)).1 ≠ 0 := by
    intro hu
    have hm := trapezoid_flippedMarkedShape hd
    change flippedMarkedShape (planarEdgeSq z) = ⟨x,Real.sqrt w⟩ at hm
    rw [flippedMarkedShape,hu,div_zero] at hm
    exact (Real.sqrt_pos.mpr (domain_bounds hd).2.2).ne' (congrArg Complex.im hm).symm
  have hs (a b : Vertex) : ContDiffAt ℝ 1 (fun q => planarEdgeSq q a b) z := by
    have hdif : ContDiffAt ℝ 1 (fun q : Vertex → ℂ => q b-q a) z := by fun_prop
    have hre := Complex.reCLM.contDiff.contDiffAt.comp z hdif
    have him := Complex.imCLM.contDiff.contDiffAt.comp z hdif
    simpa only [planarEdgeSq,Complex.normSq_apply,Function.comp_apply,Complex.reCLM_apply,Complex.imCLM_apply]
      using (hre.mul hre).add (him.mul him)
  exact hflat.prodMk (contDiffAt_flippedMarkedShape hs rfl (strip_markingChartValid hd) hU)

set_option maxHeartbeats 600000 in
/-- The seven independent cone angles and two real marking coordinates have
surjective horizontal differential at every point in either chart. -/
theorem strip_flippedAngleShape_derivative_surjective {second : Bool} {x w : ℝ}
    (hd : domain second x w) :
    Function.Surjective (fderiv ℝ (fun p : Vertex → ℂ =>
      (sevenConeAngles Type7.flippedFaces p,flippedMarkedShape (planarEdgeSq p))) (stripBase second x w)) := by
  let z := stripBase second x w
  let b : ℝ × ℝ := (x,w+x^2-1)
  let E (q : ℝ × ℝ) := stripBase second q.1 (parameterSquare q)
  let T := fderiv ℝ E b
  let L := fderiv ℝ stripAngleShape z
  change Function.Surjective L
  have hw := (domain_bounds hd).2.2
  have hb : parameterSquare b = w := by unfold parameterSquare b; dsimp only; ring
  have hz : E b = z := by simp [E,b,z,hb]
  have hL : HasFDerivAt stripAngleShape L z :=
    ((contDiffAt_stripAngleShape hd).differentiableAt (by norm_num)).hasFDerivAt
  have hT : HasFDerivAt E T b :=
    ((contDiffAt_stripExtension hd).differentiableAt (by norm_num)).hasFDerivAt
  have hcomp : HasFDerivAt (stripAngleShape ∘ E) (L.comp T) b :=
    HasFDerivAt.comp b (hz ▸ hL) hT
  let S := parameterRegion second
  have hbS : b ∈ S := (mem_parameterRegion_iff _ _).mpr (by simpa only [hb] using hd)
  have hu := uniqueDiffWithinAt_parameterRegion hbS
  let X : (ℝ × ℝ) →L[ℝ] ℝ := ContinuousLinearMap.fst ℝ _ _
  let Y : (ℝ × ℝ) →L[ℝ] ℝ := ContinuousLinearMap.snd ℝ _ _
  let W : (ℝ × ℝ) →L[ℝ] ℝ := (-(2*x)) • X+Y
  let D : (ℝ × ℝ) →L[ℝ] ℝ := (1/(2*Real.sqrt w)) • W
  let J := X.prod D
  let M := (0 : (ℝ × ℝ) →L[ℝ] Fin 7 → ℝ).prod (Complex.equivRealProdCLM.symm.toContinuousLinearMap.comp J)
  let F (q : ℝ × ℝ) : (Fin 7 → ℝ) × ℂ := (fun _ => 2*Real.pi,⟨q.1,Real.sqrt (parameterSquare q)⟩)
  have hW : HasFDerivAt parameterSquare W b := by
    convert ((X.hasFDerivAt.pow 2).const_sub (1 : ℝ)).add Y.hasFDerivAt using 1
    · rfl
    · simp only [W,b,X,ContinuousLinearMap.coe_fst',pow_one,show (2 : ℕ)-1 = 1 by decide,nsmul_eq_mul,Nat.cast_ofNat]
      exact congrArg (· + Y) (neg_smul (2*x) X)
  have hD : HasFDerivAt (fun q => Real.sqrt (parameterSquare q)) D b := by
    simpa only [hb,D,Function.comp_def] using ((Real.hasDerivAt_sqrt (hb ▸ hw.ne')).comp_hasFDerivAt b hW)
  have hF : HasFDerivAt F M b := by
    exact hasFDerivAt_const _ _ |>.prodMk
      (Complex.equivRealProdCLM.symm.toContinuousLinearMap.hasFDerivAt.comp b (X.hasFDerivAt.prodMk hD))
  have hnear : stripAngleShape ∘ E =ᶠ[𝓝[S] b] F := by
    filter_upwards [self_mem_nhdsWithin (s := S)] with q hq
    have hdq := (mem_parameterRegion_iff second q).mp hq
    apply Prod.ext
    · funext i
      change coneAngles Type7.flippedFaces (E q) i.succ = 2*Real.pi
      rw [coneAngles_eq_chart_list]
      exact flipped_euclidean_cone_angle hdq i.succ
    · exact trapezoid_flippedMarkedShape hdq
  have hLT : L.comp T = M :=
    (hcomp.hasFDerivWithinAt.fderivWithin hu).symm.trans
      ((hF.hasFDerivWithinAt.congr_of_eventuallyEq hnear (hnear.eq_of_nhdsWithin hbS)).fderivWithin hu)
  let P : ((Fin 7 → ℝ) × ℂ) →L[ℝ] (Fin 7 → ℝ) := ContinuousLinearMap.fst ℝ _ _
  have hP : P.comp L = fderiv ℝ (sevenConeAngles Type7.flippedFaces : (Vertex → ℂ) → Fin 7 → ℝ) z :=
    (P.hasFDerivAt.comp z hL).fderiv.symm
  have hseven : Function.Surjective (P.comp L) := by
    rw [hP]
    obtain ⟨h356,h352,h623,h625⟩ := poly_chart_flipSigns hd
    have he := sevenConeAngles_flip_eventuallyEq (stripPoints second x w) w hw h356 h352 h623 h625
    change Function.Surjective (fderiv ℝ (sevenConeAngles Type7.flippedFaces)
      (Type7.physicalComplex w ∘ stripPoints second x w))
    rw [he.fderiv_eq]
    exact trapezoid_seven_cone_derivative_surjective hd
  intro u
  obtain ⟨δ,hδ⟩ := hseven u.1
  change (L δ).1 = u.1 at hδ
  let v := u.2-(L δ).2
  let q : ℝ × ℝ := (v.re,2*Real.sqrt w*v.im+2*x*v.re)
  have hJ : J q = (v.re,v.im) := by
    apply Prod.ext
    · rfl
    · simp only [J,D,W,X,Y,q,ContinuousLinearMap.prod_apply,add_apply,
        smul_apply,ContinuousLinearMap.coe_fst',ContinuousLinearMap.coe_snd',smul_eq_mul]
      field_simp [(Real.sqrt_pos.mpr hw).ne'] <;> ring
  have hv : L (T q) = (0,v) := by
    have h := congrArg (fun C : (ℝ × ℝ) →L[ℝ] ((Fin 7 → ℝ) × ℂ) => C q) hLT
    change L (T q) = (0,Complex.equivRealProdCLM.symm (J q)) at h
    rw [hJ] at h
    exact h
  refine ⟨δ+T q,?_⟩
  rw [map_add,hv]
  apply Prod.ext
  · simpa only [Prod.fst_add,add_zero] using hδ
  · simp [v]

/-- Before the flip, the same planar chart has rank nine for the Type 7
cone angles and marked shape. -/
theorem strip_angleShape_derivative_surjective {second : Bool} {x w : ℝ}
    (hd : domain second x w) :
    Function.Surjective (fderiv ℝ (fun p : Vertex → ℂ =>
      (sevenConeAngles Type7.faces p,Type7.markedShape (planarEdgeSq p))) (stripBase second x w)) := by
  obtain ⟨h356,h352,h623,h625⟩ := poly_chart_flipSigns hd
  have ha := sevenConeAngles_flip_eventuallyEq (stripPoints second x w) w
    (domain_bounds hd).2.2 h356 h352 h623 h625
  have hm := planarMarkedShape_flip_eventuallyEq _ (strip_markingChartValid hd)
  have hp : (fun p : Vertex → ℂ => (sevenConeAngles Type7.flippedFaces p,flippedMarkedShape (planarEdgeSq p)))
      =ᶠ[𝓝 (stripBase second x w)]
        (fun p => (sevenConeAngles Type7.faces p,Type7.markedShape (planarEdgeSq p))) := by
    change _ =ᶠ[𝓝 (Type7.physicalComplex w ∘ stripPoints second x w)] _ at hm ⊢
    filter_upwards [ha,hm] with p hp hmp
    exact Prod.ext hp hmp
  rw [← hp.fderiv_eq]
  exact strip_flippedAngleShape_derivative_surjective hd

end OrigamiTorus.Type4
