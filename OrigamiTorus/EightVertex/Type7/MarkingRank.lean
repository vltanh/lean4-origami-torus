module

public import OrigamiTorus.Lattice.MarkedShape
public import OrigamiTorus.EightVertex.Type7.Rank
import Mathlib.Analysis.Calculus.TangentCone.Prod
import Mathlib.Tactic

/-! The two one-sided chart velocities supplement the seven cone-angle directions. -/

@[expose] public section

open Filter Set
open scoped Topology

namespace OrigamiTorus.Type7

private noncomputable abbrev rectangleScale : ℝ := (13/20)^2

private noncomputable def rectangleExtension (q : ℝ × ℝ) (i : Vertex) : ℂ :=
  let p := Type4.polynomialPoints q.1 (q.2^2) (1/3) (Type4.trapezoidHeight false q.1) 1 i
  ⟨(p.1)/rectangleScale, (q.2*p.2)/rectangleScale⟩

private theorem rectangleExtension_eq (q : ℝ × ℝ) (hy : 0 ≤ q.2) :
    rectangleExtension q = fun i =>
      rectangleScale⁻¹ • physicalComplex (q.2^2)
        (Type4.polynomialPoints q.1 (q.2^2) (1/3) (Type4.trapezoidHeight false q.1) 1 i) := by
  funext i
  apply Complex.ext <;>
    simp only [rectangleExtension,physicalComplex,Real.sqrt_sq hy,Complex.real_smul,Complex.mul_re,
      Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,zero_add,div_eq_mul_inv] <;>
    ring

private theorem rectangleExtension_at_base (w : ℝ) (hw : 1 ≤ w) :
    rectangleExtension (0, Real.sqrt w) = physicalComplex w ∘ rectangularPoint w := by
  rw [rectangleExtension_eq _ (Real.sqrt_nonneg w)]
  funext i
  dsimp only [Prod.fst,Prod.snd,Function.comp_apply]
  rw [Real.sq_sqrt (by linarith),trapezoid_at_rectangle]
  have he (a : ℝ × ℝ) : physicalComplex w (rectangleScale • a) = rectangleScale • physicalComplex w a := by
    rw [show rectangleScale • a = (rectangleScale*a.1,rectangleScale*a.2) from rfl]
    apply Complex.ext <;> simp only [physicalComplex,Complex.real_smul,Complex.mul_re,Complex.mul_im,
      Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,zero_add] <;> ring
  rw [he,smul_smul,inv_mul_cancel₀ (by norm_num : rectangleScale ≠ 0),one_smul]

private theorem contDiffAt_rectangleExtension (y : ℝ) :
    ContDiffAt ℝ 1 rectangleExtension (0,y) := by
  let H (q : ℝ × ℝ) := Type4.trapezoidHeight false q.1
  have hH : ContDiffAt ℝ 1 H (0,y) := by
    change ContDiffAt ℝ 1 (fun q : ℝ × ℝ => 33/(20+26*q.1)) (0,y)
    exact contDiffAt_const.div (by fun_prop) (by norm_num)
  let P (q : ℝ × ℝ) (i : Vertex) := Type4.polynomialPoints q.1 (q.2^2) (1/3) (H q) 1 i
  have hP (i : Vertex) : ContDiffAt ℝ 1 (fun q => P q i) (0,y) := by
    fin_cases i <;> simp [P,Type4.polynomialPoints] <;> fun_prop
  apply contDiffAt_pi.mpr
  intro i
  have h₁ : ContDiffAt ℝ 1 (fun q => (P q i).1/rectangleScale) (0,y) :=
    ((hP i).fst).div_const _
  have h₂ : ContDiffAt ℝ 1 (fun q : ℝ × ℝ => q.2*(P q i).2/rectangleScale) (0,y) :=
    ((contDiffAt_snd.mul (hP i).snd)).div_const _
  have h := (Complex.ofRealCLM.contDiff.contDiffAt.comp (0,y) h₁).add
    ((Complex.ofRealCLM.contDiff.contDiffAt.comp (0,y) h₂).mul (contDiffAt_const (c := Complex.I)))
  convert h using 1
  funext q
  apply Complex.ext <;>
    simp only [rectangleExtension,P,H,Function.comp_apply,Complex.ofRealCLM_apply,Complex.add_re,
      Complex.add_im,Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
      Complex.I_re,Complex.I_im,zero_mul,mul_zero,mul_one,sub_zero,zero_add,add_zero]

private noncomputable def angleShape (p : Vertex → ℂ) : (Fin 7 → ℝ) × ℂ :=
  (sevenConeAngles faces p,markedShape (planarEdgeSq p))

private theorem angleShape_rectangleExtension (q : ℝ × ℝ) (hy : 0 ≤ q.2)
    (hd : Type4.domain false q.1 (q.2^2)) :
    angleShape (rectangleExtension q) = (fun _ => 2*Real.pi, ⟨q.1,q.2⟩) := by
  let p := physicalComplex (q.2^2) ∘
    Type4.polynomialPoints q.1 (q.2^2) (1/3) (Type4.trapezoidHeight false q.1) 1
  rw [rectangleExtension_eq q hy]
  have hfaces : orientedFaces.map Prod.fst = faces := by decide +kernel
  have hc : rectangleScale⁻¹ ≠ 0 := by norm_num
  apply Prod.ext
  · funext i
    change coneAngles faces (fun j => rectangleScale⁻¹ • p j) i.succ = _
    rw [coneAngles_smul faces p hc,← hfaces,coneAngles_eq_chart]
    exact Type4.trapezoid_euclidean_cone_angle hd i.succ
  · change markedShape (planarEdgeSq (fun j => rectangleScale⁻¹ • p j)) = _
    rw [markedShape_planar_smul p hc]
    simpa only [p,Bool.false_eq_true,ite_false,Real.sqrt_sq hy] using Type4.trapezoid_markedShape hd

private theorem contDiffAt_angleShape (w : ℝ) (hw : 1 ≤ w) :
    ContDiffAt ℝ 1 angleShape (physicalComplex w ∘ rectangularPoint w) := by
  let z := physicalComplex w ∘ rectangularPoint w
  have hcd := contDiffAt_coneAngles (n := 1) faces z (rectangular_corners_nondegenerate w hw)
  have hflat : ContDiffAt ℝ 1 (sevenConeAngles faces : (Vertex → ℂ) → Fin 7 → ℝ) z :=
    contDiffAt_pi.mpr (fun i => (contDiffAt_pi.mp hcd) i.succ)
  let I := ContinuousLinearMap.inr ℝ ℝ (Vertex → ℂ)
  have hs := (contDiffAt_rectangular_spatial_markedShape w hw (fun _ => 0)).comp z I.contDiff.contDiffAt
  have hm : ContDiffAt ℝ 1 (fun a : Vertex → ℂ => markedShape (planarEdgeSq a)) z := by
    convert hs using 1
    funext a
    congr 1
    exact (spatialEdgeSq_angleLift_zero a (fun _ => 0)).symm
  exact hflat.prodMk hm

/-- At a rectangular base, the combined derivative onto seven cone angles and
the complex marked shape is surjective. The derivative of the trapezoid family
is computed within the quadrant of admissible parameters at the boundary. -/
theorem rectangular_angleShape_derivative_surjective (w : ℝ) (hw : 1 ≤ w) :
    let z := physicalComplex w ∘ rectangularPoint w
    Function.Surjective (fderiv ℝ (fun p : Vertex → ℂ =>
      (sevenConeAngles faces p,markedShape (planarEdgeSq p))) z) := by
  let z := physicalComplex w ∘ rectangularPoint w
  let y := Real.sqrt w
  let base : ℝ × ℝ := (0,y)
  let L := fderiv ℝ angleShape z
  let D := fderiv ℝ rectangleExtension base
  change Function.Surjective L
  have hy : 1 ≤ y := by
    change 1 ≤ Real.sqrt w
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt hw
  have hbase : rectangleExtension base = z := rectangleExtension_at_base w hw
  have hL : HasFDerivAt angleShape L z :=
    ((contDiffAt_angleShape w hw).differentiableAt (by norm_num)).hasFDerivAt
  have hD : HasFDerivAt rectangleExtension D base :=
    ((contDiffAt_rectangleExtension y).differentiableAt (by norm_num)).hasFDerivAt
  have hcomb : HasFDerivAt (angleShape ∘ rectangleExtension) (L.comp D) base := by
    apply HasFDerivAt.comp base _ hD
    rwa [hbase]
  let S : Set (ℝ × ℝ) := Ici 0 ×ˢ Ici y
  have hUnique : UniqueDiffWithinAt ℝ S base :=
    (uniqueDiffWithinAt_Ici 0).prod (uniqueDiffWithinAt_Ici y)
  have hb : base ∈ S := ⟨le_rfl,le_rfl⟩
  let E := Complex.equivRealProdCLM
  let M : (ℝ × ℝ) →L[ℝ] ((Fin 7 → ℝ) × ℂ) :=
    (0 : (ℝ × ℝ) →L[ℝ] Fin 7 → ℝ).prod E.symm.toContinuousLinearMap
  let F (q : ℝ × ℝ) := ((fun _ : Fin 7 => 2*Real.pi),0) + M q
  have hF : HasFDerivAt F M base := M.hasFDerivAt.const_add _
  have hnear : angleShape ∘ rectangleExtension =ᶠ[𝓝[S] base] F := by
    have hsmall : ∀ᶠ q : ℝ × ℝ in 𝓝 base, q.1 < 9/20 :=
      continuous_fst.continuousAt.eventually_lt continuousAt_const (by norm_num [base])
    filter_upwards [self_mem_nhdsWithin (s := S),hsmall.filter_mono nhdsWithin_le_nhds] with q hq hsmall
    have hq₁ : 0 ≤ q.1 := hq.1
    have hq₂ : 1 ≤ q.2 := hy.trans hq.2
    have hsq : 1 ≤ q.2^2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hq₂) (by linarith : 0 ≤ q.2+1)]
    have hd : Type4.domain false q.1 (q.2^2) :=
      ⟨hq₁,hsmall.le,(sub_le_self _ (sq_nonneg _)).trans hsq⟩
    change angleShape (rectangleExtension q) = F q
    rw [angleShape_rectangleExtension q (by linarith) hd]
    simp only [F,M,ContinuousLinearMap.prod_apply,zero_apply,
      Prod.mk_add_mk,add_zero,zero_add]
    congr 1
  have he : L.comp D = M :=
    (hcomb.hasFDerivWithinAt.fderivWithin hUnique).symm.trans
      ((hF.hasFDerivWithinAt.congr_of_eventuallyEq hnear (hnear.eq_of_nhdsWithin hb)).fderivWithin hUnique)
  let P : ((Fin 7 → ℝ) × ℂ) →L[ℝ] (Fin 7 → ℝ) := ContinuousLinearMap.fst ℝ _ _
  have hP : P.comp L = fderiv ℝ (sevenConeAngles faces : (Vertex → ℂ) → Fin 7 → ℝ) z :=
    (P.hasFDerivAt.comp z hL).fderiv.symm
  intro u
  obtain ⟨δ,hδ⟩ := rectangular_seven_cone_derivative_surjective w hw u.1
  rw [← hP] at hδ
  change (L δ).1 = u.1 at hδ
  let v := E (u.2-(L δ).2)
  have hv : L (D v) = (0,u.2-(L δ).2) := by
    have hv' := congrArg (fun (A : (ℝ × ℝ) →L[ℝ] (Fin 7 → ℝ) × ℂ) => A v) he
    change L (D v) = (0,E.symm v) at hv'
    simpa only [v,ContinuousLinearEquiv.symm_apply_apply] using hv'
  refine ⟨δ+D v,?_⟩
  rw [map_add,hv]
  apply Prod.ext
  · simpa only [Prod.fst_add,add_zero] using hδ
  · simp

end OrigamiTorus.Type7
