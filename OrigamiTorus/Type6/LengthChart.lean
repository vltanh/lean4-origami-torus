module

public import OrigamiTorus.Type6.MetricAngles
public import OrigamiTorus.Type6.FaceMetric
import Mathlib.Tactic

/-! The two marked period coordinates and seven cone angles have independent
differentials in the twenty-four Type 6 squared edge lengths. -/

@[expose] public section

noncomputable section

open Filter
open scoped Topology

namespace OrigamiTorus

/-- Index the table by an unordered edge, leaving nonedges undefined. -/
def type6EdgeSlot (a b : Vertex) : Option EdgeIndex :=
  (List.finRange 24).find? fun e =>
    ((edgePeriod e).1 == (a,b)) || ((edgePeriod e).1 == (b,a))

private theorem type6EdgeSlot_on_table (e : EdgeIndex) :
    type6EdgeSlot (edgePeriod e).1.1 (edgePeriod e).1.2 = some e := by
  revert e
  decide +kernel

private theorem type6EdgeSlot_symm (a b : Vertex) : type6EdgeSlot a b = type6EdgeSlot b a := by
  revert a b
  decide +kernel

theorem type6EdgeSlot_endpoints (a b : Vertex) (e : EdgeIndex)
    (h : type6EdgeSlot a b = some e) :
    (edgePeriod e).1 = (a,b) ∨ (edgePeriod e).1 = (b,a) := by
  revert a b e
  decide +kernel

/-- Insert the twenty-four edge lengths as symmetric pair data. -/
def type6LengthMetric : (EdgeIndex → ℝ) →L[ℝ] (Vertex → Vertex → ℝ) :=
  (show (EdgeIndex → ℝ) →ₗ[ℝ] (Vertex → Vertex → ℝ) from
    { toFun := fun l a b => ((type6EdgeSlot a b).map l).getD 0
      map_add' := by
        intro l k
        funext a b
        change ((type6EdgeSlot a b).map (l+k)).getD 0 =
          ((type6EdgeSlot a b).map l).getD 0 + ((type6EdgeSlot a b).map k).getD 0
        cases type6EdgeSlot a b <;> simp
      map_smul' := by
        intro r l
        funext a b
        change ((type6EdgeSlot a b).map (r • l)).getD 0 =
          r * ((type6EdgeSlot a b).map l).getD 0
        cases type6EdgeSlot a b <;> simp }).toContinuousLinearMap

theorem type6LengthMetric_apply (l : EdgeIndex → ℝ) (a b : Vertex) :
    type6LengthMetric l a b = ((type6EdgeSlot a b).map l).getD 0 := rfl

theorem type6LengthMetric_symm (l : EdgeIndex → ℝ) (a b : Vertex) :
    type6LengthMetric l a b = type6LengthMetric l b a := by
  simp only [type6LengthMetric_apply,type6EdgeSlot_symm a b]

/-- Squared lengths of the lifted edges of the periodic intrinsic chart. -/
def type6IntrinsicLengths (p : Vertex → ℂ) (U V : ℂ) (e : EdgeIndex) : ℝ :=
  let ((a,b),d) := edgePeriod e
  Complex.normSq (type6ComplexCorner p U V (b,d)-p a)

private theorem type6ComplexCorner_diff (p : Vertex → ℂ) (U V : ℂ) (a b : Corner) :
    type6ComplexCorner p U V b-type6ComplexCorner p U V a =
      type6ComplexCorner p U V (b.1,b.2-a.2)-p a.1 := by
  simp only [type6ComplexCorner,Prod.fst_sub,Prod.snd_sub,Int.cast_sub]
  ring

private theorem type6IntrinsicLengths_on_side (p : Vertex → ℂ) (U V : ℂ)
    (j : Fin 16) (a b : Corner) (h : liftedSide a b ∈ liftedSides (liftedFaces j)) :
    type6LengthMetric (type6IntrinsicLengths p U V) a.1 b.1 =
      Complex.normSq (type6ComplexCorner p U V b-type6ComplexCorner p U V a) := by
  have he (a b : Corner) (e : EdgeIndex) (h : liftedSide a b = indexedSide e) :
      type6LengthMetric (type6IntrinsicLengths p U V) a.1 b.1 =
        Complex.normSq (type6ComplexCorner p U V b-type6ComplexCorner p U V a) := by
    have h₁ : a.1 = (edgePeriod e).1.1 := congrArg Prod.fst h
    have h₂ : b.1 = (edgePeriod e).1.2 := congrArg (fun k : LiftedSide => k.2.1) h
    have h₃ : b.2-a.2 = (edgePeriod e).2 := congrArg (fun k : LiftedSide => k.2.2) h
    rw [type6ComplexCorner_diff,h₃,h₁,h₂,type6LengthMetric_apply,type6EdgeSlot_on_table]
    rfl
  obtain ⟨e,g | g⟩ := oriented_side_index j _ h
  · exact he a b e g
  · have hg : reverseSide (liftedSide a b) = liftedSide b a := by
      simp [reverseSide,liftedSide,neg_sub]
    rw [type6LengthMetric_symm _ a.1 b.1,normSq_sub_rev]
    exact he b a e (hg.symm.trans g)

/-- Positivity of the intrinsic faces identifies their metric with the
twenty-four edge lengths read at the prescribed periods. -/
theorem type6IntrinsicLengths_matches (p : Vertex → ℂ) (U V : ℂ)
    (h : ∀ j : Fin 16,
      let f := liftedFaces j
      let P := type6ComplexCorner p U V
      0 < complexCross (P f.2.1-P f.1) (P f.2.2-P f.1)) :
    ∀ j : Fin 16,
      OrientedMetricLift (type6LengthMetric (type6IntrinsicLengths p U V))
        (type6ComplexCorner p U V) (liftedFaces j) := by
  intro j
  let f := liftedFaces j
  change OrientedMetricLift _ _ (f.1,f.2.1,f.2.2)
  exact ⟨type6IntrinsicLengths_on_side p U V j f.1 f.2.1 (by simp [f,liftedSides]),
    by rw [type6LengthMetric_symm _ f.1.1 f.2.2.1,normSq_sub_rev]
       exact type6IntrinsicLengths_on_side p U V j f.2.2 f.1 (by simp [f,liftedSides]),
    type6IntrinsicLengths_on_side p U V j f.2.1 f.2.2 (by simp [f,liftedSides]), h j⟩

/-- The angle and marked shape map on the twenty-four squared edge lengths. -/
def type6AnglesAndShape (l : EdgeIndex → ℝ) : (Fin 7 → ℝ) × ℂ :=
  (metricSevenConeAngles type6FlippedFaces (type6LengthMetric l), type6MetricShape (type6LengthMetric l))

private theorem type6MetricFace_of_periodic (s : Vertex → Vertex → ℝ)
    (p : Vertex → ℂ) (U V : ℂ)
    (h : ∀ j : Fin 16, OrientedMetricLift s (type6ComplexCorner p U V) (liftedFaces j)) :
    ∀ f ∈ type6FlippedFaces, MetricFaceNondegenerate s f := by
  intro f hf
  have he : type6FlippedFaces = (List.finRange 16).map (fun j => liftedVertices (liftedFaces j)) := by
    decide +kernel
  rw [he] at hf
  obtain ⟨j,_,rfl⟩ := List.mem_map.mp hf
  exact (h j).nondegenerate

theorem type6AnglesAndShape_on_sheet (p : Vertex → ℂ) (U V : ℂ)
    (h : ∀ j : Fin 16,
      let f := liftedFaces j
      let P := type6ComplexCorner p U V
      0 < complexCross (P f.2.1-P f.1) (P f.2.2-P f.1)) :
    type6AnglesAndShape (type6IntrinsicLengths p U V) = (fun _ => 2*Real.pi,V/U) := by
  let l := type6IntrinsicLengths p U V
  have hm := type6IntrinsicLengths_matches p U V h
  apply Prod.ext
  · funext i
    exact type6_metricConeAngles_flat (type6LengthMetric_symm l) p U V hm i.succ
  · exact type6MetricShape_of_periodic _ (type6LengthMetric_symm l) p U V hm

private theorem type6Metric_connected (u : Vertex → ℝ)
    (h : ∀ f ∈ type6FlippedFaces, u f.1 = u f.2.1 ∧ u f.1 = u f.2.2) :
    ∀ v, u v = u 0 := by
  have h013 : (0,3,1) ∈ type6FlippedFaces := by decide +kernel
  have h024 : (0,2,4) ∈ type6FlippedFaces := by decide +kernel
  have h015 : (0,1,5) ∈ type6FlippedFaces := by decide +kernel
  have h136 : (1,3,6) ∈ type6FlippedFaces := by decide +kernel
  have h167 : (1,6,7) ∈ type6FlippedFaces := by decide +kernel
  have h1 : u 0 = u 1 := (h _ h013).2
  intro v
  fin_cases v
  · rfl
  · exact h1.symm
  · exact (h _ h024).1.symm
  · exact (h _ h013).1.symm
  · exact (h _ h024).2.symm
  · exact (h _ h015).2.symm
  · exact (h _ h136).2.symm.trans h1.symm
  · exact (h _ h167).2.symm.trans h1.symm

private theorem type6LengthMetric_conformal (l : EdgeIndex → ℝ) (u : Vertex → ℝ) :
    type6LengthMetric (fun e => (u (edgePeriod e).1.1+u (edgePeriod e).1.2)*l e) =
      conformalEdgeVariation (type6LengthMetric l) u := by
  funext a b
  simp only [type6LengthMetric_apply,conformalEdgeVariation]
  cases h : type6EdgeSlot a b with
  | none => simp
  | some e =>
    obtain he | he := type6EdgeSlot_endpoints a b e h
    · simp [he]
    · simp [he,add_comm]

theorem contDiffAt_type6AnglesAndShape_on_sheet (p : Vertex → ℂ) (U V : ℂ) (hU : U ≠ 0)
    (h : ∀ j : Fin 16,
      let f := liftedFaces j
      let P := type6ComplexCorner p U V
      0 < complexCross (P f.2.1-P f.1) (P f.2.2-P f.1)) :
    ContDiffAt ℝ 1 type6AnglesAndShape (type6IntrinsicLengths p U V) := by
  let l := type6IntrinsicLengths p U V
  have hm := type6IntrinsicLengths_matches p U V h
  let M := type6LengthMetric
  have hc : ContDiffAt ℝ 1 (metricSevenConeAngles type6FlippedFaces) (M l) :=
    contDiffAt_metricSevenConeAngles _ _ (type6LengthMetric_symm l) (type6MetricFace_of_periodic _ p U V hm)
  have hs : ContDiffAt ℝ 1 (type6MetricShape ∘ M) l :=
    contDiffAt_type6MetricShape_of_periodic (fun a b => by fun_prop)
      (type6LengthMetric_symm l) p U V hU hm
  exact (hc.comp l M.contDiff.contDiffAt).prodMk hs

private theorem type6_angleProjection_surjective (p : Vertex → ℂ) (U V : ℂ)
    (h : ∀ j : Fin 16,
      let f := liftedFaces j
      let P := type6ComplexCorner p U V
      0 < complexCross (P f.2.1-P f.1) (P f.2.2-P f.1)) :
    Function.Surjective (fderiv ℝ (fun l => (type6AnglesAndShape l).1) (type6IntrinsicLengths p U V)) := by
  let l := type6IntrinsicLengths p U V
  let s := type6LengthMetric l
  have hm := type6IntrinsicLengths_matches p U V h
  have hf := type6MetricFace_of_periodic s p U V hm
  have hs : ∀ a b, s a b = s b a := type6LengthMetric_symm l
  have hn : ∀ f ∈ type6FlippedFaces, (triangleVertices f).Nodup := by decide +kernel
  have hD := ((contDiffAt_metricSevenConeAngles type6FlippedFaces s hs hf).differentiableAt
    (by decide)).hasFDerivAt
  have hM := (hD.comp l type6LengthMetric.hasFDerivAt).fderiv
  change Function.Surjective (fderiv ℝ (metricSevenConeAngles type6FlippedFaces ∘ type6LengthMetric) l)
  rw [hM]
  intro r
  obtain ⟨u,hu⟩ := metricSevenConeAngles_conformal_surjective _ s hs hn hf type6Metric_connected r
  let w : Vertex → ℝ := Fin.cases 0 u
  refine ⟨fun e => (w (edgePeriod e).1.1+w (edgePeriod e).1.2)*l e,?_⟩
  rw [ContinuousLinearMap.comp_apply,type6LengthMetric_conformal]
  exact hu

/-- At a positively oriented sheet, varying the second period supplies the
two remaining directions in the joint angle and modulus differential. -/
theorem type6AnglesAndShape_derivative_surjective (p : Vertex → ℂ) (V : ℂ)
    (h : ∀ j : Fin 16,
      let f := liftedFaces j
      let P := type6ComplexCorner p 1 V
      0 < complexCross (P f.2.1-P f.1) (P f.2.2-P f.1)) :
    Function.Surjective (fderiv ℝ type6AnglesAndShape (type6IntrinsicLengths p 1 V)) := by
  let l := type6IntrinsicLengths p 1 V
  let D := fderiv ℝ type6AnglesAndShape l
  let I (v : ℂ) := type6IntrinsicLengths p 1 v
  have hD : HasFDerivAt type6AnglesAndShape D l :=
    ((contDiffAt_type6AnglesAndShape_on_sheet p 1 V one_ne_zero h).differentiableAt (by decide)).hasFDerivAt
  have hCI : ContDiff ℝ 1 I := by
    apply contDiff_pi.mpr
    intro e
    simp only [I,type6IntrinsicLengths,type6ComplexCorner,Complex.normSq_apply,
      Complex.sub_re,Complex.sub_im,Complex.add_re,Complex.add_im,Complex.mul_re,Complex.mul_im]
    have hre : ContDiff ℝ 1 (fun v : ℂ => v.re) := Complex.reCLM.contDiff
    have him : ContDiff ℝ 1 (fun v : ℂ => v.im) := Complex.imCLM.contDiff
    fun_prop (disch := assumption)
  let T := fderiv ℝ I V
  have hT : HasFDerivAt I T V := (hCI.differentiable (by decide) V).hasFDerivAt
  have hcont (j : Fin 16) : Continuous (fun v : ℂ =>
      let f := liftedFaces j
      let P := type6ComplexCorner p 1 v
      complexCross (P f.2.1-P f.1) (P f.2.2-P f.1)) := by
    simp only [type6ComplexCorner,complexCross_apply,Complex.sub_re,Complex.sub_im,
      Complex.add_re,Complex.add_im,Complex.mul_re,Complex.mul_im]
    fun_prop
  have hn : ∀ᶠ v in 𝓝 V, ∀ j : Fin 16,
      let f := liftedFaces j
      let P := type6ComplexCorner p 1 v
      0 < complexCross (P f.2.1-P f.1) (P f.2.2-P f.1) := by
    rw [Filter.eventually_all]
    intro j
    exact continuousAt_const.eventually_lt (hcont j).continuousAt (h j)
  let J : ℂ →L[ℝ] (Fin 7 → ℝ) × ℂ := (0 : ℂ →L[ℝ] (Fin 7 → ℝ)).prod (ContinuousLinearMap.id ℝ ℂ)
  have hEq : type6AnglesAndShape ∘ I =ᶠ[𝓝 V] fun v => (fun _ => 2*Real.pi,v) := by
    filter_upwards [hn] with v hv
    simpa only [Function.comp_apply,I,div_one] using type6AnglesAndShape_on_sheet p 1 v hv
  have hj : HasFDerivAt (fun v : ℂ => (fun _ : Fin 7 => 2*Real.pi,v)) J V :=
    (hasFDerivAt_const _ _).prodMk (hasFDerivAt_id _)
  have hDT : D.comp T = J := (hD.comp V hT).unique (hj.congr_of_eventuallyEq hEq)
  let A : ((Fin 7 → ℝ) × ℂ) →L[ℝ] Fin 7 → ℝ := ContinuousLinearMap.fst ℝ _ _
  have hproj := (A.hasFDerivAt.comp l hD).fderiv
  have h0 : Function.Surjective (A.comp D) := by
    rw [← hproj]
    exact type6_angleProjection_surjective p 1 V h
  intro z
  obtain ⟨u,hu⟩ := h0 z.1
  let v := z.2-(D u).2
  have hV : D (T v) = (0,v) :=
    congrArg (fun g : ℂ →L[ℝ] (Fin 7 → ℝ) × ℂ => g v) hDT
  refine ⟨u+T v,?_⟩
  rw [map_add,hV]
  change (D u).1 = z.1 at hu
  exact Prod.ext (show (D u).1 + 0 = z.1 by rw [add_zero,hu])
    (show (D u).2 + (z.2-(D u).2) = z.2 by abel)

end OrigamiTorus
