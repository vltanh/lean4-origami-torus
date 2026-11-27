module

public import OrigamiTorus.EightVertex.Type6.LengthChart
public import OrigamiTorus.Lattice.FaceDevelopment
import Mathlib.Tactic

/-! Transport the Type 6 edge-metric differential through the exact
length-matching equations to the actual three-dimensional vertices. -/

@[expose] public section

noncomputable section

open Filter
open scoped Topology ContDiff

namespace OrigamiTorus

/-- Squared distances on the labeled Type 6 spatial edges. -/
def type6SpatialLengths (q : Vertex → Point3) (e : EdgeIndex) : ℝ :=
  Type7.spatialEdgeSq q (edgePeriod e).1.1 (edgePeriod e).1.2

def type6SpatialLengthData (q : Vertex → Point3) (a b : Vertex) : ℝ :=
  ((type6EdgeSlot a b).map (type6SpatialLengths q)).getD 0

/-- Seven Euclidean cone angles and the marked modulus of a spatial placement. -/
def type6SpatialAngleShape (q : Vertex → Point3) : (Fin 7 → ℝ) × ℂ :=
  (sevenConeAngles type6FlippedFaces (Type2.euclideanPoint ∘ q),
    type6MetricShape (type6SpatialLengthData q))

/-- The spatial angle and marked modulus map is locally smooth and has rank nine. -/
def Type6SpatiallyRegular (q : Vertex → Point3) : Prop :=
  ContDiffAt ℝ 1 type6SpatialAngleShape q ∧
    Function.Surjective (fderiv ℝ type6SpatialAngleShape q)

private theorem type6_corner_edge_slots :
    ∀ f ∈ type6FlippedFaces, ∀ v a b, cornerRays v f = some (a,b) →
      (type6EdgeSlot v a).isSome = true ∧ (type6EdgeSlot v b).isSome = true ∧
        (type6EdgeSlot a b).isSome = true := by
  decide +kernel

private theorem type6_spatial_edge (q : Vertex → Point3) (a b : Vertex)
    (h : (type6EdgeSlot a b).isSome = true) :
    type6LengthMetric (type6SpatialLengths q) a b = Type7.spatialEdgeSq q a b := by
  cases he : type6EdgeSlot a b with
  | none => simp [he] at h
  | some e =>
    rw [type6LengthMetric_apply,he]
    change Type7.spatialEdgeSq q (edgePeriod e).1.1 (edgePeriod e).1.2 = _
    obtain h | h := type6EdgeSlot_endpoints a b e he
    · rw [h]
    · rw [h,spatialEdgeSq_comm]

theorem type6SpatialAngleShape_eq_metric :
    type6SpatialAngleShape = type6AnglesAndShape ∘ type6SpatialLengths := by
  funext q
  apply Prod.ext
  · funext i
    change coneAngles type6FlippedFaces (Type2.euclideanPoint ∘ q) i.succ =
      metricConeAngles type6FlippedFaces (type6LengthMetric (type6SpatialLengths q)) i.succ
    symm
    apply metricConeAngles_eq_coneAngles_of_corner
    intro f hf a b hab
    obtain ⟨hva,hvb,hab'⟩ := type6_corner_edge_slots f hf i.succ a b hab
    exact ⟨(type6_spatial_edge q _ _ hva).trans (spatialEdgeSq_euclidean q _ _),
      (type6_spatial_edge q _ _ hvb).trans (spatialEdgeSq_euclidean q _ _),
      (type6_spatial_edge q _ _ hab').trans (spatialEdgeSq_euclidean q _ _)⟩
  · rfl

private theorem type6SpatialLengths_smooth : ContDiff ℝ 1 type6SpatialLengths := by
  apply contDiff_pi.mpr
  intro e
  unfold type6SpatialLengths Type7.spatialEdgeSq Type5.squared3 Type5.squared2 Type5.dot Type5.horizontal
  fun_prop

private def intrinsicComplex (second : Bool) (x y : ℝ) (m : SheetMotion) (a : Vertex) : ℂ :=
  let p := movedIntrinsicPoint second x (y^2) m a
  ⟨p.1,p.2/y⟩

private def intrinsicCross (second : Bool) (x y : ℝ) (m : SheetMotion) (j : Fin 16) : ℝ :=
  let f := liftedFaces j
  let P := type6ComplexCorner (intrinsicComplex second x y m) 1 ⟨x,y⟩
  complexCross (P f.2.1-P f.1) (P f.2.2-P f.1)

private theorem intrinsicCross_eq (second : Bool) (x y : ℝ) (hy : y ≠ 0)
    (m : SheetMotion) (j : Fin 16) :
    intrinsicCross second x y m j =
      periodicFaceArea x (y^2) (movedIntrinsicPoint second x (y^2) m) (liftedFaces j)/y := by
  simp only [intrinsicCross,type6ComplexCorner,Complex.intCast_re,Complex.intCast_im,Complex.add_re,
    Complex.add_im,Complex.mul_re,Complex.mul_im,Complex.sub_re,Complex.sub_im,Complex.one_re,
    Complex.one_im,intrinsicComplex,complexCross_apply,periodicFaceArea,translatePoint]
  field_simp [hy]
  ring

private theorem type6_residual_lengths (second : Bool) (x y : ℝ) (hy : y ≠ 0)
    (z : Vertex → ℝ) (t : ℝ) :
    (fun m => lengthResidual second x (y^2) z (t,m)) = fun m =>
      y^2 • (type6SpatialLengths (physicalFoldedVertex second x y m z t) -
        type6IntrinsicLengths (intrinsicComplex second x y m) 1 ⟨x,y⟩) := by
  funext m e
  simp only [Pi.smul_apply,Pi.sub_apply,smul_eq_mul,lengthResidual,type6SpatialLengths,
    Type7.spatialEdgeSq,physicalFoldedVertex,Type5.squared3,Type5.squared2,Type5.dot,Type5.horizontal,
    type6IntrinsicLengths,intrinsicComplex,type6ComplexCorner,Complex.normSq_apply,Complex.intCast_re,
    Complex.intCast_im,Complex.add_re,Complex.add_im,Complex.mul_re,Complex.mul_im,
    Complex.sub_re,Complex.sub_im,Complex.one_re,Complex.one_im,Prod.fst_sub,Prod.snd_sub,
    scaledSquaredDistance,translatePoint,Prod.fst_add,Prod.snd_add,movedFoldedPoint,movedIntrinsicPoint]
  field_simp [hy]
  ring

private theorem type6_folded_smooth (second : Bool) (x y : ℝ) (z : Vertex → ℝ) (t : ℝ) :
    ContDiff ℝ 1 (fun m => physicalFoldedVertex second x y m z t) := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i <;> simp [physicalFoldedVertex,movedFoldedPoint,FoldedMotion]
  all_goals fun_prop

private theorem type6_intrinsic_lengths_smooth (second : Bool) (x y : ℝ) :
    ContDiff ℝ 1 (fun m => type6IntrinsicLengths (intrinsicComplex second x y m) 1 ⟨x,y⟩) := by
  have hs (i : Vertex) : ContDiff ℝ 1 (fun m => movedIntrinsicPoint second x (y^2) m i) := by
    fin_cases i <;> simp [movedIntrinsicPoint,IntrinsicMotion] <;> fun_prop
  apply contDiff_pi.mpr
  intro e
  simp only [type6IntrinsicLengths,type6ComplexCorner,intrinsicComplex,Complex.normSq_apply,
    Complex.add_re,Complex.add_im,Complex.mul_re,Complex.mul_im,Complex.sub_re,Complex.sub_im]
  fun_prop (disch := assumption)

private theorem type6_residual_partial (second : Bool) (x y : ℝ)
    (z : Vertex → ℝ) (t : ℝ) (m : SheetMotion) :
    fderiv ℝ (fun v => lengthResidual second x (y^2) z (t,v)) m =
      (fderiv ℝ (lengthResidual second x (y^2) z) (t,m)).comp
        (ContinuousLinearMap.inr ℝ ℝ SheetMotion) := by
  let J := ContinuousLinearMap.inr ℝ ℝ SheetMotion
  have hJ : HasFDerivAt (fun v : SheetMotion => (t,v)) J m :=
    J.hasFDerivAt.const_add (t,0) |>.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun v => by simp [J])
  exact (((residual_smooth second x (y^2) z).differentiable (by decide) (t,m)).hasFDerivAt.comp
    m hJ).fderiv

/-- The length-matching solution has rank nine at its spatial vertices.
The fixed-period intrinsic derivative is killed by the joint angle and modulus map. -/
theorem type6_spatiallyRegular_of_lengthMatch (second : Bool) (x y : ℝ) (hy : 0 < y)
    (z : Vertex → ℝ) (t : ℝ) (m : SheetMotion)
    (hlen : lengthResidual second x (y^2) z (t,m) = 0)
    (hreg : ((fderiv ℝ (lengthResidual second x (y^2) z) (t,m)).comp
        (ContinuousLinearMap.inr ℝ ℝ SheetMotion)).IsInvertible)
    (hpos : ∀ j : Fin 16,
      0 < periodicFaceArea x (y^2) (movedIntrinsicPoint second x (y^2) m) (liftedFaces j)) :
    Type6SpatiallyRegular (physicalFoldedVertex second x y m z t) ∧
      type6SpatialAngleShape (physicalFoldedVertex second x y m z t) = (fun _ => 2*Real.pi,⟨x,y⟩) := by
  let W (v : SheetMotion) := physicalFoldedVertex second x y v z t
  let I (v : SheetMotion) := type6IntrinsicLengths (intrinsicComplex second x y v) 1 ⟨x,y⟩
  let E := type6SpatialLengths ∘ W
  let A := type6AnglesAndShape
  let R (v : SheetMotion) := lengthResidual second x (y^2) z (t,v)
  have hR : R = fun v => y^2 • (E v-I v) := type6_residual_lengths second x y hy.ne' z t
  have hEI : E m = I m := by
    have h0 : R m = 0 := hlen
    rw [hR] at h0
    exact sub_eq_zero.mp ((smul_eq_zero.mp h0).resolve_left (pow_ne_zero _ hy.ne'))
  have hn : ∀ᶠ v in 𝓝 m, ∀ j : Fin 16, 0 < intrinsicCross second x y v j := by
    rw [Filter.eventually_all]
    intro j
    filter_upwards [continuousAt_const.eventually_lt
      (periodicFaceArea_continuous second x (y^2) (liftedFaces j)).continuousAt (hpos j)] with v hv
    rw [intrinsicCross_eq second x y hy.ne']
    exact div_pos hv hy
  have hm : ∀ j : Fin 16, 0 < intrinsicCross second x y m j := hn.self_of_nhds
  have hA : ContDiffAt ℝ 1 A (I m) :=
    contDiffAt_type6AnglesAndShape_on_sheet _ _ _ one_ne_zero hm
  let D := fderiv ℝ A (I m)
  have hD : HasFDerivAt A D (I m) := (hA.differentiableAt (by decide)).hasFDerivAt
  have hDs : Function.Surjective D := type6AnglesAndShape_derivative_surjective _ _ hm
  have hW : ContDiff ℝ 1 W := type6_folded_smooth second x y z t
  have hE : ContDiff ℝ 1 E := type6SpatialLengths_smooth.comp hW
  have hI : ContDiff ℝ 1 I := type6_intrinsic_lengths_smooth second x y
  let dE := fderiv ℝ E m
  let dI := fderiv ℝ I m
  let dR := fderiv ℝ R m
  have he : HasFDerivAt E dE m := (hE.differentiable (by decide) m).hasFDerivAt
  have hi : HasFDerivAt I dI m := (hI.differentiable (by decide) m).hasFDerivAt
  have hr : dR = y^2 • (dE-dI) := by
    change fderiv ℝ R m = _
    rw [hR]
    exact ((he.sub hi).const_smul (y^2)).fderiv
  have hRs : Function.Surjective dR := by
    change Function.Surjective (fderiv ℝ (fun v => lengthResidual second x (y^2) z (t,v)) m)
    rw [type6_residual_partial]
    obtain ⟨L,hL⟩ := hreg
    rw [← hL]
    exact L.surjective
  have hconstant : A ∘ I =ᶠ[𝓝 m] fun _ => (fun _ : Fin 7 => 2*Real.pi, (⟨x,y⟩ : ℂ)) := by
    filter_upwards [hn] with v hv
    simpa only [I,A,Function.comp_apply,div_one] using
      type6AnglesAndShape_on_sheet (intrinsicComplex second x y v) 1 ⟨x,y⟩ hv
  have hkernel : D.comp dI = 0 :=
    (hD.comp m hi).unique ((hasFDerivAt_const _ _).congr_of_eventuallyEq hconstant)
  have hsurj : Function.Surjective (D.comp dE) := by
    intro u
    obtain ⟨w,hw⟩ := hDs (y^2 • u)
    obtain ⟨v,hv⟩ := hRs w
    have hzero : D (dI v) = 0 :=
      congrArg (fun L : SheetMotion →L[ℝ] (Fin 7 → ℝ) × ℂ => L v) hkernel
    rw [← hv,hr] at hw
    change D (y^2 • (dE v-dI v)) = _ at hw
    rw [map_smul,map_sub,hzero,sub_zero] at hw
    exact ⟨v,smul_right_injective _ (pow_ne_zero _ hy.ne') hw⟩
  have hq : ContDiffAt ℝ 1 type6SpatialAngleShape (W m) := by
    rw [type6SpatialAngleShape_eq_metric]
    change ContDiffAt ℝ 1 (A ∘ type6SpatialLengths) (W m)
    have hA' : ContDiffAt ℝ 1 A (type6SpatialLengths (W m)) := by
      change ContDiffAt ℝ 1 A (E m)
      rwa [hEI]
    exact hA'.comp (W m) type6SpatialLengths_smooth.contDiffAt
  have hf : HasFDerivAt (type6SpatialAngleShape ∘ W)
      ((fderiv ℝ type6SpatialAngleShape (W m)).comp (fderiv ℝ W m)) m :=
    (hq.differentiableAt (by decide)).hasFDerivAt.comp m ((hW.differentiable (by decide) m).hasFDerivAt)
  have hd : HasFDerivAt (type6SpatialAngleShape ∘ W) (D.comp dE) m := by
    rw [type6SpatialAngleShape_eq_metric]
    change HasFDerivAt (A ∘ E) _ m
    rw [← hEI] at hD
    exact hD.comp m he
  have hs : Function.Surjective (fderiv ℝ type6SpatialAngleShape (W m)) := by
    rw [← hf.unique hd] at hsurj
    exact Function.Surjective.of_comp hsurj
  refine ⟨⟨hq,hs⟩,?_⟩
  rw [type6SpatialAngleShape_eq_metric]
  change A (E m) = _
  rw [hEI]
  exact hconstant.self_of_nhds

/-- A common rescaling preserves the seven angles and the marked period ratio. -/
theorem type6SpatialAngleShape_smul (q : Vertex → Point3) {r : ℝ} (hr : r ≠ 0) :
    type6SpatialAngleShape (r • q) = type6SpatialAngleShape q := by
  apply Prod.ext
  · funext i
    change coneAngles type6FlippedFaces (Type2.euclideanPoint ∘ (r • q)) i.succ = _
    have he : Type2.euclideanPoint ∘ (r • q) = fun v => r • Type2.euclideanPoint (q v) := by
      funext v
      exact Type2.euclideanPoint.map_smul r (q v)
    rw [he,coneAngles_smul _ _ hr]
    rfl
  · change type6MetricShape (type6LengthMetric (type6SpatialLengths (r • q))) =
      type6MetricShape (type6LengthMetric (type6SpatialLengths q))
    have he : type6SpatialLengths (r • q) = r^2 • type6SpatialLengths q := by
      funext e
      simp only [type6SpatialLengths,Type7.spatialEdgeSq,Pi.smul_apply,← smul_sub,squared3_smul]
      rfl
    rw [he,map_smul]
    simp only [type6MetricShape,type6MetricDisplacements,attachMetricCorner,Type7.triangleCorner,
      Pi.smul_apply,smul_eq_mul,developedCorner_scale _ _ _ _ _ (pow_ne_zero _ hr)]

/-- Rank nine holds at every nonzero rescaling of the placement. -/
theorem Type6SpatiallyRegular.smul {q : Vertex → Point3} (hq : Type6SpatiallyRegular q)
    {r : ℝ} (hr : r ≠ 0) : Type6SpatiallyRegular (r • q) := by
  let L : (Vertex → Point3) →L[ℝ] (Vertex → Point3) := r⁻¹ • ContinuousLinearMap.id ℝ _
  have he : L (r • q) = q := by simp [L,smul_smul,hr]
  have hs : Function.Surjective L := fun p => ⟨r • p,by simp [L,smul_smul,hr]⟩
  have heq : type6SpatialAngleShape ∘ L = type6SpatialAngleShape :=
    funext fun p => type6SpatialAngleShape_smul p (inv_ne_zero hr)
  have hC : ContDiffAt ℝ 1 type6SpatialAngleShape (L (r • q)) := by rw [he]; exact hq.1
  have h₁ := hC.comp (r • q) L.contDiff.contDiffAt
  have h₂ := (hC.differentiableAt (by decide)).hasFDerivAt.comp (r • q) L.hasFDerivAt
  rw [heq] at h₁ h₂
  refine ⟨h₁,?_⟩
  rw [h₂.fderiv]
  exact (he.symm ▸ hq.2).comp hs

end OrigamiTorus
