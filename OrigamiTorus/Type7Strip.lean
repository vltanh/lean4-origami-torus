module

public import OrigamiTorus.Type7StripLift
import Mathlib.Tactic

/-! Regular Type 7 realizations on a closed unbounded strip. -/

@[expose] public section

open Filter
open scoped Topology

namespace OrigamiTorus.Type7

open Type4 (stripBase)
open Type5 (squared3)

noncomputable def spatialAngleShape (q : Vertex → Point3) : (Fin 7 → ℝ) × ℂ :=
  (sevenConeAngles faces (Type2.euclideanPoint ∘ q),markedShape (spatialEdgeSq q))

/-- The spatial angle and marked-modulus map is smooth and has rank nine. -/
def SpatiallyRegular (q : Vertex → Point3) : Prop :=
  ContDiffAt ℝ 1 spatialAngleShape q ∧ Function.Surjective (fderiv ℝ spatialAngleShape q)

private theorem spatialAngleShape_smul (q : Vertex → Point3) {r : ℝ} (hr : r ≠ 0) :
    spatialAngleShape (r • q) = spatialAngleShape q := by
  apply Prod.ext
  · funext i
    change coneAngles faces (Type2.euclideanPoint ∘ (r • q)) i.succ = _
    have he : Type2.euclideanPoint ∘ (r • q) = fun v => r • Type2.euclideanPoint (q v) := by
      funext v
      exact Type2.euclideanPoint.map_smul r (q v)
    rw [he,coneAngles_smul _ _ hr]
    rfl
  · change markedShape (spatialEdgeSq (r • q)) = markedShape (spatialEdgeSq q)
    have he : spatialEdgeSq (r • q) = fun a b => r^2*spatialEdgeSq q a b := by
      funext a b
      simp only [spatialEdgeSq,Pi.smul_apply,← smul_sub,squared3_smul]
    rw [he,markedShape_scale _ _ (pow_ne_zero _ hr)]

/-- A common change of length scale preserves the spatial rank. -/
theorem SpatiallyRegular.smul {q : Vertex → Point3} (hq : SpatiallyRegular q)
    {r : ℝ} (hr : r ≠ 0) : SpatiallyRegular (r • q) := by
  let L : (Vertex → Point3) →L[ℝ] (Vertex → Point3) := r⁻¹ • ContinuousLinearMap.id ℝ _
  have he : L (r • q) = q := by simp [L,smul_smul,hr]
  have hs : Function.Surjective L := fun p => ⟨r • p,by simp [L,smul_smul,hr]⟩
  have heq : spatialAngleShape ∘ L = spatialAngleShape :=
    funext fun p => spatialAngleShape_smul p (inv_ne_zero hr)
  have hC : ContDiffAt ℝ 1 spatialAngleShape (L (r • q)) := by rw [he]; exact hq.1
  have h₁ := hC.comp (r • q) L.contDiff.contDiffAt
  have h₂ := (hC.differentiableAt (by decide)).hasFDerivAt.comp
    (r • q) L.hasFDerivAt
  rw [heq] at h₁ h₂
  refine ⟨h₁,?_⟩
  rw [h₂.fderiv]
  exact (he.symm ▸ hq.2).comp hs

private theorem marking_triangles_nondegenerate {z : Vertex → ℂ} (hz : Type4.MarkingChartValid z)
    (f : Triangle) (hf : f ∈ markingTriangles) :
    planarEdgeSq z f.1 f.2.1 ≠ 0 ∧
      developedHeightSq (planarEdgeSq z f.1 f.2.1) (planarEdgeSq z f.1 f.2.2)
        (planarEdgeSq z f.2.1 f.2.2) ≠ 0 := by
  have htable : ∀ f ∈ markingTriangles, (f,true) ∈ Type4.markingOrientations ∨
      (f,false) ∈ Type4.markingOrientations := by decide +kernel
  have hi : (Type4.markingRatio z f).im ≠ 0 := by
    rcases htable f hf with hp | hn
    · exact (show 0 < (Type4.markingRatio z f).im from hz (f,true) hp).ne'
    · exact (neg_pos.mp (show 0 < -(Type4.markingRatio z f).im from hz (f,false) hn)).ne
  have hbase : z f.2.1-z f.1 ≠ 0 := by
    intro h
    exact hi (by simp [Type4.markingRatio,h])
  refine ⟨(Complex.normSq_pos.mpr hbase).ne',?_⟩
  have he := (developed_coords_planar (z f.2.1-z f.1) (z f.2.2-z f.1) hbase).2
  have hsub : (z f.2.2-z f.1)-(z f.2.1-z f.1) = z f.2.2-z f.2.1 := by ring
  rw [hsub] at he
  unfold planarEdgeSq
  rw [he]
  exact pow_ne_zero 2 hi

private theorem regular_flat_markedShape_of_strip_lift {second : Bool} {x w : ℝ}
    (hd : Type4.domain second x w) (h : Vertex → ℝ)
    (hemb : Function.Injective (evaluateTriangles faces (angleLift (stripBase second x w) h 1))) :
    ∃ q : Vertex → Point3, Topology.IsClosedEmbedding (evaluateTriangles faces q) ∧
      (∀ v, coneAngles faces (Type2.euclideanPoint ∘ q) v = 2*Real.pi) ∧
      markedShape (spatialEdgeSq q) = ⟨x,Real.sqrt w⟩ ∧ SpatiallyRegular q := by
  let z := stripBase second x w
  let B (p : ℝ × (Vertex → ℂ)) := angleLift p.2 h p.1
  let f := spatialAngleShape ∘ B
  have hfaces : orientedFaces.map Prod.fst = faces := by decide +kernel
  have hangle (v : Vertex) : coneAngles faces z v = 2*Real.pi := by
    rw [← hfaces,coneAngles_eq_chart]
    exact Type4.trapezoid_euclidean_cone_angle hd v
  have hshape : markedShape (planarEdgeSq z) = ⟨x,Real.sqrt w⟩ := Type4.trapezoid_markedShape hd
  have hB : ContDiff ℝ 1 B := contDiff_angleLift h
  have hs0 : spatialEdgeSq (B (0,z)) = planarEdgeSq z := spatialEdgeSq_angleLift_zero z h
  have hU : (markingDisplacements (spatialEdgeSq (B (0,z)))).1 ≠ 0 := by
    rw [hs0]
    intro hu
    change (markingDisplacements (planarEdgeSq z)).2/(markingDisplacements (planarEdgeSq z)).1 = _ at hshape
    rw [hu,div_zero] at hshape
    exact (Real.sqrt_pos.mpr (Type4.domain_bounds hd).2.2).ne' (congrArg Complex.im hshape).symm
  have hsq : ContDiff ℝ 1 (squared3 : Point3 → ℝ) := by
    unfold squared3 Type5.squared2 Type5.horizontal Type5.dot
    fun_prop
  have hsd (a b : Vertex) : ContDiffAt ℝ 1 (fun q => spatialEdgeSq q a b) (B (0,z)) :=
    (hsq.comp (by fun_prop : ContDiff ℝ 1 (fun q : Vertex → Point3 => q b-q a))).contDiffAt
  have hA : ContDiffAt ℝ 1 spatialAngleShape (B (0,z)) :=
    (contDiffAt_spatialConeAngles_angleLift_zero faces h z (Type4.trapezoid_corners_nondegenerate hd)).prodMk
      (contDiffAt_markedShape hsd (by rw [hs0]; exact marking_triangles_nondegenerate (Type4.strip_markingChartValid hd)) hU)
  have hdiff : ContDiffAt ℝ 1 f (0,z) := hA.comp (0,z) hB.contDiffAt
  have he : (fun p => f (0,p)) =
      fun p => (sevenConeAngles faces p,markedShape (planarEdgeSq p)) := by
    funext p
    change (liftedAngles faces h (0,p),markedShape (spatialEdgeSq (angleLift p h 0))) = _
    rw [liftedAngles_zero,spatialEdgeSq_angleLift_zero]
  have hs : Function.Surjective (fderiv ℝ (fun p => f (0,p)) z) := by
    rw [he]
    exact Type4.strip_angleShape_derivative_surjective hd
  have hH : HasFDerivAt (fun p : Vertex → ℂ => B (0,p))
      ((fderiv ℝ B (0,z)).comp (ContinuousLinearMap.inr ℝ ℝ (Vertex → ℂ))) z :=
    ((hB.contDiffAt (x := (0,z))).differentiableAt (by norm_num)).hasFDerivAt.comp z
      (ContinuousLinearMap.inr ℝ ℝ (Vertex → ℂ)).hasFDerivAt
  have hF := (hA.differentiableAt (by norm_num)).hasFDerivAt.comp z hH
  have hsurjA : Function.Surjective (fderiv ℝ spatialAngleShape (B (0,z))) := by
    change Function.Surjective (fderiv ℝ (spatialAngleShape ∘ fun p => B (0,p)) z) at hs
    rw [hF.fderiv] at hs
    change Function.Surjective ((fderiv ℝ spatialAngleShape (B (0,z))) ∘
      ((fderiv ℝ B (0,z)).comp (ContinuousLinearMap.inr ℝ ℝ (Vertex → ℂ)))) at hs
    exact hs.of_comp
  have hreg : ∀ᶠ q in 𝓝 (B (0,z)), SpatiallyRegular q :=
    (hA.eventually (by decide)).and
      (eventually_surjective_of_continuousAt (hA.continuousAt_fderiv (by decide)) hsurjA)
  obtain ⟨t,_,q,hq,ha,hf,hr⟩ := exists_embedded_flat_inflation_of_constraints_near
    faces z h (by decide +kernel) (by decide +kernel) (by decide +kernel)
    hangle hemb f hdiff hs (P := fun s => SpatiallyRegular (B s)) (hB.continuous.continuousAt hreg)
    (fun _ _ hg => congrArg Prod.fst hg)
  have hm := congrArg Prod.snd hf
  change markedShape (spatialEdgeSq (B (t,q))) = markedShape (spatialEdgeSq (B (0,z))) at hm
  rw [hs0,hshape] at hm
  exact ⟨angleLift q h t,hq,ha,hm,hr⟩

/-- A strict lift of an unflipped chart gives a regular Type 7 realization. -/
theorem chart_regular_realizes_of_lift {second : Bool} {x w : ℝ} (hd : Type4.domain second x w)
    (h : Vertex → ℝ) (hemb : Function.Injective (evaluateTriangles faces (angleLift (stripBase second x w) h 1)))
    (a b D : ℂ) (refl : Bool) (hD : D ≠ 0)
    (hL : complexSimilarity D refl '' complexLattice 1 (x+Real.sqrt w*Complex.I) = complexLattice a b) :
    ChartRealizesWith false a b SpatiallyRegular := by
  have hy : 0 < Real.sqrt w := Real.sqrt_pos.mpr (Type4.domain_bounds hd).2.2
  obtain ⟨q,he,hflat,hm,hreg⟩ := regular_flat_markedShape_of_strip_lift hd h hemb
  refine realizes_of_markedShape_with false q he hflat x (Real.sqrt w) hy ?_ a b D refl hD hL
    (fun r hr => hreg.smul hr.ne')
  change markedShape (spatialEdgeSq q) = _
  rw [hm]
  apply Complex.ext <;> simp [Complex.mul_re,Complex.mul_im]

/-- The unflipped chart realizes every reduced modulus with `0 ≤ x ≤ 1/20`,
with rank nine at the spatial embedding and with the requested lattice scale. -/
theorem strip_regular_realizes_of_similarity {x w : ℝ}
    (hx : 0 ≤ x) (hx' : x ≤ 1/20) (hw : 1-x^2 ≤ w)
    (a b D : ℂ) (refl : Bool) (hD : D ≠ 0)
    (hL : complexSimilarity D refl '' complexLattice 1 (x+Real.sqrt w*Complex.I) = complexLattice a b) :
    ChartRealizesWith false a b SpatiallyRegular := by
  have hd : Type4.domain false x w := ⟨hx,by change x ≤ 9/20; linarith,hw⟩
  obtain ⟨h,hemb⟩ := strip_embedded_lift hx hx' hw
  exact chart_regular_realizes_of_lift hd h hemb a b D refl hD hL

/-- Regular piecewise-isometric Type 7 realizations on the normalized strip. -/
theorem strip_regular_realizes {x w : ℝ} (hx : 0 ≤ x) (hx' : x ≤ 1/20) (hw : 1-x^2 ≤ w) :
    ChartRealizesWith false 1 (x+Real.sqrt w*Complex.I) SpatiallyRegular := by
  have he : complexSimilarity 1 false = id := by funext p; simp [complexSimilarity]
  exact strip_regular_realizes_of_similarity hx hx' hw 1 _ 1 false one_ne_zero (by rw [he,Set.image_id])

theorem strip_realizes {x w : ℝ} (hx : 0 ≤ x) (hx' : x ≤ 1/20) (hw : 1-x^2 ≤ w) :
    Realizes 1 (x+Real.sqrt w*Complex.I) :=
  (strip_regular_realizes hx hx' hw).realizes

end OrigamiTorus.Type7
