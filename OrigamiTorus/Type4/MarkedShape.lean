module

public import OrigamiTorus.Lattice.MarkedShape
public import OrigamiTorus.Type4.Flip
public import OrigamiTorus.Type7.Inflation
import Mathlib.Tactic

/-! The marked loops after the Type 4 diagonal exchange, rooted at the new edge 26. -/

@[expose] public section

open Filter
open scoped Topology

namespace OrigamiTorus.Type4

open Type7 (triangleCorner planarEdgeSq reflectComplex)

noncomputable def flippedMarkingDisplacements (s : Vertex → Vertex → ℝ) : ℂ × ℂ :=
  let z₃ := triangleCorner s true 2 6 3
  let z₅ := triangleCorner s false 2 6 5
  let z₄ := z₅-z₅*triangleCorner s true 5 2 4
  let z₀ := z₃*triangleCorner s true 2 3 0
  let z₄' := z₃+(1-z₃)*triangleCorner s true 3 6 4
  let z₀' := 1+(z₅-1)*triangleCorner s true 6 5 0
  (z₄'-z₄,z₀-z₀')

noncomputable def flippedMarkedShape (s : Vertex → Vertex → ℝ) : ℂ :=
  (flippedMarkingDisplacements s).2/(flippedMarkingDisplacements s).1

/-- The same loop increments in the chart normalized at edge 26. -/
theorem flippedMarkingDisplacements_planar (p : Vertex → ℂ)
    (h26 : p 6-p 2 ≠ 0) (h52 : p 2-p 5 ≠ 0) (h23 : p 3-p 2 ≠ 0)
    (h36 : p 6-p 3 ≠ 0) (h65 : p 5-p 6 ≠ 0)
    (h3 : 0 ≤ ((p 3-p 2)/(p 6-p 2)).im)
    (h5 : ((p 5-p 2)/(p 6-p 2)).im ≤ 0)
    (h4 : 0 ≤ ((p 4-p 5)/(p 2-p 5)).im)
    (h0 : 0 ≤ ((p 0-p 2)/(p 3-p 2)).im)
    (h4' : ((p 4-p 3)/(p 6-p 3)).im ≤ 0)
    (h0' : ((p 0-p 6)/(p 5-p 6)).im ≤ 0) :
    let U := p 3-p 4+reflectComplex (p 6-p 3) (p 4-p 3)
    let V := p 0-p 5+reflectComplex (p 5-p 6) (p 5-p 0)
    flippedMarkingDisplacements (planarEdgeSq p) = (U/(p 6-p 2),V/(p 6-p 2)) := by
  simp only [flippedMarkingDisplacements,Type7.triangleCorner_planar p true 2 6 3 h26 h3,
    Type7.triangleCorner_planar p false 2 6 5 h26 h5,Type7.triangleCorner_planar p true 5 2 4 h52 h4,
    Type7.triangleCorner_planar p true 2 3 0 h23 h0,
    Type7.triangleCorner_planar_reflected p 3 6 4 h36 h4',
    Type7.triangleCorner_planar_reflected p 6 5 0 h65 h0']
  let e := p 6-p 2
  have hA : (p 5-p 2)/e-(p 5-p 2)/e*((p 4-p 5)/(p 2-p 5)) = (p 4-p 2)/e := by
    dsimp only [e]
    field_simp [h26,h52]
    ring
  have hB : (p 3-p 2)/e*((p 0-p 2)/(p 3-p 2)) = (p 0-p 2)/e := by
    dsimp only [e]
    field_simp [h26,h23]
  have hC : 1-(p 3-p 2)/e = (p 6-p 3)/e := by
    dsimp only [e]
    field_simp [h26]
    ring
  have hD : (p 5-p 2)/e-1 = (p 5-p 6)/e := by
    dsimp only [e]
    field_simp [h26]
    ring
  have hE : (p 0-p 6)/(p 5-p 6) = 1-(p 5-p 0)/(p 5-p 6) := by
    field_simp [h65]
    ring
  rw [hA,hB,hC,hD,hE,map_sub,map_one]
  apply Prod.ext
  · dsimp only [reflectComplex,e]
    ring
  · nth_rw 1 [← div_self h26]
    dsimp only [reflectComplex,e]
    ring

/-- Convex exchange of the diagonal preserves the marked shape computed from
the planar edge lengths. The signs refer to the shared six-triangle paths. -/
theorem planarMarkedShape_flip (p : Vertex → ℂ)
    (h35 : p 5-p 3 ≠ 0) (h26 : p 6-p 2 ≠ 0) (h52 : p 2-p 5 ≠ 0)
    (h23 : p 3-p 2 ≠ 0) (h36 : p 6-p 3 ≠ 0) (h65 : p 5-p 6 ≠ 0)
    (h2 : ((p 2-p 3)/(p 5-p 3)).im ≤ 0)
    (h6 : 0 ≤ ((p 6-p 3)/(p 5-p 3)).im)
    (h3 : 0 ≤ ((p 3-p 2)/(p 6-p 2)).im)
    (h5 : ((p 5-p 2)/(p 6-p 2)).im ≤ 0)
    (h4 : 0 ≤ ((p 4-p 5)/(p 2-p 5)).im)
    (h0 : 0 ≤ ((p 0-p 2)/(p 3-p 2)).im)
    (h4' : ((p 4-p 3)/(p 6-p 3)).im ≤ 0)
    (h0' : ((p 0-p 6)/(p 5-p 6)).im ≤ 0) :
    flippedMarkedShape (planarEdgeSq p) = Type7.markedShape (planarEdgeSq p) := by
  have h₁ := Type7.markingDisplacements_planar p h35 h52 h23 h36 h65 h2 h6 h4 h0 h4' h0'
  have h₂ := flippedMarkingDisplacements_planar p h26 h52 h23 h36 h65 h3 h5 h4 h0 h4' h0'
  unfold flippedMarkedShape Type7.markedShape
  rw [h₁,h₂]
  dsimp only
  rw [div_div_div_cancel_right₀ h35,div_div_div_cancel_right₀ h26]

/-- The triangles used by the two shape maps, with their signs in the folded plane. -/
def markingOrientations : List (Triangle × Bool) :=
  [((3,5,2),false),((3,5,6),true),((2,6,3),true),((2,6,5),false),
    ((5,2,4),true),((2,3,0),true),((3,6,4),false),((6,5,0),false)]

noncomputable def markingRatio (z : Vertex → ℂ) (f : Triangle) : ℂ :=
  (z f.2.2-z f.1)/(z f.2.1-z f.1)

noncomputable def signedIm (z : Vertex → ℂ) (f : Triangle × Bool) : ℝ :=
  if f.2 then (markingRatio z f.1).im else -(markingRatio z f.1).im

def MarkingChartValid (z : Vertex → ℂ) : Prop :=
  ∀ f ∈ markingOrientations, 0 < signedIm z f

private theorem markingRatio_denominator_ne (z : Vertex → ℂ) (f : Triangle × Bool)
    (h : 0 < signedIm z f) : z f.1.2.1-z f.1.1 ≠ 0 := by
  intro he
  cases hsign : f.2 <;> simp [signedIm,markingRatio,hsign,he] at h

theorem markingChartValid_of_areas (p : Vertex → ℝ × ℝ) (w : ℝ) (hw : 0 < w)
    (hs : ∀ f ∈ Type7.orientedFaces, 0 <
      if f.2 then area p f.1.1 f.1.2.1 f.1.2.2 else -area p f.1.1 f.1.2.1 f.1.2.2)
    (h356 : 0 < area p 3 5 6) (h352 : area p 3 5 2 < 0)
    (h623 : area p 6 2 3 < 0) (h625 : 0 < area p 6 2 5) :
    MarkingChartValid (Type7.physicalComplex w ∘ p) := by
  have hcycle (a b c : Vertex) : area p c a b = area p a b c := by unfold area; ring
  have hswap (a b c : Vertex) : area p b a c = -area p a b c := by unfold area; ring
  intro f hf
  obtain ⟨⟨a,b,c⟩,s⟩ := f
  apply (Type7.normalizedCorner_sign p w hw a b c s ?_).2
  suffices H : ∀ f ∈ markingOrientations, (0 < if f.2 then area p f.1.1 f.1.2.1 f.1.2.2 else -area p f.1.1 f.1.2.1 f.1.2.2) by
    exact H ((a,b,c),s) hf
  intro f hf'
  simp only [markingOrientations,List.mem_cons,List.not_mem_nil,or_false] at hf'
  rcases hf' with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact neg_pos.mpr h352
  · exact h356
  · change 0 < area p 2 6 3
    rw [hswap]
    exact neg_pos.mpr h623
  · change 0 < -area p 2 6 5
    rw [hswap,neg_neg]
    exact h625
  · exact hs ((5,2,4),true) (by decide +kernel)
  · change 0 < area p 2 3 0
    rw [hcycle]
    exact hs ((3,0,2),true) (by decide +kernel)
  · exact hs ((3,6,4),false) (by decide +kernel)
  · change 0 < -area p 6 5 0
    rw [hcycle]
    exact hs ((5,0,6),false) (by decide +kernel)

theorem planarMarkedShape_flip_of_valid (z : Vertex → ℂ) (hz : MarkingChartValid z) :
    flippedMarkedShape (planarEdgeSq z) = Type7.markedShape (planarEdgeSq z) := by
  have h₂ := hz ((3,5,2),false) (by decide +kernel)
  have h₆ := hz ((3,5,6),true) (by decide +kernel)
  have h₃ := hz ((2,6,3),true) (by decide +kernel)
  have h₅ := hz ((2,6,5),false) (by decide +kernel)
  have h₄ := hz ((5,2,4),true) (by decide +kernel)
  have h₀ := hz ((2,3,0),true) (by decide +kernel)
  have h₄' := hz ((3,6,4),false) (by decide +kernel)
  have h₀' := hz ((6,5,0),false) (by decide +kernel)
  exact planarMarkedShape_flip z
    (markingRatio_denominator_ne z _ h₂) (markingRatio_denominator_ne z _ h₃)
    (markingRatio_denominator_ne z _ h₄) (markingRatio_denominator_ne z _ h₀)
    (markingRatio_denominator_ne z _ h₄') (markingRatio_denominator_ne z _ h₀')
    (neg_pos.mp h₂).le h₆.le h₃.le (neg_pos.mp h₅).le h₄.le h₀.le (neg_pos.mp h₄').le (neg_pos.mp h₀').le

/-- Strict orientation keeps the two planar shape maps equal on a neighborhood. -/
theorem planarMarkedShape_flip_eventuallyEq (z : Vertex → ℂ) (hz : MarkingChartValid z) :
    (fun p => flippedMarkedShape (planarEdgeSq p))
      =ᶠ[𝓝 z] (fun p => Type7.markedShape (planarEdgeSq p)) := by
  have hh (f : Triangle × Bool) (hf : f ∈ markingOrientations.toFinset) :
      ∀ᶠ p in 𝓝 z, 0 < signedIm p f := by
    have hs := hz f (List.mem_toFinset.mp hf)
    have hq : ContinuousAt (fun p : Vertex → ℂ => markingRatio p f.1) z := by
      unfold markingRatio
      apply ContinuousAt.div (by fun_prop) (by fun_prop)
      exact markingRatio_denominator_ne z f hs
    have hc := Complex.continuous_im.continuousAt.comp hq
    have hcont : ContinuousAt (fun p => signedIm p f) z := by
      cases s : f.2
      · have hn : Continuous (fun r : ℝ => -r) := continuous_neg
        simpa only [signedIm,s,Bool.false_eq_true,ite_false,Function.comp_def] using hn.continuousAt.comp hc
      · simpa only [signedIm,s,ite_true,Function.comp_def] using hc
    exact continuousAt_const.eventually_lt hcont hs
  filter_upwards [(eventually_all_finset _).2 hh] with p hp
  exact planarMarkedShape_flip_of_valid p (fun f hf => hp f (List.mem_toFinset.mpr hf))

/-- The Type 4 shape map reads the desired modulus on both trapezoidal charts. -/
theorem trapezoid_flippedMarkedShape {nearEndpoint : Bool} {x w : ℝ}
    (hd : domain nearEndpoint x w) :
    let p := polynomialPoints x w (if nearEndpoint then 2/3 else 1/3) (trapezoidHeight nearEndpoint x) 1
    flippedMarkedShape (planarEdgeSq (Type7.physicalComplex w ∘ p)) = ⟨x,Real.sqrt w⟩ := by
  let p := polynomialPoints x w (if nearEndpoint then 2/3 else 1/3) (trapezoidHeight nearEndpoint x) 1
  let z := Type7.physicalComplex w ∘ p
  obtain ⟨h356,h352,h623,h625⟩ := poly_chart_flipSigns hd
  have hz : MarkingChartValid z := markingChartValid_of_areas p w (domain_bounds hd).2.2
    (poly_chart_face_signs hd) h356 h352 h623 h625
  exact (planarMarkedShape_flip_of_valid z hz).trans (trapezoid_markedShape hd)

theorem rectangular_markingChartValid (w : ℝ) (hw : 1 ≤ w) :
    MarkingChartValid (Type7.physicalComplex w ∘ Type7.rectangularPoint w) := by
  obtain ⟨h356,h352,h623,h625⟩ := Type7.rectangular_flipSigns w hw
  apply markingChartValid_of_areas (Type7.rectangularPoint w) w (by linarith) _ h356 h352 h623 h625
  intro f hf
  have hsign := Type7.rectangular_face_orientation w hw f.1 f.2 hf
  cases hs : f.2
  · simpa only [hs,Bool.false_eq_true,ite_false,neg_pos] using hsign
  · simpa only [hs,ite_true] using hsign

/-- At a rectangular base the flip preserves the surjectivity of the full
seven-angle and two-shape derivative. -/
theorem rectangular_flippedAngleShape_derivative_surjective (w : ℝ) (hw : 1 ≤ w) :
    let z := Type7.physicalComplex w ∘ Type7.rectangularPoint w
    Function.Surjective (fderiv ℝ (fun p : Vertex → ℂ =>
      (sevenConeAngles Type7.flippedFaces p,flippedMarkedShape (planarEdgeSq p))) z) := by
  let p := Type7.rectangularPoint w
  let z := Type7.physicalComplex w ∘ p
  obtain ⟨h356,h352,h623,h625⟩ := Type7.rectangular_flipSigns w hw
  have ha := sevenConeAngles_flip_eventuallyEq p w (by linarith) h356 h352 h623 h625
  have hm := planarMarkedShape_flip_eventuallyEq z (rectangular_markingChartValid w hw)
  have hEq : (fun p : Vertex → ℂ => (sevenConeAngles Type7.flippedFaces p,flippedMarkedShape (planarEdgeSq p)))
      =ᶠ[𝓝 z] fun p => (sevenConeAngles Type7.faces p,Type7.markedShape (planarEdgeSq p)) := by
    filter_upwards [ha,hm] with q h₁ h₂
    exact Prod.ext h₁ h₂
  change Function.Surjective (fderiv ℝ (fun q : Vertex → ℂ =>
    (sevenConeAngles Type7.flippedFaces q,flippedMarkedShape (planarEdgeSq q))) z)
  rw [hEq.fderiv_eq]
  exact Type7.rectangular_angleShape_derivative_surjective w hw

theorem contDiffAt_flippedMarkedShape {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {s : E → Vertex → Vertex → ℝ} {x : E} {z : Vertex → ℂ}
    (hs : ∀ a b, ContDiffAt ℝ 1 (fun q => s q a b) x)
    (hbase : s x = planarEdgeSq z) (hz : MarkingChartValid z)
    (hU : (flippedMarkingDisplacements (s x)).1 ≠ 0) :
    ContDiffAt ℝ 1 (fun q => flippedMarkedShape (s q)) x := by
  have ht (a b c : Vertex) (sign sgn : Bool) (hm : ((a,b,c),sgn) ∈ markingOrientations) :
      ContDiffAt ℝ 1 (fun q => triangleCorner (s q) sign a b c) x := by
    have hsgn := hz ((a,b,c),sgn) hm
    have hn := markingRatio_denominator_ne z ((a,b,c),sgn) hsgn
    have hi : ((z c-z a)/(z b-z a)).im ≠ 0 := by
      intro he
      cases sgn <;> simp [signedIm,markingRatio,he] at hsgn
    have he : z c-z a-(z b-z a) = z c-z b := by ring
    apply contDiffAt_developedCorner sign (hs a b) (hs a c) (hs b c) <;> rw [hbase]
    · exact (Complex.normSq_pos.mpr hn).ne'
    · change developedHeightSq (Complex.normSq (z b-z a)) (Complex.normSq (z c-z a))
        (Complex.normSq (z c-z b)) ≠ 0
      rw [← he,(developed_coords_planar (z b-z a) (z c-z a) hn).2]
      exact pow_ne_zero _ hi
  have h₃ := ht 2 6 3 true true (by decide +kernel)
  have h₅ := ht 2 6 5 false false (by decide +kernel)
  have h₄ := ht 5 2 4 true true (by decide +kernel)
  have h₀ := ht 2 3 0 true true (by decide +kernel)
  have h₄' := ht 3 6 4 true false (by decide +kernel)
  have h₀' := ht 6 5 0 true false (by decide +kernel)
  have hfirst : ContDiffAt ℝ 1 (fun q => (flippedMarkingDisplacements (s q)).1) x :=
    (h₃.add ((contDiffAt_const.sub h₃).mul h₄')).sub (h₅.sub (h₅.mul h₄))
  have hsecond : ContDiffAt ℝ 1 (fun q => (flippedMarkingDisplacements (s q)).2) x :=
    (h₃.mul h₀).sub (contDiffAt_const.add ((h₅.sub contDiffAt_const).mul h₀'))
  simpa only [flippedMarkedShape,div_eq_mul_inv] using hsecond.mul (hfirst.fun_inv hU)

/-- Seven cone angles and the complex marked modulus as functions of the
eight spatial vertex positions. -/
noncomputable def spatialAngleShape (q : Vertex → Point3) : (Fin 7 → ℝ) × ℂ :=
  (sevenConeAngles Type7.flippedFaces (Type2.euclideanPoint ∘ q),
    flippedMarkedShape (Type7.spatialEdgeSq q))

/-- The spatial angle and modulus map is locally smooth and has rank nine. -/
def SpatiallyRegular (q : Vertex → Point3) : Prop :=
  ContDiffAt ℝ 1 spatialAngleShape q ∧ Function.Surjective (fderiv ℝ spatialAngleShape q)

/-- A Type 4 planar base with a strict lift and surjective horizontal
differential gives a regular spatial placement at its marked modulus. -/
theorem regular_embedded_flat_markedShape_of_planar (z : Vertex → ℂ) (h : Vertex → ℝ) (τ : ℂ)
    (hτ : 0 < τ.im) (hz : MarkingChartValid z)
    (hbaseShape : flippedMarkedShape (planarEdgeSq z) = τ)
    (hemb : Function.Injective (evaluateTriangles Type7.flippedFaces (angleLift z h 1)))
    (hangle : ∀ v, coneAngles Type7.flippedFaces z v = 2*Real.pi)
    (hn : ∀ f ∈ Type7.flippedFaces, ∀ v a b, cornerRays v f = some (a,b) →
      z a ≠ z v ∧ z b ≠ z v ∧ 0 < InnerProductGeometry.angle (z a-z v) (z b-z v) ∧
        InnerProductGeometry.angle (z a-z v) (z b-z v) < Real.pi)
    (hsurj : Function.Surjective (fderiv ℝ (fun p : Vertex → ℂ =>
      (sevenConeAngles Type7.flippedFaces p,flippedMarkedShape (planarEdgeSq p))) z)) :
    ∃ q : Vertex → Point3, Topology.IsClosedEmbedding (evaluateTriangles Type7.flippedFaces q) ∧
      (∀ v, coneAngles Type7.flippedFaces (Type2.euclideanPoint ∘ q) v = 2*Real.pi) ∧
      flippedMarkedShape (Type7.spatialEdgeSq q) = τ ∧ SpatiallyRegular q := by
  let B (x : ℝ × (Vertex → ℂ)) := angleLift x.2 h x.1
  let f := spatialAngleShape ∘ B
  have hB : ContDiff ℝ 1 B := contDiff_angleLift h
  have hs0 : Type7.spatialEdgeSq (B (0,z)) = planarEdgeSq z :=
    Type7.spatialEdgeSq_angleLift_zero z h
  have hUnz : (flippedMarkingDisplacements (Type7.spatialEdgeSq (B (0,z)))).1 ≠ 0 := by
    rw [hs0]
    intro he
    unfold flippedMarkedShape at hbaseShape
    rw [he,div_zero] at hbaseShape
    exact hτ.ne' (congrArg Complex.im hbaseShape).symm
  have hsq : ContDiff ℝ 1 (Type5.squared3 : Point3 → ℝ) := by
    unfold Type5.squared3 Type5.squared2 Type5.horizontal Type5.dot
    fun_prop
  have hsd (a b : Vertex) : ContDiffAt ℝ 1 (fun q => Type7.spatialEdgeSq q a b) (B (0,z)) :=
    (hsq.comp (by fun_prop : ContDiff ℝ 1
      (fun q : Vertex → Point3 => q b-q a))).contDiffAt
  have hA : ContDiffAt ℝ 1 spatialAngleShape (B (0,z)) :=
    (contDiffAt_spatialConeAngles_angleLift_zero Type7.flippedFaces h z hn).prodMk
      (contDiffAt_flippedMarkedShape hsd hs0 hz hUnz)
  have hd : ContDiffAt ℝ 1 f (0,z) := hA.comp (0,z) hB.contDiffAt
  have he : (fun p => f (0,p)) =
      fun p => (sevenConeAngles Type7.flippedFaces p,flippedMarkedShape (planarEdgeSq p)) := by
    funext p
    change (liftedAngles Type7.flippedFaces h (0,p),
      flippedMarkedShape (Type7.spatialEdgeSq (angleLift p h 0))) = _
    rw [liftedAngles_zero,Type7.spatialEdgeSq_angleLift_zero]
  have hs : Function.Surjective (fderiv ℝ (fun p => f (0,p)) z) := by
    rwa [he]
  have hD := hA.differentiableAt (by norm_num)
  have hH : HasFDerivAt (fun p : Vertex → ℂ => B (0,p))
      ((fderiv ℝ B (0,z)).comp (ContinuousLinearMap.inr ℝ ℝ (Vertex → ℂ))) z :=
    ((hB.contDiffAt (x := (0,z))).differentiableAt (by norm_num)).hasFDerivAt.comp z
      (ContinuousLinearMap.inr ℝ ℝ (Vertex → ℂ)).hasFDerivAt
  have hF := hD.hasFDerivAt.comp z hH
  have hsurjA : Function.Surjective (fderiv ℝ spatialAngleShape (B (0,z))) := by
    change Function.Surjective (fderiv ℝ (spatialAngleShape ∘ fun p => B (0,p)) z) at hs
    rw [hF.fderiv] at hs
    change Function.Surjective ((fderiv ℝ spatialAngleShape (B (0,z))) ∘
      ((fderiv ℝ B (0,z)).comp (ContinuousLinearMap.inr ℝ ℝ (Vertex → ℂ)))) at hs
    exact hs.of_comp
  have hreg : ∀ᶠ q in 𝓝 (B (0,z)), SpatiallyRegular q :=
    (hA.eventually (by decide)).and
      (eventually_surjective_of_continuousAt (hA.continuousAt_fderiv (by decide)) hsurjA)
  obtain ⟨t,_,q,hq,ha,hf,hreg'⟩ := exists_embedded_flat_inflation_of_constraints_near
    Type7.flippedFaces z h (by decide +kernel) (by decide +kernel) (by decide +kernel)
    hangle hemb f hd hs (P := fun x => SpatiallyRegular (B x)) (hB.continuous.continuousAt hreg)
    (fun _ _ hg => congrArg Prod.fst hg)
  refine ⟨angleLift q h t,hq,ha,?_,hreg'⟩
  have hm := congrArg Prod.snd hf
  change flippedMarkedShape (Type7.spatialEdgeSq (B (t,q))) =
    flippedMarkedShape (Type7.spatialEdgeSq (B (0,z))) at hm
  rw [hs0,hbaseShape] at hm
  exact hm

/-- Inflate a Type 4 planar base while preserving its marked modulus. -/
theorem embedded_flat_markedShape_of_planar (z : Vertex → ℂ) (h : Vertex → ℝ) (τ : ℂ)
    (hτ : 0 < τ.im) (hz : MarkingChartValid z)
    (hbaseShape : flippedMarkedShape (planarEdgeSq z) = τ)
    (hemb : Function.Injective (evaluateTriangles Type7.flippedFaces (angleLift z h 1)))
    (hangle : ∀ v, coneAngles Type7.flippedFaces z v = 2*Real.pi)
    (hn : ∀ f ∈ Type7.flippedFaces, ∀ v a b, cornerRays v f = some (a,b) →
      z a ≠ z v ∧ z b ≠ z v ∧ 0 < InnerProductGeometry.angle (z a-z v) (z b-z v) ∧
        InnerProductGeometry.angle (z a-z v) (z b-z v) < Real.pi)
    (hsurj : Function.Surjective (fderiv ℝ (fun p : Vertex → ℂ =>
      (sevenConeAngles Type7.flippedFaces p,flippedMarkedShape (planarEdgeSq p))) z)) :
    ∃ q : Vertex → Point3, Topology.IsClosedEmbedding (evaluateTriangles Type7.flippedFaces q) ∧
      (∀ v, coneAngles Type7.flippedFaces (Type2.euclideanPoint ∘ q) v = 2*Real.pi) ∧
      flippedMarkedShape (Type7.spatialEdgeSq q) = τ := by
  obtain ⟨q,he,hflat,hm,_⟩ := regular_embedded_flat_markedShape_of_planar
    z h τ hτ hz hbaseShape hemb hangle hn hsurj
  exact ⟨q,he,hflat,hm⟩

/-- Inflation at rectangular bases preserves the local Type 4 marking and
all cone angles, with lengths read from the new diagonal 26. -/
theorem rectangular_embedded_flat_markedShape (w : ℝ) (hw : 1 ≤ w) :
    ∃ q : Vertex → Point3, Topology.IsClosedEmbedding (evaluateTriangles Type7.flippedFaces q) ∧
      (∀ v, coneAngles Type7.flippedFaces (Type2.euclideanPoint ∘ q) v = 2*Real.pi) ∧
      flippedMarkedShape (Type7.spatialEdgeSq q) = ⟨0,Real.sqrt w⟩ := by
  let p := Type7.rectangularPoint w
  let z := Type7.physicalComplex w ∘ p
  have hw₀ : 0 < w := by linarith
  have hz : MarkingChartValid z := rectangular_markingChartValid w hw
  have hbaseShape : flippedMarkedShape (planarEdgeSq z) = ⟨0,Real.sqrt w⟩ :=
    (planarMarkedShape_flip_of_valid z hz).trans (Type7.rectangular_markedShape w hw)
  obtain ⟨h,hemb⟩ := Type7.rectangular_physical_lift true w hw
  obtain ⟨h356,h352,h623,h625⟩ := Type7.rectangular_flipSigns w hw
  have hfaces : Type7.orientedFaces.map Prod.fst = Type7.faces := by decide +kernel
  have hangle (v : Vertex) : coneAngles Type7.flippedFaces z v = 2*Real.pi := by
    rw [coneAngles_eq_chart_list,flip_angle_sum p w hw₀ h356 h352 h623 h625 v,← hfaces,List.map_map]
    exact Type7.rectangular_euclidean_cone_angle w hw v
  have hnf : Type7.orientedFlippedFaces.map Prod.fst = Type7.flippedFaces := by decide +kernel
  have hn := planarCorners_nondegenerate_of_face_areas Type7.orientedFlippedFaces p w hw₀
    (fun f hf => Type7.rectangular_flipped_face_orientation w hw f.1 f.2 hf)
  rw [hnf] at hn
  exact embedded_flat_markedShape_of_planar z h ⟨0,Real.sqrt w⟩ (Real.sqrt_pos.mpr hw₀) hz
    hbaseShape hemb hangle hn (rectangular_flippedAngleShape_derivative_surjective w hw)

end OrigamiTorus.Type4
