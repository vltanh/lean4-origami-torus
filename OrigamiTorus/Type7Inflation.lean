module

public import OrigamiTorus.AngleInflation
public import OrigamiTorus.SpatialRealizations
public import OrigamiTorus.Type4Flip
public import OrigamiTorus.Type7MarkingRank
import Mathlib.Tactic

/-! Embedded inflation of the rectangular planar family preserving the cone
angles and the local Type 7 marking. -/

@[expose] public section

namespace OrigamiTorus.Type7

theorem rectangular_physical_lift (flipped : Bool) (w : ℝ) (hw : 1 ≤ w) :
    let z := physicalComplex w ∘ rectangularPoint w
    ∃ h : Vertex → ℝ, Function.Injective (evaluateTriangles (faceChoice flipped) (angleLift z h 1)) := by
  obtain ⟨h,he⟩ := rectangular_spatialEmbedding flipped w hw
  have hy : Real.sqrt w ≠ 0 := (Real.sqrt_pos.mpr (by linarith)).ne'
  refine ⟨h,?_⟩
  exact evaluateTriangles_rescale_injective (faceChoice flipped)
    (fun i => ((rectangularPoint w i).1,(rectangularPoint w i).2,h i)) hy one_ne_zero he.injective

/-- Every rectangular planar base can be inflated to an embedded spatial
realization preserving the eight cone angles and the marked displacement ratio. -/
theorem rectangular_embedded_flat_markedShape (w : ℝ) (hw : 1 ≤ w) :
    ∃ q : Vertex → Point3, Topology.IsClosedEmbedding (evaluateTriangles faces q) ∧
      (∀ v, coneAngles faces (Type2.euclideanPoint ∘ q) v = 2*Real.pi) ∧
      markedShape (spatialEdgeSq q) = ⟨0,Real.sqrt w⟩ := by
  let z := physicalComplex w ∘ rectangularPoint w
  obtain ⟨h,hz⟩ := rectangular_physical_lift false w hw
  have hfaces : orientedFaces.map Prod.fst = faces := by decide +kernel
  have hangle (v : Vertex) : coneAngles faces z v = 2*Real.pi := by
    rw [← hfaces,coneAngles_eq_chart]
    exact rectangular_euclidean_cone_angle w hw v
  let f (x : ℝ × (Vertex → ℂ)) := (liftedAngles faces h x, markedShape (spatialEdgeSq (angleLift x.2 h x.1)))
  have hd : ContDiffAt ℝ 1 f (0,z) :=
    (contDiffAt_liftedAngles faces h z (rectangular_corners_nondegenerate w hw)).prodMk
      (contDiffAt_rectangular_spatial_markedShape w hw h)
  have he : (fun p => f (0,p)) =
      fun p => (sevenConeAngles faces p,markedShape (planarEdgeSq p)) := by
    funext p
    change (liftedAngles faces h (0,p),markedShape (spatialEdgeSq (angleLift p h 0))) = _
    rw [liftedAngles_zero,spatialEdgeSq_angleLift_zero]
  have hs : Function.Surjective (fderiv ℝ (fun p => f (0,p)) z) := by
    rw [he]
    exact rectangular_angleShape_derivative_surjective w hw
  obtain ⟨t,_,p,hp,ha,hf⟩ := exists_embedded_flat_inflation_of_constraints faces z h
    (by decide +kernel) (by decide +kernel) (by decide +kernel) hangle hz f hd hs
    (fun _ _ hg => congrArg Prod.fst hg)
  refine ⟨angleLift p h t,hp,ha,?_⟩
  have hm := congrArg Prod.snd hf
  change markedShape (spatialEdgeSq (angleLift p h t)) =
    markedShape (spatialEdgeSq (angleLift z h 0)) at hm
  rw [spatialEdgeSq_angleLift_zero] at hm
  exact hm.trans (rectangular_markedShape w hw)

theorem rectangular_embedded_flat_inflation (w : ℝ) (hw : 1 ≤ w) :
    ∃ q : Vertex → Point3, Topology.IsClosedEmbedding (evaluateTriangles faces q) ∧
      ∀ v, coneAngles faces (Type2.euclideanPoint ∘ q) v = 2*Real.pi := by
  obtain ⟨q,hq,ha,_⟩ := rectangular_embedded_flat_markedShape w hw
  exact ⟨q,hq,ha⟩

end OrigamiTorus.Type7

namespace OrigamiTorus.Type4

open Type7 (physicalComplex rectangularPoint)

/-- The flipped rectangular chart gives an embedded flat-star realization on the
Type 4 face list in the Type 7 labels. -/
theorem rectangular_embedded_flat_inflation (w : ℝ) (hw : 1 ≤ w) :
    ∃ q : Vertex → Point3, Topology.IsClosedEmbedding (evaluateTriangles Type7.flippedFaces q) ∧
      ∀ v, coneAngles Type7.flippedFaces (Type2.euclideanPoint ∘ q) v = 2*Real.pi := by
  let p := rectangularPoint w
  let z := physicalComplex w ∘ p
  have hw₀ : 0 < w := by linarith
  obtain ⟨h356,h352,h623,h625⟩ := Type7.rectangular_flipSigns w hw
  have he := sevenConeAngles_flip_eventuallyEq p w hw₀ h356 h352 h623 h625
  have hs : Function.Surjective (fderiv ℝ
      (sevenConeAngles Type7.flippedFaces : (Vertex → ℂ) → Fin 7 → ℝ) z) := by
    rw [he.fderiv_eq]
    exact Type7.rectangular_seven_cone_derivative_surjective w hw
  have hfaces : Type7.orientedFaces.map Prod.fst = Type7.faces := by decide +kernel
  have hangle (v : Vertex) : coneAngles Type7.flippedFaces z v = 2*Real.pi := by
    rw [coneAngles_eq_chart_list,flip_angle_sum p w hw₀ h356 h352 h623 h625 v,← hfaces,List.map_map]
    exact Type7.rectangular_euclidean_cone_angle w hw v
  obtain ⟨h,hz⟩ := Type7.rectangular_physical_lift true w hw
  have hnf : Type7.orientedFlippedFaces.map Prod.fst = Type7.flippedFaces := by decide +kernel
  have hn := planarCorners_nondegenerate_of_face_areas Type7.orientedFlippedFaces p w hw₀
    (fun f hf => Type7.rectangular_flipped_face_orientation w hw f.1 f.2 hf)
  rw [hnf] at hn
  exact exists_embedded_flat_inflation Type7.flippedFaces z h (by decide +kernel) (by decide +kernel)
    (by decide +kernel) hn hangle hs hz

end OrigamiTorus.Type4
