module

public import OrigamiTorus.Lattice.PeriodicArea
public import OrigamiTorus.Geometry.SpatialRealizations
import Mathlib.Tactic

/-! The intrinsic Type 6 triangles triangulate their marked torus exactly once. -/

public section

open Set

namespace OrigamiTorus

theorem type6_intrinsicMap_injective (x w : ℝ) (hw : 0 < w)
    (q : Vertex → ℝ × ℝ) (hpos : ∀ j : Fin 16, 0 < periodicFaceArea x w q (liftedFaces j)) :
    Function.Injective (type6_intrinsicMap x w q) := by
  rw [type6_intrinsicMap_eq_development]
  exact type6_periodicFaceSystem.injective x w hw q hpos (type6_latticeTotalArea x w hw.ne' q)

/-- The intrinsic Type 6 development is a homeomorphism to the marked quotient. -/
noncomputable def type6_intrinsicHomeomorph (x w : ℝ) (hw : 0 < w)
    (q : Vertex → ℝ × ℝ) (hpos : ∀ j : Fin 16, 0 < periodicFaceArea x w q (liftedFaces j)) :
    triangleWeightSpace type6FlippedFaces ≃ₜ MarkedTorus :=
  type6_periodicFaceSystem.homeomorph x w hw q hpos (type6_latticeTotalArea x w hw.ne' q)

theorem type6_intrinsicHomeomorph_apply (x w : ℝ) (hw : 0 < w)
    (q : Vertex → ℝ × ℝ) (hpos : ∀ j : Fin 16, 0 < periodicFaceArea x w q (liftedFaces j))
    (u : triangleWeightSpace type6FlippedFaces) :
    type6_intrinsicHomeomorph x w hw q hpos u = type6_intrinsicMap x w q u := by
  unfold type6_intrinsicHomeomorph
  rw [type6_intrinsicMap_eq_development]
  exact type6_periodicFaceSystem.homeomorph_apply x w hw q hpos (type6_latticeTotalArea x w hw.ne' q) u

open Type5 (squared2 squared3)

/-- Evaluation of a face in ordinary Euclidean coordinates on the intrinsic sheet. -/
@[expose] noncomputable def physicalFacePoint (second : Bool) (x y : ℝ) (m : SheetMotion)
    (j : Fin 16) (u : Vertex → ℝ) : ℝ × ℝ :=
  ∑ i, u i • physicalIntrinsicCorner second x y m (i,facePeriod (liftedFaces j) i)

private noncomputable def unscalePlane (y : ℝ) : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ) where
  toFun := fun p => (p.1,p.2/y)
  map_add' a b := by
    apply Prod.ext
    · rfl
    · exact add_div a.2 b.2 y
  map_smul' r a := by
    have hs (p : ℝ × ℝ) : r • p = (r*p.1,r*p.2) := rfl
    simp [hs,mul_div_assoc]

theorem type6_project_physicalFacePoint (second : Bool) (x y : ℝ) (hy : y ≠ 0) (m : SheetMotion)
    (j : Fin 16) (u : triangleWeightSpace type6FlippedFaces)
    (hu : u.val ∈ faceWeights (triangleVertexSet (liftedVertices (liftedFaces j)))) :
    type6_intrinsicMap x (y^2) (movedIntrinsicPoint second x (y^2) m) u =
      projectPeriods (periodCoordinates x y (physicalFacePoint second x y m j u.val)) := by
  let q := movedIntrinsicPoint second x (y^2) m
  let f := liftedFaces j
  have hP : physicalFacePoint second x y m j u.val =
      unscalePlane y (∑ i, u.val i • translatePoint x (y^2) (facePeriod f i) (q i)) := by
    unfold physicalFacePoint
    change (∑ i, u.val i • unscalePlane y (translatePoint x (y^2) (facePeriod f i) (q i))) = _
    simp only [map_sum,map_smul]
  have hcoord (p : ℝ × ℝ) : periodCoordinates x y (unscalePlane y p) = periodCoordinates x (y^2) p := by
    have h (r : ℝ) : r/y/y = r/y^2 := by rw [div_div,pow_two]
    apply Prod.ext <;> simp only [periodCoordinates,unscalePlane,LinearMap.coe_mk,AddHom.coe_mk,h]
  change type6_intrinsicMap x (y^2) q u = _
  rw [type6_intrinsicMap_on_face x (y^2) q j u hu, facePeriodPoint_eq_coordinates _ _ (pow_ne_zero 2 hy),
    hP,hcoord]

theorem type6_weighted_face_metric (second : Bool) (x y : ℝ) (hy : y ≠ 0) (m : SheetMotion)
    (z : Vertex → ℝ) (t : ℝ) (hlen : lengthResidual second x (y^2) z (t,m) = 0)
    (j : Fin 16) (u v : triangleWeightSpace type6FlippedFaces)
    (hu : u.val ∈ faceWeights (triangleVertexSet (liftedVertices (liftedFaces j))))
    (hv : v.val ∈ faceWeights (triangleVertexSet (liftedVertices (liftedFaces j)))) :
    let E := evaluateTriangles type6FlippedFaces (physicalFoldedVertex second x y m z t)
    squared3 (E u - E v) =
      squared2 (physicalFacePoint second x y m j u.val - physicalFacePoint second x y m j v.val) := by
  dsimp only
  unfold evaluateTriangles evaluateWeights physicalFacePoint
  have hd := type6_periodicFaceSystem.distinct j
  rw [lifted_affine_difference (liftedFaces j) hd _ _ _ hu hv,
    lifted_affine_difference (liftedFaces j) hd _ _ _ hu hv]
  obtain ⟨ha,hb,hc⟩ := type6_facePeriod_correct j
  simp only [ha,hb,hc]
  exact type6_face_metric second x y m z t hy hlen j _ _

/-- A marked flat torus in the reduced half-domain has an embedded Type 6
origami realization. The homeomorphism supplies the triangulation, and the
folding preserves all distances within each lifted face. -/
theorem type6_regular_origamiTorus (x y : ℝ) (hx : 0 ≤ x) (hx' : x ≤ 1/2)
    (hy : 0 < y) (hw : 1-x^2 ≤ y^2) {U : Set SheetMotion} (hU : IsOpen U) (hbase : 0 ∈ U) :
    ∃ (second : Bool) (z : Vertex → ℝ) (t : ℝ) (m : SheetMotion)
      (H : triangleWeightSpace type6FlippedFaces ≃ₜ MarkedTorus) (F : MarkedTorus → Point3),
      chartDomain second x (y^2) ∧ 0 < t ∧ m ∈ U ∧
      Type6SpatiallyRegular (physicalFoldedVertex second x y m z t) ∧
      Topology.IsClosedEmbedding F ∧
      (∀ u, F (H u) = evaluateTriangles type6FlippedFaces (physicalFoldedVertex second x y m z t) u) ∧
      (∀ j u, u.val ∈ faceWeights (triangleVertexSet (liftedVertices (liftedFaces j))) →
        H u = projectPeriods (periodCoordinates x y (physicalFacePoint second x y m j u.val))) ∧
      ∀ j u v,
        u.val ∈ faceWeights (triangleVertexSet (liftedVertices (liftedFaces j))) →
        v.val ∈ faceWeights (triangleVertexSet (liftedVertices (liftedFaces j))) →
        squared3 (F (H u) - F (H v)) =
          squared2 (physicalFacePoint second x y m j u.val - physicalFacePoint second x y m j v.val) := by
  obtain ⟨second,z,t,m,hd,ht,hm,hlen,hpos,hreg,_,he⟩ := type6_regular_embeddedFaces x y hx hx' hy hw hU hbase
  let H := type6_intrinsicHomeomorph x (y^2) (sq_pos_of_pos hy)
    (movedIntrinsicPoint second x (y^2) m) hpos
  let E := evaluateTriangles type6FlippedFaces (physicalFoldedVertex second x y m z t)
  refine ⟨second,z,t,m,H,E ∘ H.symm,hd,ht,hm,hreg,he.comp H.symm.isClosedEmbedding,?_,?_,?_⟩
  · intro u
    simp [E]
  · intro j u hu
    change type6_intrinsicHomeomorph x (y^2) _ _ _ u = _
    rw [type6_intrinsicHomeomorph_apply]
    exact type6_project_physicalFacePoint second x y hy.ne' m j u hu
  · intro j u v hu hv
    simpa using type6_weighted_face_metric second x y hy.ne' m z t hlen j u v hu hv

/-- A marked flat torus in the reduced half-domain has an embedded Type 6
origami realization. The homeomorphism supplies the triangulation, and the
folding preserves all distances within each lifted face. -/
theorem type6_origamiTorus (x y : ℝ) (hx : 0 ≤ x) (hx' : x ≤ 1/2)
    (hy : 0 < y) (hw : 1-x^2 ≤ y^2) {U : Set SheetMotion} (hU : IsOpen U) (hbase : 0 ∈ U) :
    ∃ (second : Bool) (z : Vertex → ℝ) (t : ℝ) (m : SheetMotion)
      (H : triangleWeightSpace type6FlippedFaces ≃ₜ MarkedTorus) (F : MarkedTorus → Point3),
      chartDomain second x (y^2) ∧ 0 < t ∧ m ∈ U ∧
      Topology.IsClosedEmbedding F ∧
      (∀ u, F (H u) = evaluateTriangles type6FlippedFaces (physicalFoldedVertex second x y m z t) u) ∧
      (∀ j u, u.val ∈ faceWeights (triangleVertexSet (liftedVertices (liftedFaces j))) →
        H u = projectPeriods (periodCoordinates x y (physicalFacePoint second x y m j u.val))) ∧
      ∀ j u v,
        u.val ∈ faceWeights (triangleVertexSet (liftedVertices (liftedFaces j))) →
        v.val ∈ faceWeights (triangleVertexSet (liftedVertices (liftedFaces j))) →
        squared3 (F (H u) - F (H v)) =
          squared2 (physicalFacePoint second x y m j u.val - physicalFacePoint second x y m j v.val) := by
  obtain ⟨second,z,t,m,H,F,hd,ht,hm,_,hemb,hfold,hproj,hmetric⟩ :=
    type6_regular_origamiTorus x y hx hx' hy hw hU hbase
  exact ⟨second,z,t,m,H,F,hd,ht,hm,hemb,hfold,hproj,hmetric⟩

end OrigamiTorus
