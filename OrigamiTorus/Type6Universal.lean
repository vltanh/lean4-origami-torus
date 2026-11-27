module

public import OrigamiTorus.Type6Tiling
public import OrigamiTorus.LatticeTorus
import Mathlib.Topology.Algebra.ConstMulAction
import Mathlib.Tactic

/-! Transporting the Type 6 construction to any rank-two plane lattice. -/

public section

open scoped ComplexConjugate

namespace OrigamiTorus

open Type5 (squared2 squared3)

private theorem complex_plane_dist_sq (p q : ℝ × ℝ) :
    dist (Complex.equivRealProdCLM.symm p) (Complex.equivRealProdCLM.symm q)^2 = squared2 (p-q) := by
  rw [dist_eq_norm, ← map_sub, Complex.sq_norm, Complex.equivRealProdCLM_symm_apply]
  simp [Complex.normSq_apply,squared2,Type5.dot]

/-- Every rank-two plane lattice has a Type 6 origami torus. The homeomorphism
identifies the labeled triangles with the intrinsic torus. Both the intrinsic
map and the spatial embedding are affine in barycentric coordinates on each
face, and the embedding preserves Euclidean triangle distances. -/
theorem type6_regular_universal_lifted (a b : ℂ) (ha : a ≠ 0) (hb : (b/a).im ≠ 0) :
    ∃ (H : triangleWeightSpace type6FlippedFaces ≃ₜ ComplexTorus a b)
      (F : ComplexTorus a b → Point3) (Q : Vertex → Point3) (P : Fin 16 → Vertex → ℂ),
      Type6SpatiallyRegular Q ∧ Topology.IsClosedEmbedding F ∧
      (∀ u, F (H u) = evaluateTriangles type6FlippedFaces Q u) ∧
      (∀ j u, u.val ∈ faceWeights (triangleVertexSet (liftedVertices (liftedFaces j))) →
        H u = complexTorusProjection a b (∑ i, u.val i • P j i)) ∧
      ∀ j u v,
        u.val ∈ faceWeights (triangleVertexSet (liftedVertices (liftedFaces j))) →
        v.val ∈ faceWeights (triangleVertexSet (liftedVertices (liftedFaces j))) →
        squared3 (F (H u) - F (H v)) =
          dist (∑ i, u.val i • P j i) (∑ i, v.val i • P j i)^2 := by
  obtain ⟨x,y,D,refl,hx,hx',hy,hw,hD,hL⟩ := reduced_complex_lattice a b ha hb
  obtain ⟨J,hJ⟩ := complexTorus_rebase a b x y hy.ne' D refl hD hL
  obtain ⟨second,z,t,m,H₀,F₀,_,_,_,hreg,hE,hfold,hproj,hmetric⟩ :=
    type6_regular_origamiTorus x y hx hx' hy hw (U := Set.univ) isOpen_univ (Set.mem_univ _)
  let S : Point3 ≃ₜ Point3 := Homeomorph.smulOfNeZero ‖D‖ (norm_ne_zero_iff.mpr hD)
  let H := H₀.trans J
  let F := S ∘ F₀ ∘ J.symm
  let Q (i : Vertex) := ‖D‖ • physicalFoldedVertex second x y m z t i
  let P (j : Fin 16) (i : Vertex) := complexSimilarity D refl
    (Complex.equivRealProdCLM.symm (physicalIntrinsicCorner second x y m (i,facePeriod (liftedFaces j) i)))
  have hP (j : Fin 16) (u : Vertex → ℝ) : (∑ i, u i • P j i) = complexSimilarity D refl
      (Complex.equivRealProdCLM.symm (physicalFacePoint second x y m j u)) := by
    let L := (complexSimilarityLinear D refl).comp Complex.equivRealProdCLM.symm.toLinearEquiv.toLinearMap
    change (∑ i, u i • L (physicalIntrinsicCorner second x y m (i,facePeriod (liftedFaces j) i))) =
      L (∑ i, u i • physicalIntrinsicCorner second x y m (i,facePeriod (liftedFaces j) i))
    simp only [map_sum,map_smul]
  refine ⟨H,F,Q,P,hreg.smul (norm_ne_zero_iff.mpr hD),S.isClosedEmbedding.comp (hE.comp J.symm.isClosedEmbedding),?_,?_,?_⟩
  · intro u
    change S (F₀ (J.symm (J (H₀ u)))) = _
    rw [J.symm_apply_apply,hfold]
    let L : Point3 →ₗ[ℝ] Point3 := ‖D‖ • LinearMap.id
    exact (congrFun (evaluateTriangles_comp_linear type6FlippedFaces
      (physicalFoldedVertex second x y m z t) L) u).symm
  · intro j u hu
    change J (H₀ u) = _
    rw [hP,hproj j u hu,hJ]
  · intro j u v hu hv
    change squared3 (S (F₀ (J.symm (J (H₀ u)))) - S (F₀ (J.symm (J (H₀ v))))) = _
    rw [J.symm_apply_apply,J.symm_apply_apply,hP,hP]
    change squared3 (‖D‖ • F₀ (H₀ u) - ‖D‖ • F₀ (H₀ v)) = _
    rw [← smul_sub,squared3_smul,hmetric j u v hu hv]
    let p := Complex.equivRealProdCLM.symm (physicalFacePoint second x y m j u.val)
    let q := Complex.equivRealProdCLM.symm (physicalFacePoint second x y m j v.val)
    change _ = dist (complexSimilarity D refl p) (complexSimilarity D refl q)^2
    rw [show dist (complexSimilarity D refl p) (complexSimilarity D refl q) = ‖D‖*dist p q
        from complex_similarity_dist D refl p q,
      mul_pow, complex_plane_dist_sq]

/-- Every rank-two plane lattice has a Type 6 origami torus. The homeomorphism
identifies the labeled triangles with the intrinsic torus. Both the intrinsic
map and the spatial embedding are affine in barycentric coordinates on each
face, and the embedding preserves Euclidean triangle distances. -/
theorem type6_universal_lifted (a b : ℂ) (ha : a ≠ 0) (hb : (b/a).im ≠ 0) :
    ∃ (H : triangleWeightSpace type6FlippedFaces ≃ₜ ComplexTorus a b)
      (F : ComplexTorus a b → Point3) (Q : Vertex → Point3) (P : Fin 16 → Vertex → ℂ),
      Topology.IsClosedEmbedding F ∧
      (∀ u, F (H u) = evaluateTriangles type6FlippedFaces Q u) ∧
      (∀ j u, u.val ∈ faceWeights (triangleVertexSet (liftedVertices (liftedFaces j))) →
        H u = complexTorusProjection a b (∑ i, u.val i • P j i)) ∧
      ∀ j u v,
        u.val ∈ faceWeights (triangleVertexSet (liftedVertices (liftedFaces j))) →
        v.val ∈ faceWeights (triangleVertexSet (liftedVertices (liftedFaces j))) →
        squared3 (F (H u) - F (H v)) =
          dist (∑ i, u.val i • P j i) (∑ i, v.val i • P j i)^2 := by
  obtain ⟨H,F,Q,P,_,hemb,hfold,hproj,hmetric⟩ := type6_regular_universal_lifted a b ha hb
  exact ⟨H,F,Q,P,hemb,hfold,hproj,hmetric⟩

/-- Every flat lattice torus has a piecewise-isometric Type 6 embedding at which the spatial angle and marked modulus map has rank nine. -/
theorem type6_regular_universal (a b : ℂ) (ha : a ≠ 0) (hb : (b/a).im ≠ 0) :
    ∃ (H : triangleWeightSpace type6FlippedFaces ≃ₜ ComplexTorus a b)
      (F : ComplexTorus a b → Point3) (Q : Vertex → Point3) (P : Triangle → Vertex → ℂ),
      Type6SpatiallyRegular Q ∧ Topology.IsClosedEmbedding F ∧
      (∀ u, F (H u) = evaluateTriangles type6FlippedFaces Q u) ∧
      (∀ f ∈ type6FlippedFaces, ∀ u, u.val ∈ faceWeights (triangleVertexSet f) →
        H u = complexTorusProjection a b (∑ i, u.val i • P f i)) ∧
      ∀ f ∈ type6FlippedFaces, ∀ u v,
        u.val ∈ faceWeights (triangleVertexSet f) →
        v.val ∈ faceWeights (triangleVertexSet f) →
        squared3 (F (H u) - F (H v)) =
          dist (∑ i, u.val i • P f i) (∑ i, v.val i • P f i)^2 := by
  classical
  obtain ⟨H,F,Q,P,hreg,hE,hfold,hproj,hmetric⟩ := type6_regular_universal_lifted a b ha hb
  have exists_lift (f : Triangle) (hf : f ∈ type6FlippedFaces) :
      ∃ j : Fin 16, liftedVertices (liftedFaces j) = f := by
    rw [← type6_liftedSidesPair.1,List.map_map] at hf
    obtain ⟨j,_,hj⟩ := List.mem_map.mp hf
    exact ⟨j,hj⟩
  let index (f : Triangle) := if hf : f ∈ type6FlippedFaces then (exists_lift f hf).choose else 0
  have hindex (f : Triangle) (hf : f ∈ type6FlippedFaces) :
      liftedVertices (liftedFaces (index f)) = f := by
    simp only [index,dite_eq_left hf]
    exact (exists_lift f hf).choose_spec
  refine ⟨H,F,Q,P ∘ index,hreg,hE,hfold,?_,?_⟩
  · intro f hf u hu
    exact hproj (index f) u (by simpa only [hindex f hf] using hu)
  · intro f hf u v hu hv
    exact hmetric (index f) u v (by simpa only [hindex f hf] using hu)
      (by simpa only [hindex f hf] using hv)

/-- Every flat lattice torus has a piecewise-isometric Type 6 embedding. -/
theorem type6_universal (a b : ℂ) (ha : a ≠ 0) (hb : (b/a).im ≠ 0) :
    ∃ (H : triangleWeightSpace type6FlippedFaces ≃ₜ ComplexTorus a b)
      (F : ComplexTorus a b → Point3) (Q : Vertex → Point3) (P : Triangle → Vertex → ℂ),
      Topology.IsClosedEmbedding F ∧
      (∀ u, F (H u) = evaluateTriangles type6FlippedFaces Q u) ∧
      (∀ f ∈ type6FlippedFaces, ∀ u, u.val ∈ faceWeights (triangleVertexSet f) →
        H u = complexTorusProjection a b (∑ i, u.val i • P f i)) ∧
      ∀ f ∈ type6FlippedFaces, ∀ u v,
        u.val ∈ faceWeights (triangleVertexSet f) →
        v.val ∈ faceWeights (triangleVertexSet f) →
        squared3 (F (H u) - F (H v)) =
          dist (∑ i, u.val i • P f i) (∑ i, v.val i • P f i)^2 := by
  obtain ⟨H,F,Q,P,_,hemb,hfold,hproj,hmetric⟩ := type6_regular_universal a b ha hb
  exact ⟨H,F,Q,P,hemb,hfold,hproj,hmetric⟩

end OrigamiTorus
