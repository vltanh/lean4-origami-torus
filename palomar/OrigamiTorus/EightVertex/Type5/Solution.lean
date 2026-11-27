module

public import OrigamiTorus.EightVertex.Type5.ContinuationTorus

public section

namespace OrigamiTorusType5Challenge

open OrigamiTorus

/-- The unit square lattice torus has a piecewise-isometric Type 5 embedding. -/
theorem type5_square :
    let a : ℂ := 1
    let b : ℂ := Complex.I
    let fs : List Triangle :=
      [(0,1,2), (0,3,1), (0,2,4), (0,5,3), (0,4,5), (1,5,2), (1,3,6), (1,6,4),
        (1,4,7), (1,7,5), (2,6,3), (2,3,7), (2,7,4), (2,5,6), (3,5,7), (4,6,5)]
    ∃ (H : triangleWeightSpace fs ≃ₜ ComplexTorus a b)
      (F : ComplexTorus a b → Point3) (Q : Vertex → Point3) (P : Triangle → Vertex → ℂ),
      Topology.IsClosedEmbedding F ∧
      (∀ u, F (H u) = evaluateTriangles fs Q u) ∧
      (∀ f ∈ fs, ∀ u, u.val ∈ faceWeights (triangleVertexSet f) →
        H u = complexTorusProjection a b (∑ i, u.val i • P f i)) ∧
      ∀ f ∈ fs, ∀ u v,
        u.val ∈ faceWeights (triangleVertexSet f) →
        v.val ∈ faceWeights (triangleVertexSet f) →
        Type5.squared3 (F (H u) - F (H v)) =
          dist (∑ i, u.val i • P f i) (∑ i, v.val i • P f i)^2 := by
  obtain ⟨H,F,P,hE,hfold,hproj,hmetric⟩ := Type5.square_complex_by_faces
  exact ⟨H,F,Type5.squareExtrinsic,P,hE,hfold,hproj,hmetric⟩

/-- The same Type 5 face complex realizes every lattice torus in the specified
closed nonrectangular modulus box. -/
theorem type5_nonrectangular_box (x y : ℝ)
    (hx : x ∈ Set.Icc (174241221608834/10^15) (174241221628834/10^15))
    (hy : y ∈ Set.Icc (1084897889745590/10^15) (1084897889765590/10^15)) :
    let a : ℂ := 1
    let b : ℂ := x+y*Complex.I
    let fs : List Triangle :=
      [(0,1,2), (0,3,1), (0,2,4), (0,5,3), (0,4,5), (1,5,2), (1,3,6), (1,6,4),
        (1,4,7), (1,7,5), (2,6,3), (2,3,7), (2,7,4), (2,5,6), (3,5,7), (4,6,5)]
    ∃ (H : triangleWeightSpace fs ≃ₜ ComplexTorus a b)
      (F : ComplexTorus a b → Point3) (Q : Vertex → Point3) (P : Triangle → Vertex → ℂ),
      Topology.IsClosedEmbedding F ∧
      (∀ u, F (H u) = evaluateTriangles fs Q u) ∧
      (∀ f ∈ fs, ∀ u, u.val ∈ faceWeights (triangleVertexSet f) →
        H u = complexTorusProjection a b (∑ i, u.val i • P f i)) ∧
      ∀ f ∈ fs, ∀ u v,
        u.val ∈ faceWeights (triangleVertexSet f) →
        v.val ∈ faceWeights (triangleVertexSet f) →
        Type5.squared3 (F (H u) - F (H v)) =
          dist (∑ i, u.val i • P f i) (∑ i, v.val i • P f i)^2 := by
  obtain ⟨H,F,P,hE,hfold,hproj,hmetric⟩ :=
    Type5.Continuation.torus_by_faces (x := x) (y := y) ⟨hx,hy⟩
  exact ⟨H,F,Type5.Continuation.extrinsic x y,P,hE,hfold,hproj,hmetric⟩

end OrigamiTorusType5Challenge
