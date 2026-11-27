module

public import OrigamiTorus.EightVertex.Type3.Universal

public section

namespace OrigamiTorusType3Challenge

open OrigamiTorus

/-- Every flat lattice torus has a piecewise-isometric Type 3 embedding. -/
theorem type3_universal (a b : ℂ) (ha : a ≠ 0) (hb : (b/a).im ≠ 0) :
    ∃ (H : triangleWeightSpace type3Faces ≃ₜ ComplexTorus a b)
      (F : ComplexTorus a b → Point3) (Q : Vertex → Point3) (P : Triangle → Vertex → ℂ),
      Topology.IsClosedEmbedding F ∧
      (∀ u, F (H u) = evaluateTriangles type3Faces Q u) ∧
      (∀ f ∈ type3Faces, ∀ u, u.val ∈ faceWeights (triangleVertexSet f) →
        H u = complexTorusProjection a b (∑ i, u.val i • P f i)) ∧
      ∀ f ∈ type3Faces, ∀ u v,
        u.val ∈ faceWeights (triangleVertexSet f) →
        v.val ∈ faceWeights (triangleVertexSet f) →
        Type5.squared3 (F (H u) - F (H v)) =
          dist (∑ i, u.val i • P f i) (∑ i, v.val i • P f i)^2 :=
  Type3.universal a b ha hb

end OrigamiTorusType3Challenge
