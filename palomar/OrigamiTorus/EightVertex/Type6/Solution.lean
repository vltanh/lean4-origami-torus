module

public import OrigamiTorus.EightVertex.Type6.Universal
import Mathlib.Topology.MetricSpace.Pseudo.Pi

public section

namespace OrigamiTorusType6Challenge

open OrigamiTorus

/-- A Type 6 realization for every flat lattice torus, regular for the joint angle and marked modulus map. -/
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
        Type5.squared3 (F (H u) - F (H v)) =
          dist (∑ i, u.val i • P f i) (∑ i, v.val i • P f i)^2 := by
  exact OrigamiTorus.type6_regular_universal a b ha hb

end OrigamiTorusType6Challenge
