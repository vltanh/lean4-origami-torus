module

public import OrigamiTorus.EightVertex.Type7.WideLift

public section

namespace OrigamiTorusType7Challenge

open OrigamiTorus

/-- Every reduced modulus off the sharp-rhombic ray admits a
piecewise-isometric Type 7 embedding. -/
theorem type7_open_strip (x w : ℝ) (hx : 0 ≤ x) (hx' : x < 1/2) (hw : 1-x^2 ≤ w) :
    let a : ℂ := 1
    let b : ℂ := x+Real.sqrt w*Complex.I
    let fs : List Triangle :=
      [(3,5,6), (3,2,5), (3,6,4), (3,0,2), (3,4,1), (3,1,0), (5,0,6), (5,2,4),
        (5,4,7), (5,7,0), (6,7,4), (6,0,1), (6,1,7), (2,1,4), (2,0,7), (2,7,1)]
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
  exact Type7.chart_by_faces false 1 _ (Type7.open_strip_realizes hx hx' hw)

/-- Every rectangular flat torus has a piecewise-isometric Type 7 embedding. -/
theorem type7_rectangular (a b : ℂ) (ha : a ≠ 0) (hb : b ≠ 0) (ho : (b/a).re = 0) :
    let fs : List Triangle :=
      [(3,5,6), (3,2,5), (3,6,4), (3,0,2), (3,4,1), (3,1,0), (5,0,6), (5,2,4),
        (5,4,7), (5,7,0), (6,7,4), (6,0,1), (6,1,7), (2,1,4), (2,0,7), (2,7,1)]
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
          dist (∑ i, u.val i • P f i) (∑ i, v.val i • P f i)^2 :=
  Type7.rectangular_by_faces a b ha hb ho

end OrigamiTorusType7Challenge
