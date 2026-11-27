module

public import OrigamiTorus.EightVertex.Type4.WideLift

public section

namespace OrigamiTorusType4Challenge

open OrigamiTorus

/-- Type 4 admits a piecewise-isometric embedding for every normalized modulus
in the open strip. The labels are those of the flipped Type 7 chart. -/
theorem type4_open_strip (x w : ℝ) (hx : 0 ≤ x) (hx' : x < 1/2) (hw : 1-x^2 ≤ w) :
    let a : ℂ := 1
    let b : ℂ := x+Real.sqrt w*Complex.I
    let fs : List Triangle :=
      [(3,6,4), (3,0,2), (3,4,1), (3,1,0), (5,0,6), (5,2,4), (5,4,7), (5,7,0),
        (6,7,4), (6,0,1), (6,1,7), (2,1,4), (2,0,7), (2,7,1), (6,3,2), (6,2,5)]
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
  exact Type7.chart_by_faces true 1 _ (Type4.open_strip_realizes hx hx' hw)

end OrigamiTorusType4Challenge
