module

public import OrigamiTorus.EightVertex.Type5.OffRayBase
public import OrigamiTorus.EightVertex.Type5.SharpRaySeparation
public import OrigamiTorus.EightVertex.Type5.PositiveCycle

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
closed box adjoining the square. -/
theorem type5_nonrectangular_box (x y : ℝ)
    (hx : x ∈ Set.Icc 0 ((1 / 512)^4))
    (hy : y ∈ Set.Icc 1 (1 + (1 / 512)^4)) :
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

/-- An oblique box about the off-ray base modulus (1+i√31)/4. -/
theorem type5_oblique_box (x y : ℝ) (hy : 0 < y)
    (hx : x ∈ Set.Icc (1/4 - 1/2^80) (1/4 + 1/2^80))
    (hv : y^2 ∈ Set.Icc (31/16 - 1/2^80) (31/16 + 1/2^80)) :
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
  have box : Type5.OffRayBase.Box x (y^2) := by
    simpa only [Type5.OffRayBase.Box, Type5.OffRayBase.radius, Rat.cast_sub, Rat.cast_add,
      Rat.cast_div, Rat.cast_one, Rat.cast_pow, Rat.cast_ofNat] using And.intro hx hv
  obtain ⟨H,F,P,hE,hfold,hproj,hmetric⟩ := Type5.OffRayBase.torus_by_faces hy box
  exact ⟨H,F,(Type5.OffRayBase.chart x (y^2)).extrinsic,P,hE,hfold,hproj,hmetric⟩

/-- The off-ray determinant signs separate the labeled spatial complex. -/
theorem type5_off_ray_separation (r : Vertex → Point3) :
    let fs : List Triangle :=
      [(0,1,2), (0,3,1), (0,2,4), (0,5,3), (0,4,5), (1,5,2), (1,3,6), (1,6,4),
        (1,4,7), (1,7,5), (2,6,3), (2,3,7), (2,7,4), (2,5,6), (3,5,7), (4,6,5)]
    let B (a b c d : Vertex) := affineBracket (r a) (r b) (r c) (r d)
    B 1 2 3 4 < 0 ∧ 0 < B 1 2 3 5 ∧ B 1 2 4 5 < 0 ∧
      B 1 3 4 5 < 0 ∧ 0 < B 2 3 4 5 ∧ 0 < B 0 1 2 5 ∧
      B 0 1 3 5 < 0 ∧ B 0 2 3 4 < 0 ∧ 0 < B 0 2 4 5 ∧
      B 1 2 3 6 < 0 ∧ 0 < B 1 2 4 7 ∧ B 1 3 5 7 < 0 ∧
      B 2 3 5 7 < 0 ∧ B 2 4 5 6 < 0 ∧ 0 < B 0 2 4 6 ∧
      0 < B 0 4 5 6 ∧ B 2 3 6 7 < 0 →
      Topology.IsClosedEmbedding (evaluateTriangles fs r) := by
  dsimp only
  rintro ⟨s1234, s1235, s1245, s1345, s2345, s0125, s0135, s0234,
    s0245, s1236, s1247, s1357, s2357, s2456, s0246, s0456,
    s2367⟩
  apply Type5.OffRay.spatial_embedding
  constructor <;> assumption

/-- The sharp-ray determinant signs separate the labeled spatial complex. -/
theorem type5_sharp_ray_separation (r : Vertex → Point3) :
    let fs : List Triangle :=
      [(0,1,2), (0,3,1), (0,2,4), (0,5,3), (0,4,5), (1,5,2), (1,3,6), (1,6,4),
        (1,4,7), (1,7,5), (2,6,3), (2,3,7), (2,7,4), (2,5,6), (3,5,7), (4,6,5)]
    let B (a b c d : Vertex) := affineBracket (r a) (r b) (r c) (r d)
    0 < B 0 1 2 5 ∧ 0 < B 0 1 2 6 ∧ B 0 1 3 4 < 0 ∧
      B 0 1 3 6 < 0 ∧ B 0 2 3 4 < 0 ∧ 0 < B 1 2 3 4 ∧
      B 1 2 3 6 < 0 ∧ 0 < B 1 2 3 7 ∧ 0 < B 1 2 4 5 ∧
      B 1 3 4 5 < 0 ∧ 0 < B 1 3 5 6 ∧ B 1 3 5 7 < 0 ∧
      0 < B 1 4 5 6 ∧ 0 < B 2 3 4 5 ∧ B 2 3 4 7 < 0 ∧
      B 2 4 5 6 < 0 ∧ B 2 4 6 7 < 0 →
      Topology.IsClosedEmbedding (evaluateTriangles fs r) := by
  dsimp only
  rintro ⟨s0125, s0126, s0134, s0136, s0234, s1234, s1236, s1237,
    s1245, s1345, s1356, s1357, s1456, s2345, s2347, s2456,
    s2467⟩
  apply Type5.SharpRay.spatial_embedding
  constructor <;> assumption

/-- A five-cycle of strict squared-distance deficits determines two completions of the leaf. -/
theorem type5_leaf_completions (K : Fin 5 → Type5.MixedPoint) {a b c d e : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (he : 0 < e)
    (hK : ∀ i j, Type5.mixedDot (K i-K j) (K i-K j) = -2*Type5.pentagonGram a b c d e i j) :
    ∃ p q : Type5.MixedPoint, p ≠ q ∧ ∀ z : Type5.MixedPoint,
      (∀ i, Type5.mixedDot (K i-z) (K i-z) = 0) ↔ z = p ∨ z = q := by
  exact Type5.positive_cycle_completions K ha hb hc hd he hK

end OrigamiTorusType5Challenge
