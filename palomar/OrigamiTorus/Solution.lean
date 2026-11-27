module

public import OrigamiTorus.Defs
public import OrigamiTorus.Geometry.SpatialRealizations
public import OrigamiTorus.Type1.Nonexistence
public import OrigamiTorus.Type2.Nonexistence
public import OrigamiTorus.Type3.Universal
public import OrigamiTorus.Type4.WideLift
public import OrigamiTorus.Type5.Periodic
public import OrigamiTorus.Type6.Inflation
public import OrigamiTorus.Type6.Universal
public import OrigamiTorus.Type7.Tiling
import OrigamiTorus.Type2.Certificate
import OrigamiTorus.Type2.Perturbation
import OrigamiTorus.Type6.Signs
import Mathlib.Topology.MetricSpace.Pseudo.Pi

public section

namespace OrigamiTorusChallenge

open OrigamiTorus

/-- Every embedded Lutz Type 1 realization has a vertex with nonzero angle defect. -/
theorem type1_nonexistence (q : Vertex → Point3)
    (h : Function.Injective (evaluateTriangles Type1.faces q)) :
    ¬ ∀ v, coneAngles Type1.faces (Type2.euclideanPoint ∘ q) v = 2 * Real.pi :=
  Type1.nonexistence q h

/-- No assignment satisfies the Type 2 determinant-sign formula. -/
theorem type2_sign_obstruction (a : Nat → Bool) :
    ¬ ∀ c ∈ OrigamiTorus.Type2.signClauses, ∃ l ∈ c, a l.1 = l.2 :=
  OrigamiTorus.Type2.type2_signsImpossible a

/-- Every embedded Lutz Type 2 realization has a vertex with nonzero angle defect. -/
theorem type2_nonexistence (q : Vertex → Point3)
    (h : Function.Injective (evaluateTriangles Type2.geometricFaces q)) :
    ¬ ∀ v, ((Type2.incidentCorners v).map (Type2.cornerAngle q v)).sum = 2 * Real.pi := by
  intro hflat
  apply Type2.type2_nonexistence q h
  intro v
  rw [Type2.linkPerimeter_eq_coneAngle]
  exact hflat v

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

/-- Both diagonals separate the respective opposite vertices on the entire chart. -/
theorem type6_diagonal_signs (second : Bool) (x w : ℝ) (hd : chartDomain second x w) :
    let p := stripPoint second x w
    0 < area p 1 2 0 ∧ area p 1 2 5 < 0 ∧ area p 0 5 1 < 0 ∧ 0 < area p 0 5 2 :=
  OrigamiTorus.type6_flipSigns second x w hd

/-- An inflated generic lift matches all twenty-four intrinsic squared edge lengths
while the lattice periods stay fixed. -/
theorem type6_length_matched_lift (x w : ℝ) (hx : 0 ≤ x) (hx' : x ≤ 1 / 2) (hw : 1 - x^2 ≤ w)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (second : Bool) (z : Vertex → ℝ) (t : ℝ) (m : SheetMotion),
      chartDomain second x w ∧ 0 < t ∧ (∀ i, |m i| < ε) ∧
      lengthResidual second x w z (t,m) = 0 ∧
      GenericLift (movedFoldedPoint second x w m) (fun v => t * z v) ∧
      ∀ pair ∈ type6DisjointPairs,
        isSeparated (movedFoldedPoint second x w m) (fun v => t * z v) pair := by
  let U : Set SheetMotion := Metric.ball 0 ε
  have hbase : (0 : SheetMotion) ∈ U := Metric.mem_ball_self hε
  have hsmall (m : SheetMotion) (hm : m ∈ U) : ∀ i, |m i| < ε := by
    have hcoords := (dist_pi_lt_iff hε).mp (show dist m (0 : SheetMotion) < ε from hm)
    intro i
    simpa [Real.dist_eq] using hcoords i
  by_cases h : x ≤ 1 / 6
  · have hd : chartDomain false x w := ⟨hx, h, hw⟩
    obtain ⟨z, t, m, ht, hm, hp⟩ :=
      OrigamiTorus.type6_lengthMatchedLift false x w hd Metric.isOpen_ball hbase
    exact ⟨false, z, t, m, hd, ht, hsmall m hm, hp⟩
  · have hd : chartDomain true x w := ⟨le_of_lt (lt_of_not_ge h), hx', hw⟩
    obtain ⟨z, t, m, ht, hm, hp⟩ :=
      OrigamiTorus.type6_lengthMatchedLift true x w hd Metric.isOpen_ball hbase
    exact ⟨true, z, t, m, hd, ht, hsmall m hm, hp⟩

/-- An embedding can be perturbed to general position inside any open set of placements. -/
theorem generic_embedded_perturbation (fs : List Triangle) (q : Vertex → Point3)
    {U : Set (Vertex → Point3)} (hU : IsOpen U) (hq : q ∈ U)
    (h : Function.Injective (evaluateTriangles fs q)) :
    ∃ v ∈ U, Function.Injective (evaluateTriangles fs v) ∧
      GenericLift (fun i => ((v i).1,(v i).2.1)) (fun i => (v i).2.2) :=
  exists_generic_embedded_placement fs q hU hq h

/-- The length-matched Type 6 configuration embeds the labeled triangles in Euclidean space. -/
theorem type6_spatial_embedding_lift (x y : ℝ) (hx : 0 ≤ x) (hx' : x ≤ 1/2)
    (hy : 0 < y) (hw : 1-x^2 ≤ y^2) {U : Set SheetMotion} (hU : IsOpen U) (hbase : 0 ∈ U) :
    ∃ (second : Bool) (z : Vertex → ℝ) (t : ℝ) (m : SheetMotion),
      chartDomain second x (y^2) ∧ 0 < t ∧ m ∈ U ∧ lengthResidual second x (y^2) z (t,m) = 0 ∧
      Topology.IsClosedEmbedding (evaluateTriangles type6FlippedFaces (physicalFoldedVertex second x y m z t)) := by
  obtain ⟨second,z,t,m,hchart,ht,hm,hlen,_,hemb⟩ := type6_embeddedFaces x y hx hx' hy hw hU hbase
  exact ⟨second,z,t,m,hchart,ht,hm,hlen,hemb⟩

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
        Type5.squared3 (F (H u) - F (H v)) =
          dist (∑ i, u.val i • P f i) (∑ i, v.val i • P f i)^2 :=
  OrigamiTorus.type6_universal a b ha hb

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

end OrigamiTorusChallenge
