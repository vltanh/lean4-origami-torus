module

public import OrigamiTorus.Geometry.TriangleIntersections
public import OrigamiTorus.EightVertex.Type5.Square
public import OrigamiTorus.EightVertex.Type6.FaceMetric
public import OrigamiTorus.EightVertex.Type6.Regularity
public import OrigamiTorus.EightVertex.Type7.Rectangular
import Mathlib.Tactic

/-! Geometric simplicial complexes for the certified spatial configurations. -/

namespace OrigamiTorus

private theorem disjoint_endpoints {e : Edge} {f : Triangle}
    (hd : Disjoint ({e.1,e.2} : Finset Vertex) (triangleVertexSet f)) :
    !(triangleVertices f).contains e.1 && !(triangleVertices f).contains e.2 = true := by
  rw [Finset.disjoint_left] at hd
  have h₁ : e.1 ∉ triangleVertices f := fun h =>
    hd (by simp) ((mem_triangleVertexSet _ _).mpr h)
  have h₂ : e.2 ∉ triangleVertices f := fun h =>
    hd (by simp) ((mem_triangleVertexSet _ _).mpr h)
  simp [h₁, h₂]

public theorem mem_disjointTests {fs : List Triangle} {e : Edge} {f : Triangle}
    (he : e ∈ fs.flatMap faceEdges) (hf : f ∈ fs)
    (hd : Disjoint ({e.1,e.2} : Finset Vertex) (triangleVertexSet f)) :
    (e,f) ∈ (fs.flatMap faceEdges).eraseDups.flatMap (fun e =>
      (fs.filter fun f => !(triangleVertices f).contains e.1 &&
        !(triangleVertices f).contains e.2).map (e, ·)) :=
  List.mem_flatMap.mpr ⟨e, List.mem_eraseDups.mpr he,
    List.mem_map.mpr ⟨f, List.mem_filter.mpr ⟨hf, disjoint_endpoints hd⟩, rfl⟩⟩

public theorem type6_edgeTriangleSeparated (p : Vertex → ℝ × ℝ) (z : Vertex → ℝ)
    (hg : GenericLift p z) (hs : ∀ pair ∈ type6DisjointPairs, isSeparated p z pair) :
    EdgeTriangleSeparated (fun i => ((p i).1,(p i).2,z i)) type6FlippedFaces := by
  rintro ⟨a,b⟩ he ⟨c,d,g⟩ hf hi
  have hm : ((a,b),(c,d,g)) ∈ type6DisjointPairs := by
    simpa only [type6DisjointPairs, Bool.not_or] using mem_disjointTests he hf hi
  rw [vertexHull_pair, vertexHull_triangle]
  exact type6_disjoint_edge_face p z a b c d g hm hg (hs _ hm)

/-- The fixed-period lift retains the exact labeled face complex in space. -/
public theorem type6_spatialLengthMatchedLift_regular (second : Bool) (x w : ℝ) (hd : chartDomain second x w)
    {U : Set SheetMotion} (hU : IsOpen U) (hbase : 0 ∈ U) :
    ∃ (z : Vertex → ℝ) (t : ℝ) (m : SheetMotion)
      (K : Geometry.SimplicialComplex ℝ Point3),
      0 < t ∧ m ∈ U ∧ lengthResidual second x w z (t,m) = 0 ∧
      ((fderiv ℝ (lengthResidual second x w z) (t,m)).comp
        (ContinuousLinearMap.inr ℝ ℝ SheetMotion)).IsInvertible ∧
      (∀ f : Fin 16, 0 < periodicFaceArea x w (movedIntrinsicPoint second x w m) (liftedFaces f)) ∧
      K.faces = ((triangleComplex type6FlippedFaces).map (fun i =>
        ((movedFoldedPoint second x w m i).1,(movedFoldedPoint second x w m i).2,t*z i))).faces ∧
      Topology.IsClosedEmbedding (evaluateTriangles type6FlippedFaces (fun i =>
        ((movedFoldedPoint second x w m i).1,(movedFoldedPoint second x w m i).2,t*z i))) := by
  obtain ⟨z,t,m,ht,hm,hlen,hi,hpos,hg,hs⟩ := type6_orientedLengthMatchedLift_regular second x w hd hU hbase
  let p := movedFoldedPoint second x w m
  let h (i : Vertex) := t*z i
  have hsep := type6_edgeTriangleSeparated p h hg hs
  exact ⟨z,t,m,spatialTriangleComplex p h _ hg hsep,ht,hm,hlen,hi,hpos,
    spatialTriangleComplex_faces p h _ hg hsep, spatialTriangles_isClosedEmbedding p h _ hg hsep⟩

/-- The fixed-period lift retains the exact labeled face complex in space. -/
public theorem type6_spatialLengthMatchedLift (second : Bool) (x w : ℝ) (hd : chartDomain second x w)
    {U : Set SheetMotion} (hU : IsOpen U) (hbase : 0 ∈ U) :
    ∃ (z : Vertex → ℝ) (t : ℝ) (m : SheetMotion)
      (K : Geometry.SimplicialComplex ℝ Point3),
      0 < t ∧ m ∈ U ∧ lengthResidual second x w z (t,m) = 0 ∧
      (∀ f : Fin 16, 0 < periodicFaceArea x w (movedIntrinsicPoint second x w m) (liftedFaces f)) ∧
      K.faces = ((triangleComplex type6FlippedFaces).map (fun i =>
        ((movedFoldedPoint second x w m i).1,(movedFoldedPoint second x w m i).2,t*z i))).faces ∧
      Topology.IsClosedEmbedding (evaluateTriangles type6FlippedFaces (fun i =>
        ((movedFoldedPoint second x w m i).1,(movedFoldedPoint second x w m i).2,t*z i))) := by
  obtain ⟨z,t,m,K,ht,hm,hlen,_,hpos,hfaces,hemb⟩ :=
    type6_spatialLengthMatchedLift_regular second x w hd hU hbase
  exact ⟨z,t,m,K,ht,hm,hlen,hpos,hfaces,hemb⟩

public theorem fixedPeriod_physical_embedding (fs : List Triangle) (second : Bool) (x y : ℝ) (z : Vertex → ℝ) (t : ℝ)
    (m : SheetMotion) (hy : y ≠ 0)
    (h : Topology.IsClosedEmbedding (evaluateTriangles fs (fun i =>
      ((movedFoldedPoint second x (y^2) m i).1,(movedFoldedPoint second x (y^2) m i).2,t*z i)))) :
    Topology.IsClosedEmbedding (evaluateTriangles fs (physicalFoldedVertex second x y m z t)) := by
  let scale : Point3 →ₗ[ℝ] Point3 :=
    { toFun := fun v => (v.1,v.2.1/y,v.2.2)
      map_add' := by intro a b; ext <;> simp [add_div]
      map_smul' := by
        intro r v
        have hs (a : Point3) : r • a = (r*a.1,r*a.2.1,r*a.2.2) := rfl
        simp [hs,mul_div_assoc] }
  have hscale : Function.Injective scale := by
    intro a b e
    change (a.1,a.2.1/y,a.2.2) = (b.1,b.2.1/y,b.2.2) at e
    obtain ⟨h₁,h⟩ := Prod.mk.inj e
    obtain ⟨h₂,h₃⟩ := Prod.mk.inj h
    exact Prod.ext h₁ (Prod.ext ((div_left_inj₀ hy).mp h₂) h₃)
  have hcont : Continuous scale := by
    change Continuous (fun v : Point3 => (v.1,v.2.1/y,v.2.2))
    fun_prop
  let _ : CompactSpace (triangleWeightSpace fs) :=
    isCompact_iff_compactSpace.mp (isCompact_triangleWeightSpace _)
  have he : evaluateTriangles fs (physicalFoldedVertex second x y m z t) =
      scale ∘ evaluateTriangles fs (fun i =>
        ((movedFoldedPoint second x (y^2) m i).1,(movedFoldedPoint second x (y^2) m i).2,t*z i)) := by
    have hp : physicalFoldedVertex second x y m z t = scale ∘ (fun i =>
        ((movedFoldedPoint second x (y^2) m i).1,(movedFoldedPoint second x (y^2) m i).2,t*z i)) := by
      funext i
      rfl
    rw [hp, evaluateTriangles_comp_linear]
  rw [he]
  exact (hcont.comp h.continuous).isClosedEmbedding (hscale.comp h.injective)

/-- The Type 6 construction on the normalized lattice domain has a spatial embedding
in Euclidean coordinates and matches the marked intrinsic face lengths. -/
public theorem type6_regular_embeddedFaces (x y : ℝ) (hx : 0 ≤ x) (hx' : x ≤ 1/2)
    (hy : 0 < y) (hw : 1-x^2 ≤ y^2) {U : Set SheetMotion} (hU : IsOpen U) (hbase : 0 ∈ U) :
    ∃ (second : Bool) (z : Vertex → ℝ) (t : ℝ) (m : SheetMotion),
      chartDomain second x (y^2) ∧ 0 < t ∧ m ∈ U ∧ lengthResidual second x (y^2) z (t,m) = 0 ∧
      (∀ f : Fin 16, 0 < periodicFaceArea x (y^2) (movedIntrinsicPoint second x (y^2) m) (liftedFaces f)) ∧
      Type6SpatiallyRegular (physicalFoldedVertex second x y m z t) ∧
      type6SpatialAngleShape (physicalFoldedVertex second x y m z t) = (fun _ => 2*Real.pi,⟨x,y⟩) ∧
      Topology.IsClosedEmbedding (evaluateTriangles type6FlippedFaces (physicalFoldedVertex second x y m z t)) := by
  have H (second : Bool) (hd : chartDomain second x (y^2)) :
      ∃ (z : Vertex → ℝ) (t : ℝ) (m : SheetMotion),
        0 < t ∧ m ∈ U ∧ lengthResidual second x (y^2) z (t,m) = 0 ∧
        (∀ f : Fin 16, 0 < periodicFaceArea x (y^2) (movedIntrinsicPoint second x (y^2) m) (liftedFaces f)) ∧
        Type6SpatiallyRegular (physicalFoldedVertex second x y m z t) ∧
        type6SpatialAngleShape (physicalFoldedVertex second x y m z t) = (fun _ => 2*Real.pi,⟨x,y⟩) ∧
        Topology.IsClosedEmbedding (evaluateTriangles type6FlippedFaces (physicalFoldedVertex second x y m z t)) := by
    obtain ⟨z,t,m,_,ht,hm,hl,hi,hpos,_,hemb⟩ := type6_spatialLengthMatchedLift_regular second x (y^2) hd hU hbase
    obtain ⟨hreg,hshape⟩ := type6_spatiallyRegular_of_lengthMatch second x y hy z t m hl hi hpos
    exact ⟨z,t,m,ht,hm,hl,hpos,hreg,hshape,fixedPeriod_physical_embedding type6FlippedFaces second x y z t m hy.ne' hemb⟩
  by_cases h : x ≤ 1/6
  · have hd : chartDomain false x (y^2) := ⟨hx,h,hw⟩
    obtain ⟨z,t,m,hrest⟩ := H false hd
    exact ⟨false,z,t,m,hd,hrest⟩
  · have hd : chartDomain true x (y^2) := ⟨(lt_of_not_ge h).le,hx',hw⟩
    obtain ⟨z,t,m,hrest⟩ := H true hd
    exact ⟨true,z,t,m,hd,hrest⟩

/-- The Type 6 construction on the normalized lattice domain has a spatial embedding
in Euclidean coordinates and matches the marked intrinsic face lengths. -/
public theorem type6_embeddedFaces (x y : ℝ) (hx : 0 ≤ x) (hx' : x ≤ 1/2)
    (hy : 0 < y) (hw : 1-x^2 ≤ y^2) {U : Set SheetMotion} (hU : IsOpen U) (hbase : 0 ∈ U) :
    ∃ (second : Bool) (z : Vertex → ℝ) (t : ℝ) (m : SheetMotion),
      chartDomain second x (y^2) ∧ 0 < t ∧ m ∈ U ∧ lengthResidual second x (y^2) z (t,m) = 0 ∧
      (∀ f : Fin 16, 0 < periodicFaceArea x (y^2) (movedIntrinsicPoint second x (y^2) m) (liftedFaces f)) ∧
      Topology.IsClosedEmbedding (evaluateTriangles type6FlippedFaces (physicalFoldedVertex second x y m z t)) := by
  obtain ⟨second,z,t,m,hd,ht,hm,hlen,hpos,_,_,hemb⟩ :=
    type6_regular_embeddedFaces x y hx hx' hy hw hU hbase
  exact ⟨second,z,t,m,hd,ht,hm,hlen,hpos,hemb⟩

namespace Type5

public theorem square_edgeTriangleSeparated : EdgeTriangleSeparated squareExtrinsic faces := by
  rintro ⟨a,b⟩ he ⟨c,d,g⟩ hf hi
  have hm : ((a,b),(c,d,g)) ∈ squareDisjointPairs := by
    simpa only [squareDisjointPairs, edgeList] using mem_disjointTests he hf hi
  rw [vertexHull_pair, vertexHull_triangle]
  exact square_disjoint_edge_face a b c d g hm

/-- The spatial side of the exact square construction. -/
public theorem square_spatialComplex :
    ∃ K : Geometry.SimplicialComplex ℝ Point3,
      K.faces = ((triangleComplex faces).map squareExtrinsic).faces ∧
      Topology.IsClosedEmbedding (evaluateTriangles faces squareExtrinsic) := by
  let p (i : Vertex) := horizontal (squareExtrinsic i)
  let z (i : Vertex) := (squareExtrinsic i).2.2
  have he : (fun i => ((p i).1,(p i).2,z i)) = squareExtrinsic := by
    funext i
    exact Prod.ext rfl (Prod.ext rfl rfl)
  have hsep : EdgeTriangleSeparated (fun i => ((p i).1,(p i).2,z i)) faces := he ▸
    square_edgeTriangleSeparated
  exact ⟨spatialTriangleComplex p z _ square_generic hsep,
    (spatialTriangleComplex_faces p z _ square_generic hsep).trans (by rw [he]),
    he ▸ spatialTriangles_isClosedEmbedding p z _ square_generic hsep⟩

end Type5

namespace Type7

private theorem all_distinct (flipped : Bool) :
    (disjointPairs (faceChoice flipped)).all (fun ((a,b),c,d,e) =>
      decide ([a,b,c,d,e].Pairwise (· ≠ ·))) = true := by
  cases flipped <;> decide +kernel

public theorem rectangular_edgeTriangleSeparated (flipped : Bool) (p : Vertex → ℝ × ℝ) (z : Vertex → ℝ)
    (hg : GenericLift p z)
    (hs : ∀ pair ∈ disjointPairs (faceChoice flipped), isSeparated p z pair) :
    EdgeTriangleSeparated (fun i => ((p i).1,(p i).2,z i)) (faceChoice flipped) := by
  rintro ⟨a,b⟩ he ⟨c,d,g⟩ hf hi
  have hm : ((a,b),(c,d,g)) ∈ disjointPairs (faceChoice flipped) :=
    mem_disjointTests he hf hi
  rw [vertexHull_pair, vertexHull_triangle]
  exact separated_segment_disjoint_triangle p z a b c d g hg
    (of_decide_eq_true ((List.all_eq_true.mp (all_distinct flipped)) _ hm)) (hs _ hm)

/-- Every rectangular base has a spatial embedding with the prescribed triangles. -/
public theorem rectangular_spatialEmbedding (flipped : Bool) (w : ℝ) (hw : 1 ≤ w) :
    ∃ z : Vertex → ℝ, Topology.IsClosedEmbedding (evaluateTriangles (faceChoice flipped)
      (fun i => ((rectangularPoint w i).1,(rectangularPoint w i).2,z i))) := by
  obtain ⟨z,hg,hs⟩ := rectangular_generic_lift flipped w hw
  exact ⟨z, spatialTriangles_isClosedEmbedding _ z _ hg
    (rectangular_edgeTriangleSeparated flipped _ z hg hs)⟩

end Type7

end OrigamiTorus
