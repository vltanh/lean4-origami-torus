module

public import OrigamiTorus.Type5Square
public import OrigamiTorus.PeriodicArea
public import OrigamiTorus.LatticeTorus
public import OrigamiTorus.SpatialRealizations
import Mathlib.Tactic

/-! Periodic face data for the exact Type 5 square witness. -/

@[expose] public section

namespace OrigamiTorus.Type5

def squareLift (f : Triangle) : LiftedFace :=
  ((f.1,0),(f.2.1,squareShift f.1 f.2.1),(f.2.2,squareShift f.1 f.2.2))

def squareLiftedFaces (j : Fin 16) : LiftedFace :=
  squareLift (faces.get (Fin.cast (by decide +kernel : 16 = faces.length) j))

theorem square_liftedFaces_labels :
    (List.finRange 16).map (fun j => liftedVertices (squareLiftedFaces j)) = faces := by
  decide +kernel

theorem square_liftedFaces_mem (j : Fin 16) : liftedVertices (squareLiftedFaces j) ∈ faces := by
  rw [← square_liftedFaces_labels]
  exact List.mem_map.mpr ⟨j,by simp,rfl⟩

/-- Every directed edge of the square witness has the same period difference
as its oppositely directed occurrence after reversal. -/
theorem square_liftedSides_pair :
    let sides := ((List.finRange 16).map squareLiftedFaces).flatMap liftedSides
    sides.Nodup ∧ sides.all (fun e => sides.contains (reverseSide e)) = true := by
  decide +kernel

/-- The three labels on every lifted triangle are distinct. -/
theorem square_liftedFaces_distinct :
    ∀ j : Fin 16, let f := liftedVertices (squareLiftedFaces j)
      f.1 ≠ f.2.1 ∧ f.1 ≠ f.2.2 ∧ f.2.1 ≠ f.2.2 := by
  decide +kernel

/-- Face lifts differ by a common translation on every shared subface. -/
theorem square_period_agrees :
    SharedFacePeriods squareLiftedFaces := by
  unfold SharedFacePeriods
  decide +kernel

private theorem square_area_lift (q : Vertex → ℝ × ℝ) (f : Triangle) :
    periodicFaceArea 0 1 q (squareLift f) = orientedArea q f := by
  rcases f with ⟨a,b,c⟩
  simp [squareLift,periodicFaceArea,orientedArea,translatePoint,shiftPoint,cross,Prod.fst_sub,Prod.snd_sub]
  ring

theorem square_lifted_area (q : Vertex → ℝ × ℝ) (j : Fin 16) :
    periodicFaceArea 0 1 q (squareLiftedFaces j) = orientedArea q (liftedVertices (squareLiftedFaces j)) :=
  square_area_lift q _

theorem square_lifted_area_positive (j : Fin 16) :
    0 < periodicFaceArea 0 1 squareIntrinsic (squareLiftedFaces j) := by
  rw [square_lifted_area]
  exact square_intrinsic_positive _ (square_liftedFaces_mem j)

theorem square_lifted_total_area (q : Vertex → ℝ × ℝ) :
    ∑ j : Fin 16, periodicFaceArea 0 1 q (squareLiftedFaces j) = 2 := by
  have h := square_total_area q
  rw [← square_liftedFaces_labels, ← List.ofFn_id, List.map_ofFn, List.map_ofFn, List.sum_ofFn] at h
  simpa only [square_lifted_area,Function.comp_apply,id_eq] using h

/-- The exact face metric agrees with the planar lifts used for the square lattice. -/
theorem square_lifted_face_metric (j : Fin 16) (s t : ℝ) :
    let f := squareLiftedFaces j
    let P (a : Corner) := squareExtrinsic a.1
    let Q (a : Corner) := translatePoint 0 1 a.2 (squareIntrinsic a.1)
    squared3 (smul3 s (P f.2.1 - P f.1) + smul3 t (P f.2.2 - P f.1)) =
      squared2 (smul2 s (Q f.2.1 - Q f.1) + smul2 t (Q f.2.2 - Q f.1)) := by
  let g := faces.get (Fin.cast (by decide +kernel : 16 = faces.length) j)
  have hg : g ∈ faces := square_liftedFaces_mem j
  have h (p : ℝ × ℝ) (d : Period) : translatePoint 0 1 d p = p+realPeriod d := by
    apply Prod.ext <;> simp [translatePoint,realPeriod]
  rcases hg' : g with ⟨a,b,c⟩
  change squared3 (smul3 s (squareExtrinsic g.2.1-squareExtrinsic g.1) +
    smul3 t (squareExtrinsic g.2.2-squareExtrinsic g.1)) =
      squared2 (smul2 s (translatePoint 0 1 (squareShift g.1 g.2.1) (squareIntrinsic g.2.1) -
        translatePoint 0 1 0 (squareIntrinsic g.1)) +
          smul2 t (translatePoint 0 1 (squareShift g.1 g.2.2) (squareIntrinsic g.2.2) -
            translatePoint 0 1 0 (squareIntrinsic g.1)))
  rw [hg',h,h,h]
  have h0 : realPeriod (0 : Period) = 0 := by simp [realPeriod]
  rw [h0,add_zero]
  exact square_face_metric a b c (hg' ▸ hg) s t

theorem square_weight_has_liftedFace (u : triangleWeightSpace faces) :
    ∃ j : Fin 16, u.val ∈ faceWeights (triangleVertexSet (liftedVertices (squareLiftedFaces j))) := by
  obtain ⟨f,hf,hu⟩ := u.property
  rw [← square_liftedFaces_labels] at hf
  obtain ⟨j,_,rfl⟩ := List.mem_map.mp hf
  exact ⟨j,hu⟩

def squarePeriodicFaceSystem : PeriodicFaceSystem faces squareLiftedFaces where
  mem := square_liftedFaces_mem
  cover := square_weight_has_liftedFace
  shared := square_period_agrees
  distinct := square_liftedFaces_distinct
  reverseEdge := by decide +kernel
  link := orientedLinkCycle
  link_nonempty v := lt_of_lt_of_le (by decide : 0 < 3) (linkCycles_checked v).2.1
  edgeShift := squareShift
  link_corner v i := by
    fin_cases v <;> revert i <;> decide +kernel

/-- The exact intrinsic square triangles developed into the square lattice quotient. -/
noncomputable def squareIntrinsicMap : triangleWeightSpace faces → MarkedTorus :=
  periodicDevelopment squareLiftedFaces square_weight_has_liftedFace 0 1 squareIntrinsic

theorem square_intrinsicMap_on_face (j : Fin 16) (u : triangleWeightSpace faces)
    (hu : u.val ∈ faceWeights (triangleVertexSet (liftedVertices (squareLiftedFaces j)))) :
    squareIntrinsicMap u = projectPeriods (facePeriodPoint 0 1 squareIntrinsic (squareLiftedFaces j) u.val) :=
  periodicDevelopment_on_face squareLiftedFaces square_weight_has_liftedFace square_period_agrees
    0 1 squareIntrinsic j u hu

theorem square_intrinsicMap_continuous : Continuous squareIntrinsicMap :=
  periodicDevelopment_continuous squareLiftedFaces square_weight_has_liftedFace square_period_agrees
    0 1 squareIntrinsic

theorem square_lattice_total_area :
    ∑ j : Fin 16, latticeFaceArea 0 1 squareIntrinsic (squareLiftedFaces j) = 2 := by
  simp_rw [latticeFaceArea_eq 0 1 one_ne_zero, div_one]
  exact square_lifted_total_area squareIntrinsic

/-- The exact intrinsic triangles triangulate the unit square torus. -/
noncomputable def squareIntrinsicHomeomorph : triangleWeightSpace faces ≃ₜ MarkedTorus :=
  squarePeriodicFaceSystem.homeomorph 0 1 one_pos squareIntrinsic
    square_lifted_area_positive square_lattice_total_area

theorem square_intrinsicHomeomorph_apply (u : triangleWeightSpace faces) :
    squareIntrinsicHomeomorph u = squareIntrinsicMap u :=
  squarePeriodicFaceSystem.homeomorph_apply 0 1 one_pos squareIntrinsic
    square_lifted_area_positive square_lattice_total_area u

/-- Affine evaluation in the plane of the unit square lattice. -/
noncomputable def squareFacePoint (j : Fin 16) (u : Vertex → ℝ) : ℝ × ℝ :=
  ∑ i, u i • translatePoint 0 1 (facePeriod (squareLiftedFaces j) i) (squareIntrinsic i)

theorem square_weighted_face_metric (j : Fin 16) (u v : triangleWeightSpace faces)
    (hu : u.val ∈ faceWeights (triangleVertexSet (liftedVertices (squareLiftedFaces j))))
    (hv : v.val ∈ faceWeights (triangleVertexSet (liftedVertices (squareLiftedFaces j)))) :
    squared3 (evaluateTriangles faces squareExtrinsic u - evaluateTriangles faces squareExtrinsic v) =
      squared2 (squareFacePoint j u.val - squareFacePoint j v.val) := by
  let f := squareLiftedFaces j
  have hd := square_liftedFaces_distinct j
  unfold evaluateTriangles evaluateWeights squareFacePoint
  rw [lifted_affine_difference f hd _ _ _ hu hv, lifted_affine_difference f hd _ _ _ hu hv]
  obtain ⟨ha,hb,hc⟩ := facePeriod_correct f hd
  dsimp only [f] at ha hb hc
  simp only [f,ha,hb,hc]
  exact square_lifted_face_metric j _ _

/-- The exact radical coordinates realize the unit square torus as an embedded
Type 5 origami torus, preserving Euclidean distances on each triangle. -/
theorem square_torus :
    ∃ F : MarkedTorus → Point3,
      Topology.IsClosedEmbedding F ∧
      (∀ u, F (squareIntrinsicHomeomorph u) = evaluateTriangles faces squareExtrinsic u) ∧
      (∀ j u, u.val ∈ faceWeights (triangleVertexSet (liftedVertices (squareLiftedFaces j))) →
        squareIntrinsicHomeomorph u = projectPeriods (squareFacePoint j u.val)) ∧
      ∀ j u v,
        u.val ∈ faceWeights (triangleVertexSet (liftedVertices (squareLiftedFaces j))) →
        v.val ∈ faceWeights (triangleVertexSet (liftedVertices (squareLiftedFaces j))) →
        squared3 (F (squareIntrinsicHomeomorph u) - F (squareIntrinsicHomeomorph v)) =
          squared2 (squareFacePoint j u.val - squareFacePoint j v.val) := by
  let H := squareIntrinsicHomeomorph
  let E := evaluateTriangles faces squareExtrinsic
  obtain ⟨_,_,hE⟩ := square_spatialComplex
  have hmap (u : triangleWeightSpace faces) : (E ∘ H.symm) (H u) = E u := by simp
  refine ⟨E ∘ H.symm,hE.comp H.symm.isClosedEmbedding,hmap,?_,?_⟩
  · intro j u hu
    rw [square_intrinsicHomeomorph_apply, square_intrinsicMap_on_face j u hu,
      facePeriodPoint_eq_coordinates 0 1 one_ne_zero]
    congr 1
    change periodCoordinates 0 1 (squareFacePoint j u.val) = squareFacePoint j u.val
    exact Prod.ext (by simp [periodCoordinates]) (by simp [periodCoordinates])
  · intro j u v hu hv
    rw [hmap u,hmap v]
    exact square_weighted_face_metric j u v hu hv

/-- The explicit radical square realization on the quotient of the complex
plane by the square lattice, with its affine maps indexed by labeled faces. -/
theorem square_complex_by_faces :
    ∃ (H : triangleWeightSpace faces ≃ₜ ComplexTorus 1 Complex.I)
      (F : ComplexTorus 1 Complex.I → Point3) (P : Triangle → Vertex → ℂ),
      Topology.IsClosedEmbedding F ∧
      (∀ u, F (H u) = evaluateTriangles faces squareExtrinsic u) ∧
      (∀ f ∈ faces, ∀ u, u.val ∈ faceWeights (triangleVertexSet f) →
        H u = complexTorusProjection 1 Complex.I (∑ i, u.val i • P f i)) ∧
      ∀ f ∈ faces, ∀ u v,
        u.val ∈ faceWeights (triangleVertexSet f) →
        v.val ∈ faceWeights (triangleVertexSet f) →
        squared3 (F (H u)-F (H v)) =
          dist (∑ i, u.val i • P f i) (∑ i, v.val i • P f i)^2 := by
  classical
  have hsim : complexSimilarity 1 false = id := by funext z; simp [complexSimilarity]
  obtain ⟨J,hJ⟩ := complexTorus_rebase 1 Complex.I 0 1 one_ne_zero 1 false one_ne_zero
    (by simp [hsim])
  have hJ' (p : ℝ × ℝ) :
      J (projectPeriods p) = complexTorusProjection 1 Complex.I (Complex.equivRealProdCLM.symm p) := by
    have hp : periodCoordinates 0 1 p = p := by
      exact Prod.ext (by simp [periodCoordinates]) (by simp [periodCoordinates])
    simpa only [hp,hsim,id_eq] using hJ p
  obtain ⟨F,hF,hfold,hproj,hmetric⟩ := square_torus
  have exists_lift (f : Triangle) (hf : f ∈ faces) :
      ∃ j : Fin 16, liftedVertices (squareLiftedFaces j) = f := by
    rw [← square_liftedFaces_labels] at hf
    obtain ⟨j,_,he⟩ := List.mem_map.mp hf
    exact ⟨j,he⟩
  let index (f : Triangle) := if hf : f ∈ faces then (exists_lift f hf).choose else 0
  have hindex (f : Triangle) (hf : f ∈ faces) : liftedVertices (squareLiftedFaces (index f)) = f := by
    simp only [index,dite_eq_left hf]
    exact (exists_lift f hf).choose_spec
  let P (f : Triangle) (i : Vertex) :=
    Complex.equivRealProdCLM.symm (translatePoint 0 1 (facePeriod (squareLiftedFaces (index f)) i) (squareIntrinsic i))
  have hpoint (f : Triangle) (u : Vertex → ℝ) :
      (∑ i, u i • P f i) = Complex.equivRealProdCLM.symm (squareFacePoint (index f) u) := by
    simp only [P,squareFacePoint,map_sum,map_smul]
  have hdist (p q : ℝ × ℝ) :
      dist (Complex.equivRealProdCLM.symm p) (Complex.equivRealProdCLM.symm q)^2 = squared2 (p-q) := by
    rw [dist_eq_norm,← map_sub,Complex.sq_norm,Complex.equivRealProdCLM_symm_apply]
    simp [Complex.normSq_apply,squared2,dot]
  let H := squareIntrinsicHomeomorph.trans J
  let G := F ∘ J.symm
  have hfold' (u : triangleWeightSpace faces) : G (H u) = F (squareIntrinsicHomeomorph u) := by simp [G,H]
  refine ⟨H,G,P,hF.comp J.symm.isClosedEmbedding,fun u => (hfold' u).trans (hfold u),?_,?_⟩
  · intro f hf u hu
    change J (squareIntrinsicHomeomorph u) = _
    rw [hpoint,hproj (index f) u (by simpa only [hindex f hf] using hu),hJ']
  · intro f hf u v hu hv
    rw [hfold',hfold',hpoint,hpoint,hdist]
    apply hmetric (index f) u v
    · simpa only [hindex f hf] using hu
    · simpa only [hindex f hf] using hv

end OrigamiTorus.Type5
