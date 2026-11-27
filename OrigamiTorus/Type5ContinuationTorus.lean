module

public import OrigamiTorus.Type5ContinuationCertificate
import Mathlib.Tactic

/-! The intrinsic development and face metrics of the Type 5 nonrectangular family. -/

@[expose] public section

noncomputable section

namespace OrigamiTorus.Type5.Continuation

theorem shift_add (x y : ℝ) {a b c : Vertex} (hf : (a,b,c) ∈ faces) :
    shift x y a c = shift x y a b+shift x y b c := by
  have ht : ∀ a b c : Vertex, (a,b,c) ∈ faces → squareShift a c = squareShift a b+squareShift b c := by
    decide +kernel
  change translatePoint x y (squareShift a c) (0,0) = _
  rw [ht a b c hf]
  apply Prod.ext <;> simp [shift,translatePoint,add_mul,add_assoc,add_left_comm]

private theorem translate_eq_add (x y : ℝ) (d : Period) (p : Plane ℝ) :
    translatePoint x y d p = p+translatePoint x y d (0,0) := by
  apply Prod.ext <;> simp [translatePoint,add_assoc]

private theorem lift_area (x y : ℝ) (p : Vertex → Plane ℝ) (f : Triangle) :
    periodicFaceArea x y p (squareLift f) = markedFaceCross (shift x y) p f := by
  rcases f with ⟨a,b,c⟩
  simp only [periodicFaceArea,squareLift,markedFaceCross,cross,shift,translatePoint,
    Prod.fst_add,Prod.snd_add,Prod.fst_sub,Prod.snd_sub,Prod.fst_zero,Prod.snd_zero,Int.cast_zero]
  ring

private theorem lift_area_lattice (x y : ℝ) (hy : y ≠ 0) (p : Vertex → Plane ℝ) (f : Triangle) :
    periodicFaceArea x y p (squareLift f) = y*orientedArea (periodCoordinates x y ∘ p) f := by
  rcases f with ⟨a,b,c⟩
  rw [lift_area]
  simp only [markedFaceCross,orientedArea,Function.comp_apply,shift,translatePoint,periodCoordinates,
    cross,Prod.fst_add,Prod.snd_add,Prod.fst_sub,Prod.snd_sub,shiftPoint]
  field_simp [hy]
  ring

private theorem lift_recovers (i : Fin 16) : squareLift (liftedVertices (squareLiftedFaces i)) = squareLiftedFaces i := by
  unfold squareLiftedFaces
  rcases faces.get _ with ⟨a,b,c⟩
  rfl

theorem periodic_area_positive {x y : ℝ} (h : ModulusBox x y) (i : Fin 16) :
    0 < periodicFaceArea x y (intrinsic x y) (squareLiftedFaces i) := by
  rw [← lift_recovers i,lift_area]
  exact intrinsic_positive h (square_liftedFaces_mem i)

theorem periodic_lattice_total_area {x y : ℝ} (h : ModulusBox x y) :
    ∑ i : Fin 16, latticeFaceArea x y (intrinsic x y) (squareLiftedFaces i) = 2 := by
  have hy := (modulus_bounds h).2.2.1.ne'
  have hs := square_total_area (periodCoordinates x y ∘ intrinsic x y)
  rw [← square_liftedFaces_labels,← List.ofFn_id,List.map_ofFn,List.map_ofFn,List.sum_ofFn] at hs
  have hh (i : Fin 16) : latticeFaceArea x y (intrinsic x y) (squareLiftedFaces i) =
      orientedArea (periodCoordinates x y ∘ intrinsic x y) (liftedVertices (squareLiftedFaces i)) := by
    rw [latticeFaceArea_eq x y hy]
    conv_lhs => rw [← lift_recovers i,lift_area_lattice x y hy]
    field_simp [hy]
  simpa only [hh,Function.comp_apply,id_eq] using hs

theorem periodic_total_area {x y : ℝ} (h : ModulusBox x y) :
    ∑ i : Fin 16, periodicFaceArea x y (intrinsic x y) (squareLiftedFaces i) = 2*y := by
  have hy := (modulus_bounds h).2.2.1.ne'
  have ha := periodic_lattice_total_area h
  simp_rw [latticeFaceArea_eq x y hy] at ha
  rw [← Finset.sum_div,div_eq_iff hy] at ha
  exact ha

def intrinsicHomeomorph {x y : ℝ} (h : ModulusBox x y) : triangleWeightSpace faces ≃ₜ MarkedTorus :=
  squarePeriodicFaceSystem.homeomorph x y (modulus_bounds h).2.2.1 (intrinsic x y)
    (periodic_area_positive h) (periodic_lattice_total_area h)

def facePoint (x y : ℝ) (i : Fin 16) (u : Vertex → ℝ) : Plane ℝ :=
  ∑ j, u j • translatePoint x y (facePeriod (squareLiftedFaces i) j) (intrinsic x y j)

theorem intrinsicHomeomorph_on_face {x y : ℝ} (h : ModulusBox x y) (i : Fin 16)
    (u : triangleWeightSpace faces) (hu : u.val ∈ faceWeights (triangleVertexSet (liftedVertices (squareLiftedFaces i)))) :
    intrinsicHomeomorph h u = projectPeriods (periodCoordinates x y (facePoint x y i u.val)) := by
  rw [intrinsicHomeomorph,PeriodicFaceSystem.homeomorph_apply,
    periodicDevelopment_on_face _ squarePeriodicFaceSystem.cover square_period_agrees x y (intrinsic x y) i u hu,
    facePeriodPoint_eq_coordinates x y (modulus_bounds h).2.2.1.ne']
  rfl

theorem face_metric {x y : ℝ} (h : ModulusBox x y) (a b c : Vertex) (hf : (a,b,c) ∈ faces) (s t : ℝ) :
    let u := intrinsic x y b+shift x y a b-intrinsic x y a
    let v := intrinsic x y c+shift x y a c-intrinsic x y a
    squared3 (smul3 s (extrinsic x y b-extrinsic x y a)+smul3 t (extrinsic x y c-extrinsic x y a)) =
      squared2 (smul2 s u+smul2 t v) := by
  have hedges {e : Edge} (he : e ∈ faceEdges (a,b,c)) : e ∈ edgeList := by
    simp only [edgeList,List.mem_eraseDups,List.mem_flatMap]
    exact ⟨(a,b,c),hf,he⟩
  have hab := all_edge_lengths h (a := a) (b := b) (hedges (by simp [faceEdges]))
  have hac := all_edge_lengths h (a := a) (b := c) (hedges (by simp [faceEdges,orderedEdge,min_comm,max_comm]))
  have hbc := all_edge_lengths h (a := b) (b := c) (hedges (by simp [faceEdges]))
  have hu : intrinsic x y b+shift x y a b-intrinsic x y a =
      intrinsic x y b-intrinsic x y a+shift x y a b := by abel
  have hv : intrinsic x y c+shift x y a c-intrinsic x y a =
      intrinsic x y c-intrinsic x y a+shift x y a c := by abel
  have hw : intrinsic x y c+shift x y a c-(intrinsic x y b+shift x y a b) =
      intrinsic x y c-intrinsic x y b+shift x y b c := by rw [shift_add x y hf]; abel
  exact triangle_squared_metric (intrinsic x y a) (intrinsic x y b+shift x y a b)
    (intrinsic x y c+shift x y a c) (extrinsic x y a) (extrinsic x y b) (extrinsic x y c)
    (by simpa only [EdgeMatch,hu] using hab) (by simpa only [EdgeMatch,hv] using hac)
    (by simpa only [EdgeMatch,hw] using hbc) s t

theorem lifted_face_metric {x y : ℝ} (h : ModulusBox x y) (i : Fin 16) (s t : ℝ) :
    let f := squareLiftedFaces i
    let P (a : Corner) := extrinsic x y a.1
    let Q (a : Corner) := translatePoint x y a.2 (intrinsic x y a.1)
    squared3 (smul3 s (P f.2.1-P f.1)+smul3 t (P f.2.2-P f.1)) =
      squared2 (smul2 s (Q f.2.1-Q f.1)+smul2 t (Q f.2.2-Q f.1)) := by
  let g := liftedVertices (squareLiftedFaces i)
  have hg : g ∈ faces := square_liftedFaces_mem i
  have he : squareLift g = squareLiftedFaces i := lift_recovers i
  rw [← he]
  rcases hg' : g with ⟨a,b,c⟩
  simp only [squareLift]
  have h0 (p : Plane ℝ) : translatePoint x y 0 p = p := by
    apply Prod.ext <;> simp [translatePoint]
  simp only [h0,translate_eq_add x y (squareShift a b) (intrinsic x y b),
    translate_eq_add x y (squareShift a c) (intrinsic x y c)]
  exact face_metric h a b c (hg' ▸ hg) s t

theorem weighted_face_metric {x y : ℝ} (h : ModulusBox x y) (i : Fin 16)
    (u v : triangleWeightSpace faces)
    (hu : u.val ∈ faceWeights (triangleVertexSet (liftedVertices (squareLiftedFaces i))))
    (hv : v.val ∈ faceWeights (triangleVertexSet (liftedVertices (squareLiftedFaces i)))) :
    squared3 (evaluateTriangles faces (extrinsic x y) u-evaluateTriangles faces (extrinsic x y) v) =
      squared2 (facePoint x y i u.val-facePoint x y i v.val) := by
  let f := squareLiftedFaces i
  have hd := square_liftedFaces_distinct i
  unfold evaluateTriangles evaluateWeights facePoint
  rw [lifted_affine_difference f hd _ _ _ hu hv,lifted_affine_difference f hd _ _ _ hu hv]
  obtain ⟨ha,hb,hc⟩ := facePeriod_correct f hd
  dsimp only [f] at ha hb hc
  simp only [f,ha,hb,hc]
  exact lifted_face_metric h i _ _

/-- The exact radical formula realizes every lattice torus in the archived
nonrectangular box by an embedded, piecewise-isometric Type 5 surface. -/
theorem torus_by_faces {x y : ℝ} (h : ModulusBox x y) :
    let τ : ℂ := x+y*Complex.I
    ∃ (H : triangleWeightSpace faces ≃ₜ ComplexTorus 1 τ)
      (F : ComplexTorus 1 τ → Point3) (P : Triangle → Vertex → ℂ),
      Topology.IsClosedEmbedding F ∧
      (∀ u, F (H u) = evaluateTriangles faces (extrinsic x y) u) ∧
      (∀ f ∈ faces, ∀ u, u.val ∈ faceWeights (triangleVertexSet f) →
        H u = complexTorusProjection 1 τ (∑ i, u.val i • P f i)) ∧
      ∀ f ∈ faces, ∀ u v,
        u.val ∈ faceWeights (triangleVertexSet f) →
        v.val ∈ faceWeights (triangleVertexSet f) →
        squared3 (F (H u)-F (H v)) =
          dist (∑ i, u.val i • P f i) (∑ i, v.val i • P f i)^2 := by
  classical
  let τ : ℂ := x+y*Complex.I
  have hsim : complexSimilarity 1 false = id := by funext z; simp [complexSimilarity]
  obtain ⟨J,hJ⟩ := complexTorus_rebase 1 τ x y (modulus_bounds h).2.2.1.ne' 1 false one_ne_zero
    (by rw [hsim,Set.image_id])
  let H := (intrinsicHomeomorph h).trans J
  let E := evaluateTriangles faces (extrinsic x y)
  let F := E ∘ H.symm
  have hfold (u : triangleWeightSpace faces) : F (H u) = E u := by simp [F]
  have exists_lift (f : Triangle) (hf : f ∈ faces) :
      ∃ i : Fin 16, liftedVertices (squareLiftedFaces i) = f := by
    rw [← square_liftedFaces_labels] at hf
    obtain ⟨i,_,he⟩ := List.mem_map.mp hf
    exact ⟨i,he⟩
  let index (f : Triangle) := if hf : f ∈ faces then (exists_lift f hf).choose else 0
  have hindex (f : Triangle) (hf : f ∈ faces) : liftedVertices (squareLiftedFaces (index f)) = f := by
    simp only [index,dite_eq_left hf]
    exact (exists_lift f hf).choose_spec
  let P (f : Triangle) (i : Vertex) := Complex.equivRealProdCLM.symm
    (translatePoint x y (facePeriod (squareLiftedFaces (index f)) i) (intrinsic x y i))
  have hpoint (f : Triangle) (u : Vertex → ℝ) :
      (∑ i, u i • P f i) = Complex.equivRealProdCLM.symm (facePoint x y (index f) u) := by
    simp only [P,facePoint,map_sum,map_smul]
  have hdist (p q : Plane ℝ) :
      dist (Complex.equivRealProdCLM.symm p) (Complex.equivRealProdCLM.symm q)^2 = squared2 (p-q) := by
    rw [dist_eq_norm,← map_sub,Complex.sq_norm,Complex.equivRealProdCLM_symm_apply]
    simp [Complex.normSq_apply,squared2,dot]
  refine ⟨H,F,P,(spatial_embedding h).comp H.symm.isClosedEmbedding,hfold,?_,?_⟩
  · intro f hf u hu
    change J (intrinsicHomeomorph h u) = _
    rw [hpoint,intrinsicHomeomorph_on_face h (index f) u (by simpa only [hindex f hf] using hu),hJ,hsim]
    rfl
  · intro f hf u v hu hv
    rw [hfold,hfold,hpoint,hpoint,hdist]
    exact weighted_face_metric h (index f) u v (by simpa only [hindex f hf] using hu)
      (by simpa only [hindex f hf] using hv)

end OrigamiTorus.Type5.Continuation
