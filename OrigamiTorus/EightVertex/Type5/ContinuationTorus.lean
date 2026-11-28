module

public import OrigamiTorus.EightVertex.Type5.ContinuationCertificate
import Mathlib.Tactic

/-! Intrinsic development and face metrics for Type 5 with the square marking, including the near-square family. -/

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

theorem marked_lattice_total_area {x y : ℝ} (hy : y ≠ 0) (p : Vertex → Plane ℝ) :
    ∑ i : Fin 16, latticeFaceArea x y p (squareLiftedFaces i) = 2 := by
  have hs := square_total_area (periodCoordinates x y ∘ p)
  rw [← square_liftedFaces_labels,← List.ofFn_id,List.map_ofFn,List.map_ofFn,List.sum_ofFn] at hs
  have hh (i : Fin 16) : latticeFaceArea x y p (squareLiftedFaces i) =
      orientedArea (periodCoordinates x y ∘ p) (liftedVertices (squareLiftedFaces i)) := by
    rw [latticeFaceArea_eq x y hy]
    conv_lhs => rw [← lift_recovers i,lift_area_lattice x y hy]
    field_simp [hy]
  simpa only [hh,Function.comp_apply,id_eq] using hs

theorem periodic_lattice_total_area {x y : ℝ} (h : ModulusBox x y) :
    ∑ i : Fin 16, latticeFaceArea x y (intrinsic x y) (squareLiftedFaces i) = 2 :=
  marked_lattice_total_area (modulus_bounds h).2.2.1.ne' _

/-- Any positively oriented placement with the square marking triangulates its lattice quotient. -/
def markedIntrinsicHomeomorph {x y : ℝ} (hy : 0 < y) (p : Vertex → Plane ℝ)
    (h : ∀ f ∈ faces, 0 < markedFaceCross (shift x y) p f) :
    triangleWeightSpace faces ≃ₜ MarkedTorus :=
  squarePeriodicFaceSystem.homeomorph x y hy p (fun i => by
    rw [← lift_recovers i,lift_area]
    exact h _ (square_liftedFaces_mem i)) (marked_lattice_total_area hy.ne' p)

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

def markedFacePoint (x y : ℝ) (p : Vertex → Plane ℝ) (i : Fin 16) (u : Vertex → ℝ) : Plane ℝ :=
  ∑ j, u j • translatePoint x y (facePeriod (squareLiftedFaces i) j) (p j)

theorem markedIntrinsicHomeomorph_on_face {x y : ℝ} (hy : 0 < y) (p : Vertex → Plane ℝ)
    (ha : ∀ f ∈ faces, 0 < markedFaceCross (shift x y) p f) (i : Fin 16)
    (u : triangleWeightSpace faces) (hu : u.val ∈ faceWeights (triangleVertexSet (liftedVertices (squareLiftedFaces i)))) :
    markedIntrinsicHomeomorph hy p ha u = projectPeriods (periodCoordinates x y (markedFacePoint x y p i u.val)) := by
  rw [markedIntrinsicHomeomorph,PeriodicFaceSystem.homeomorph_apply,
    periodicDevelopment_on_face _ squarePeriodicFaceSystem.cover square_period_agrees x y p i u hu,
    facePeriodPoint_eq_coordinates x y hy.ne']
  rfl

def facePoint (x y : ℝ) (i : Fin 16) (u : Vertex → ℝ) : Plane ℝ :=
  markedFacePoint x y (intrinsic x y) i u

theorem intrinsicHomeomorph_on_face {x y : ℝ} (h : ModulusBox x y) (i : Fin 16)
    (u : triangleWeightSpace faces) (hu : u.val ∈ faceWeights (triangleVertexSet (liftedVertices (squareLiftedFaces i)))) :
    intrinsicHomeomorph h u = projectPeriods (periodCoordinates x y (facePoint x y i u.val)) :=
  markedIntrinsicHomeomorph_on_face (modulus_bounds h).2.2.1 (intrinsic x y) (fun _ hf => intrinsic_positive h hf) i u hu

/-- Three matched edge lengths give the metric on the whole marked triangle. -/
theorem marked_face_metric {x y : ℝ} {p : Vertex → Plane ℝ} {r : Vertex → Point3}
    (hedge : ∀ {a b : Vertex}, orderedEdge a b ∈ edgeList →
      squared3 (r b-r a) = squared2 (p b-p a+shift x y a b)) (a b c : Vertex) (hf : (a,b,c) ∈ faces) (s t : ℝ) :
    let u := p b+shift x y a b-p a
    let v := p c+shift x y a c-p a
    squared3 (smul3 s (r b-r a)+smul3 t (r c-r a)) =
      squared2 (smul2 s u+smul2 t v) := by
  have hedges {e : Edge} (he : e ∈ faceEdges (a,b,c)) : e ∈ edgeList := by
    simp only [edgeList,List.mem_eraseDups,List.mem_flatMap]
    exact ⟨(a,b,c),hf,he⟩
  have hab := hedge (a := a) (b := b) (hedges (by simp [faceEdges]))
  have hac := hedge (a := a) (b := c) (hedges (by simp [faceEdges,orderedEdge,min_comm,max_comm]))
  have hbc := hedge (a := b) (b := c) (hedges (by simp [faceEdges]))
  have hu : p b+shift x y a b-p a =
      p b-p a+shift x y a b := by abel
  have hv : p c+shift x y a c-p a =
      p c-p a+shift x y a c := by abel
  have hw : p c+shift x y a c-(p b+shift x y a b) =
      p c-p b+shift x y b c := by rw [shift_add x y hf]; abel
  exact triangle_squared_metric (p a) (p b+shift x y a b)
    (p c+shift x y a c) (r a) (r b) (r c)
    (by simpa only [hu] using hab) (by simpa only [hv] using hac)
    (by simpa only [hw] using hbc) s t

theorem face_metric {x y : ℝ} (h : ModulusBox x y) (a b c : Vertex) (hf : (a,b,c) ∈ faces) (s t : ℝ) :
    let u := intrinsic x y b+shift x y a b-intrinsic x y a
    let v := intrinsic x y c+shift x y a c-intrinsic x y a
    squared3 (smul3 s (extrinsic x y b-extrinsic x y a)+smul3 t (extrinsic x y c-extrinsic x y a)) =
      squared2 (smul2 s u+smul2 t v) :=
  marked_face_metric (all_edge_lengths h) a b c hf s t

theorem marked_lifted_face_metric {x y : ℝ} {p : Vertex → Plane ℝ} {r : Vertex → Point3}
    (hedge : ∀ {a b : Vertex}, orderedEdge a b ∈ edgeList →
      squared3 (r b-r a) = squared2 (p b-p a+shift x y a b)) (i : Fin 16) (s t : ℝ) :
    let f := squareLiftedFaces i
    let P (a : Corner) := r a.1
    let Q (a : Corner) := translatePoint x y a.2 (p a.1)
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
  simp only [h0,translate_eq_add x y (squareShift a b) (p b),
    translate_eq_add x y (squareShift a c) (p c)]
  exact marked_face_metric hedge a b c (hg' ▸ hg) s t

theorem marked_weighted_face_metric {x y : ℝ} {p : Vertex → Plane ℝ} {r : Vertex → Point3}
    (hedge : ∀ {a b : Vertex}, orderedEdge a b ∈ edgeList →
      squared3 (r b-r a) = squared2 (p b-p a+shift x y a b)) (i : Fin 16)
    (u v : triangleWeightSpace faces)
    (hu : u.val ∈ faceWeights (triangleVertexSet (liftedVertices (squareLiftedFaces i))))
    (hv : v.val ∈ faceWeights (triangleVertexSet (liftedVertices (squareLiftedFaces i)))) :
    squared3 (evaluateTriangles faces (r) u-evaluateTriangles faces (r) v) =
      squared2 (markedFacePoint x y p i u.val-markedFacePoint x y p i v.val) := by
  let f := squareLiftedFaces i
  have hd := square_liftedFaces_distinct i
  unfold evaluateTriangles evaluateWeights markedFacePoint
  rw [lifted_affine_difference f hd _ _ _ hu hv,lifted_affine_difference f hd _ _ _ hu hv]
  obtain ⟨ha,hb,hc⟩ := facePeriod_correct f hd
  dsimp only [f] at ha hb hc
  simp only [f,ha,hb,hc]
  exact marked_lifted_face_metric hedge i _ _

theorem lifted_face_metric {x y : ℝ} (h : ModulusBox x y) (i : Fin 16) (s t : ℝ) :
    let f := squareLiftedFaces i
    let P (a : Corner) := extrinsic x y a.1
    let Q (a : Corner) := translatePoint x y a.2 (intrinsic x y a.1)
    squared3 (smul3 s (P f.2.1-P f.1)+smul3 t (P f.2.2-P f.1)) =
      squared2 (smul2 s (Q f.2.1-Q f.1)+smul2 t (Q f.2.2-Q f.1)) :=
  marked_lifted_face_metric (all_edge_lengths h) i _ _

theorem weighted_face_metric {x y : ℝ} (h : ModulusBox x y) (i : Fin 16)
    (u v : triangleWeightSpace faces)
    (hu : u.val ∈ faceWeights (triangleVertexSet (liftedVertices (squareLiftedFaces i))))
    (hv : v.val ∈ faceWeights (triangleVertexSet (liftedVertices (squareLiftedFaces i)))) :
    squared3 (evaluateTriangles faces (extrinsic x y) u-evaluateTriangles faces (extrinsic x y) v) =
      squared2 (facePoint x y i u.val-facePoint x y i v.val) :=
  marked_weighted_face_metric (all_edge_lengths h) i u v hu hv

/-- Positive marked faces and matching edge lengths give a map from the actual complex
lattice quotient, with its intrinsic face metrics. The spatial placement may self-intersect. -/
theorem marked_map_by_faces {x y : ℝ} {p : Vertex → Plane ℝ} {r : Vertex → Point3}
    (hedge : ∀ {a b : Vertex}, orderedEdge a b ∈ edgeList →
      squared3 (r b-r a) = squared2 (p b-p a+shift x y a b))
    (hy : 0 < y) (ha : ∀ f ∈ faces, 0 < markedFaceCross (shift x y) p f) :
    let τ : ℂ := x+y*Complex.I
    ∃ (H : triangleWeightSpace faces ≃ₜ ComplexTorus 1 τ)
      (F : ComplexTorus 1 τ → Point3) (P : Triangle → Vertex → ℂ),
      Continuous F ∧
      (∀ u, F (H u) = evaluateTriangles faces r u) ∧
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
  obtain ⟨J,hJ⟩ := complexTorus_rebase 1 τ x y hy.ne' 1 false one_ne_zero
    (by rw [hsim,Set.image_id])
  let H := (markedIntrinsicHomeomorph hy p ha).trans J
  let E := evaluateTriangles faces r
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
    (translatePoint x y (facePeriod (squareLiftedFaces (index f)) i) (p i))
  have hpoint (f : Triangle) (u : Vertex → ℝ) :
      (∑ i, u i • P f i) = Complex.equivRealProdCLM.symm (markedFacePoint x y p (index f) u) := by
    simp only [P,markedFacePoint,map_sum,map_smul]
  have hdist (p q : Plane ℝ) :
      dist (Complex.equivRealProdCLM.symm p) (Complex.equivRealProdCLM.symm q)^2 = squared2 (p-q) := by
    rw [dist_eq_norm,← map_sub,Complex.sq_norm,Complex.equivRealProdCLM_symm_apply]
    simp [Complex.normSq_apply,squared2,dot]
  refine ⟨H,F,P,(continuous_evaluateTriangles faces r).comp H.symm.continuous,hfold,?_,?_⟩
  · intro f hf u hu
    change J (markedIntrinsicHomeomorph hy p ha u) = _
    rw [hpoint,markedIntrinsicHomeomorph_on_face hy p ha (index f) u (by simpa only [hindex f hf] using hu),hJ,hsim]
    rfl
  · intro f hf u v hu hv
    rw [hfold,hfold,hpoint,hpoint,hdist]
    exact marked_weighted_face_metric hedge (index f) u v (by simpa only [hindex f hf] using hu)
      (by simpa only [hindex f hf] using hv)

/-- The dyadic-grid formula realizes every lattice torus in the near-square
box by an embedded, piecewise-isometric Type 5 surface. -/
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
  obtain ⟨H,F,P,_,hF,hP,hmetric⟩ := marked_map_by_faces (all_edge_lengths h) (modulus_bounds h).2.2.1
    (fun _ hf => intrinsic_positive h hf)
  refine ⟨H,F,P,?_,hF,hP,hmetric⟩
  have heq : F = evaluateTriangles faces (extrinsic x y) ∘ H.symm := by
    funext z
    simpa using hF (H.symm z)
  rw [heq]
  exact (spatial_embedding h).comp H.symm.isClosedEmbedding

end OrigamiTorus.Type5.Continuation
