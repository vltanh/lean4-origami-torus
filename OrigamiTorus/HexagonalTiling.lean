module

public import OrigamiTorus.HexagonalNearest
public import OrigamiTorus.HexagonalWinding
public import OrigamiTorus.PeriodicArea
import Mathlib.Tactic

/-! The seven exact hexagonal coordinate systems give intrinsic quotient
triangulations with strictly shortest edges. -/

@[expose] public section

namespace OrigamiTorus.Winding.Hexagonal

def asReal (p : RationalPoint) : ℝ × ℝ := (p.1,p.2)

def casePoints (j : Fin 7) (v : Vertex) : ℝ × ℝ :=
  asReal (placement (rayCase j).1 (rayCase j).2 v)

def caseShift (j : Fin 7) : EdgeCochain := markedShift (rayCase j).1 (rayCase j).2

def reverseFace (f : Triangle) : Triangle := (f.1,f.2.2,f.2.1)

def reverseOrientation : Fin 7 → Bool := ![true,true,true,false,false,true,false]

def orientFace (j : Fin 7) (f : Triangle) : Triangle := if reverseOrientation j then reverseFace f else f

def caseFaces (j : Fin 7) : List Triangle := (rayCase j).1.faces.map (orientFace j)

theorem caseFaces_length (j : Fin 7) : (caseFaces j).length = 16 := by revert j; decide +kernel

def caseFace (j : Fin 7) (i : Fin 16) : Triangle :=
  (caseFaces j).get (Fin.cast (caseFaces_length j).symm i)

def liftFace (K : EdgeCochain) (f : Triangle) : LiftedFace :=
  ((f.1,0),(f.2.1,K f.1 f.2.1),(f.2.2,K f.1 f.2.2))

def caseLift (j : Fin 7) (i : Fin 16) : LiftedFace := liftFace (caseShift j) (caseFace j i)

theorem caseLift_labels (j : Fin 7) :
    (List.finRange 16).map (fun i => liftedVertices (caseLift j i)) = caseFaces j := by
  revert j
  decide +kernel

theorem caseFaces_same_labelSets (j : Fin 7) :
    (caseFaces j).map triangleVertexSet = (rayCase j).1.faces.map triangleVertexSet := by
  unfold caseFaces
  rw [List.map_map]
  congr 1
  funext f
  rcases f with ⟨a,b,c⟩
  cases h : reverseOrientation j <;> simp [orientFace,h,reverseFace,triangleVertexSet_eq,Finset.pair_comm]

theorem caseFaces_same_weightSpace (j : Fin 7) :
    triangleWeightSpace (caseFaces j) = triangleWeightSpace (rayCase j).1.faces := by
  ext w
  have hh (fs : List Triangle) : w ∈ triangleWeightSpace fs ↔
      ∃ s ∈ fs.map triangleVertexSet, w ∈ faceWeights s := by
    change (∃ f ∈ fs, w ∈ faceWeights (triangleVertexSet f)) ↔ _
    constructor
    · rintro ⟨f,hf,hw⟩
      exact ⟨_,List.mem_map.mpr ⟨f,hf,rfl⟩,hw⟩
    · rintro ⟨s,hs,hw⟩
      obtain ⟨f,hf,rfl⟩ := List.mem_map.mp hs
      exact ⟨f,hf,hw⟩
  rw [hh,hh,caseFaces_same_labelSets]

def caseLink (j : Fin 7) (v : Vertex) : List Vertex :=
  let ds := directedLinkFromFaces (caseFaces j) v
  let start := (ds.headD (v,v)).1
  let next (a : Vertex) := (ds.lookup a).getD a
  (List.range ds.length).map fun i => (next^[i]) start

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem caseShared (j : Fin 7) : SharedFacePeriods (caseLift j) := by
  unfold SharedFacePeriods
  revert j
  decide +kernel

theorem caseDistinct (j : Fin 7) (i : Fin 16) :
    let f := caseLift j i
    f.1.1 ≠ f.2.1.1 ∧ f.1.1 ≠ f.2.2.1 ∧ f.2.1.1 ≠ f.2.2.1 := by
  revert j i
  decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem caseReverseEdge (j : Fin 7) (i : Fin 16) (k : Fin 3) :
    ∃ (l : Fin 16) (r : Fin 3),
      let f := rotateCorners k (caseLift j i)
      let g := rotateCorners r (caseLift j l)
      g.1.1 = f.2.1.1 ∧ g.2.1.1 = f.1.1 ∧ g.2.1.2 - g.1.2 = f.1.2 - f.2.1.2 := by
  revert j i k
  decide +kernel

theorem caseLink_nonempty (j : Fin 7) (v : Vertex) : 0 < (caseLink j v).length := by
  revert j v
  decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem caseLink_corner (j : Fin 7) (v : Vertex) (i : Fin (caseLink j v).length) :
    ∃ (l : Fin 16) (k : Fin 3),
      let f := rotateCorners k (caseLift j l)
      f.1.1 = v ∧ f.2.1.1 = (caseLink j v).get i ∧
      f.2.2.1 = (caseLink j v).get (finRotate _ i) ∧
      caseShift j f.1.1 f.2.1.1 = (liftedSide f.1 f.2.1).2.2 ∧
      caseShift j f.1.1 f.2.2.1 = (liftedSide f.1 f.2.2).2.2 := by
  revert j v i
  decide +kernel

def caseFaceSystem (j : Fin 7) : PeriodicFaceSystem (caseFaces j) (caseLift j) where
  mem i := by
    rw [← caseLift_labels j]
    exact List.mem_map.mpr ⟨i,by simp,rfl⟩
  cover u := by
    obtain ⟨f,hf,hw⟩ := u.property
    rw [← caseLift_labels j] at hf
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp hf
    exact ⟨i,hw⟩
  shared := caseShared j
  distinct := caseDistinct j
  reverseEdge := caseReverseEdge j
  link := caseLink j
  link_nonempty := caseLink_nonempty j
  edgeShift := caseShift j
  link_corner := caseLink_corner j

private theorem areaSign_eq (j : Fin 7) :
    areaSign (rayCase j).1 (rayCase j).2 = if reverseOrientation j then -1 else 1 := by
  revert j
  decide +kernel

private theorem orient_area (j : Fin 7) (f : Triangle) :
    faceDoubleArea (rayCase j).1 (rayCase j).2 (orientFace j f) =
      areaSign (rayCase j).1 (rayCase j).2 * faceDoubleArea (rayCase j).1 (rayCase j).2 f := by
  rw [areaSign_eq]
  rcases f with ⟨a,b,c⟩
  cases h : reverseOrientation j
  · simp [orientFace,h]
  · have h' : orientFace j (a,b,c) = (a,c,b) := by simp [orientFace,h,reverseFace]
    rw [h']
    simp only [ite_true,faceDoubleArea]
    ring

private theorem lifted_area (j : Fin 7) (f : Triangle) :
    periodicFaceArea 0 1 (casePoints j) (liftFace (caseShift j) f) =
      (faceDoubleArea (rayCase j).1 (rayCase j).2 f : ℝ) := by
  rcases f with ⟨a,b,c⟩
  simp [periodicFaceArea,liftFace,casePoints,caseShift,translatePoint,asReal,
    faceDoubleArea,markedDisplacement,rationalPeriod,Prod.fst_add,Prod.snd_add,Prod.fst_sub,Prod.snd_sub]
  ring

theorem caseArea_positive (j : Fin 7) (i : Fin 16) :
    0 < periodicFaceArea 0 1 (casePoints j) (caseLift j i) := by
  have hf : caseFace j i ∈ caseFaces j := List.get_mem _ _
  obtain ⟨f,hf,he⟩ := List.mem_map.mp hf
  rw [caseLift,lifted_area,← he,orient_area]
  exact_mod_cast (coordinate_certificate j).1 f hf

theorem caseArea_total (j : Fin 7) :
    ∑ i : Fin 16, latticeFaceArea 0 1 (casePoints j) (caseLift j i) = 2 := by
  have h : ((caseFaces j).map (faceDoubleArea (rayCase j).1 (rayCase j).2)).sum = 2 := by
    rw [caseFaces,List.map_map]
    change ((rayCase j).1.faces.map fun f => faceDoubleArea (rayCase j).1 (rayCase j).2 (orientFace j f)).sum = 2
    simp_rw [orient_area]
    exact (coordinate_certificate j).2.1
  rw [← caseLift_labels j,← List.ofFn_id,List.map_ofFn,List.map_ofFn,List.sum_ofFn] at h
  simp_rw [latticeFaceArea_eq 0 1 one_ne_zero,div_one,caseLift,lifted_area]
  exact_mod_cast h

/-- The explicit lifts give a degree-one affine development to the torus
in lattice coordinates. -/
noncomputable def intrinsicHomeomorph (j : Fin 7) : triangleWeightSpace (caseFaces j) ≃ₜ MarkedTorus :=
  (caseFaceSystem j).homeomorph 0 1 one_pos (casePoints j) (caseArea_positive j) (caseArea_total j)

theorem intrinsicHomeomorph_on_face (j : Fin 7) (i : Fin 16) (u : triangleWeightSpace (caseFaces j))
    (hu : u.val ∈ faceWeights (triangleVertexSet (liftedVertices (caseLift j i)))) :
    intrinsicHomeomorph j u = projectPeriods (facePeriodPoint 0 1 (casePoints j) (caseLift j i) u.val) := by
  rw [intrinsicHomeomorph,PeriodicFaceSystem.homeomorph_apply]
  exact periodicDevelopment_on_face _ (caseFaceSystem j).cover (caseShared j) 0 1 (casePoints j) i u hu

private theorem absolute_twice_dot (d : RationalPoint) (u : Period) :
    |2*dot d (rationalPeriod u)| = 2*|dot d (rationalPeriod u)| := by
  rw [abs_mul,abs_of_pos (by norm_num : (0 : ℚ) < 2)]

/-- Every edge of each of the seven exact intrinsic placements has the
strict shortest lift at the hexagonal metric. -/
theorem caseEdges_shortest (j : Fin 7) (e : Edge) (he : e ∈ (rayCase j).1.edges) {y : ℝ} (hy : y^2 = 3/4) :
    let d := asReal (markedDisplacement (rayCase j).1 (rayCase j).2 e.1 e.2)
    StrictShortest (1/2) y (d.1+d.2/2) d.2 := by
  let d := markedDisplacement (rayCase j).1 (rayCase j).2 e.1 e.2
  have h := (coordinate_certificate j).2.2 e he
  have h₁ : 2*dot d (rationalPeriod (1,0)) = 2*d.1+d.2 := by norm_num [dot,rationalPeriod]; ring
  have h₂ : 2*dot d (rationalPeriod (0,1)) = d.1+2*d.2 := by norm_num [dot,rationalPeriod]; ring
  have h₃ : 2*dot d (rationalPeriod (-1,1)) = -(d.1-d.2) := by norm_num [dot,rationalPeriod]; ring
  have ha := h (1,0) (by simp [nearestDirections])
  have hb := h (0,1) (by simp [nearestDirections])
  have hd := h (-1,1) (by simp [nearestDirections])
  change 2*|dot d (rationalPeriod (1,0))| < 1 at ha
  change 2*|dot d (rationalPeriod (0,1))| < 1 at hb
  change 2*|dot d (rationalPeriod (-1,1))| < 1 at hd
  rw [← absolute_twice_dot,h₁] at ha
  rw [← absolute_twice_dot,h₂] at hb
  rw [← absolute_twice_dot,h₃,abs_neg] at hd
  change StrictShortest (1/2) y ((d.1 : ℝ)+(d.2 : ℝ)/2) (d.2 : ℝ)
  apply strictShortest_of_three hy
  · exact_mod_cast ha
  · exact_mod_cast hb
  · exact_mod_cast hd

noncomputable def physicalPoint (y : ℝ) (p : ℝ × ℝ) : ℝ × ℝ := (p.1+(1/2)*p.2,y*p.2)

private theorem periodCoordinates_physicalPoint {y : ℝ} (hy : y ≠ 0) (p : ℝ × ℝ) :
    periodCoordinates (1/2) y (physicalPoint y p) = p := by
  apply Prod.ext
  · simp only [periodCoordinates,physicalPoint]
    field_simp [hy]
    ring
  · simp only [periodCoordinates,physicalPoint]
    field_simp [hy]

/-- The seven developments give affine triangulations of the actual
hexagonal lattice quotient. The vertex coordinates and periods are fixed
by `casePoints` and `caseLift`. -/
theorem hexagonal_intrinsic_torus (j : Fin 7) {y : ℝ} (hy : 0 < y) (hw : y^2 = 3/4) :
    let τ : ℂ := ((1/2 : ℝ) : ℂ)+y*Complex.I
    ∃ H : triangleWeightSpace (caseFaces j) ≃ₜ ComplexTorus 1 τ,
      (∀ i : Fin 16, ∀ u : triangleWeightSpace (caseFaces j),
        u.val ∈ faceWeights (triangleVertexSet (liftedVertices (caseLift j i))) →
        H u = complexTorusProjection 1 τ (Complex.equivRealProdCLM.symm
          (physicalPoint y (facePeriodPoint 0 1 (casePoints j) (caseLift j i) u.val)))) ∧
      ∀ e ∈ (rayCase j).1.edges,
        let d := asReal (markedDisplacement (rayCase j).1 (rayCase j).2 e.1 e.2)
        StrictShortest (1/2) y (d.1+d.2/2) d.2 := by
  let τ : ℂ := ((1/2 : ℝ) : ℂ)+y*Complex.I
  have hsim : complexSimilarity 1 false = id := by funext z; simp [complexSimilarity]
  have hL : complexSimilarity 1 false '' complexLattice 1 τ = complexLattice 1 τ := by
    rw [hsim,Set.image_id]
  obtain ⟨J,hJ⟩ := complexTorus_rebase 1 τ (1/2) y hy.ne' 1 false one_ne_zero hL
  refine ⟨(intrinsicHomeomorph j).trans J,?_,fun e he => caseEdges_shortest j e he hw⟩
  intro i u hu
  rw [Homeomorph.trans_apply,intrinsicHomeomorph_on_face j i u hu]
  let p := facePeriodPoint 0 1 (casePoints j) (caseLift j i) u.val
  have hh := hJ (physicalPoint y p)
  rw [periodCoordinates_physicalPoint hy.ne'] at hh
  simpa only [complexSimilarity,Bool.false_eq_true,ite_false,one_mul] using hh

end OrigamiTorus.Winding.Hexagonal
