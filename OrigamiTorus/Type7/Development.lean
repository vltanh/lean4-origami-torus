module

public import OrigamiTorus.Lattice.FaceDevelopment
public import OrigamiTorus.Type4.Periodic
public import OrigamiTorus.Type4.MarkedShape
import Mathlib.Tactic

/-! The shared dual-tree development with either diagonal of the root quadrilateral. -/

@[expose] public section

namespace OrigamiTorus.Type7

def chartLifts (flipped : Bool) : Fin 16 → LiftedFace :=
  if flipped then Type4.markedLiftedFaces else markedLiftedFaces

def chartFaceSystem (flipped : Bool) : PeriodicFaceSystem (faceChoice flipped) (chartLifts flipped) :=
  match flipped with
  | false => markedPeriodicFaceSystem
  | true => Type4.markedPeriodicFaceSystem

/-- Face order shared by the planar development and the integer period table. -/
def markedFace (flipped : Bool) (j : Fin 16) : Triangle := liftedVertices (chartLifts flipped j)

theorem markedFace_mem (flipped : Bool) (j : Fin 16) : markedFace flipped j ∈ faceChoice flipped :=
  (chartFaceSystem flipped).mem j

theorem exists_markedFace (flipped : Bool) (f : Triangle) (hf : f ∈ faceChoice flipped) :
    ∃ j : Fin 16, markedFace flipped j = f := by
  cases flipped
  · change f ∈ faces at hf
    rw [← markedLiftedFaces_labels] at hf
    obtain ⟨j,_,hj⟩ := List.mem_map.mp hf
    exact ⟨j,hj⟩
  · exact (Type4.has_markedFace f).mp hf

def rootEdge (flipped : Bool) : Edge := if flipped then (2,6) else (3,5)

def rootEdgeSq (flipped : Bool) (q : Vertex → Point3) : ℝ :=
  spatialEdgeSq q (rootEdge flipped).1 (rootEdge flipped).2

theorem rootEdgeSq_pos (flipped : Bool) (q : Vertex → Point3)
    (he : Function.Injective (evaluateTriangles (faceChoice flipped) q)) : 0 < rootEdgeSq flipped q := by
  cases flipped
  · exact (spatial_triangle_regular q 3 5 6
      (not_collinear_of_injective_face _ q he 3 5 6
        (by decide +kernel) (by decide) (by decide) (by decide))).1
  · exact (spatial_triangle_regular q 2 6 3
      (not_collinear_of_injective_face _ q he 2 6 3
        (by decide +kernel) (by decide) (by decide) (by decide))).1

noncomputable def placeFace (flipped : Bool) (q : Vertex → Point3)
    (he : Function.Injective (evaluateTriangles (faceChoice flipped) q))
    (a b c : Vertex) (s : Bool) (A B : ℂ)
    (hf : (a ≠ b ∧ a ≠ c ∧ b ≠ c) ∧
      ∃ f ∈ faceChoice flipped, triangleVertexSet (a,b,c) ⊆ triangleVertexSet f)
    (hAB : rootEdgeSq flipped q*Complex.normSq (B-A) = spatialEdgeSq q a b) :
    DevelopedFace q (rootEdgeSq flipped q) (a,b,c) s :=
  DevelopedFace.onEdge q _ a b c s A B (rootEdgeSq_pos flipped q he)
    hf.1.1 hf.1.2.1 hf.1.2.2
    (not_collinear_of_injective_face _ q he a b c hf.2 hf.1.1 hf.1.2.1 hf.1.2.2) hAB

/-- The two root charts take the common diagonal to the directed unit segment. -/
noncomputable def rootChart (flipped : Bool) (q : Vertex → Point3)
    (he : Function.Injective (evaluateTriangles (faceChoice flipped) q)) (j : Fin 2) :
    DevelopedFace q (rootEdgeSq flipped q) (markedFace flipped (Fin.castLE (by decide) j)) true := by
  revert j
  cases flipped
  · let F0 := placeFace false q he 3 5 6 true 0 1 (by decide +kernel) (by simp [rootEdgeSq,rootEdge])
    let F1 := placeFace false q he 3 5 2 false 0 1 (by decide +kernel) (by simp [rootEdgeSq,rootEdge])
    exact Fin.cons F0 (Fin.cons F1.swapLast (fun j => Fin.elim0 j))
  · let F0 := placeFace true q he 2 6 3 true 0 1 (by decide +kernel) (by simp [rootEdgeSq,rootEdge])
    let F1 := placeFace true q he 2 6 5 false 0 1 (by decide +kernel) (by simp [rootEdgeSq,rootEdge])
    exact Fin.cons F0.rotate (Fin.cons F1.swapLast.rotate.rotate (fun j => Fin.elim0 j))

noncomputable def rootPoint (flipped : Bool) (q : Vertex → Point3)
    (he : Function.Injective (evaluateTriangles (faceChoice flipped) q)) (a : Vertex) : ℂ :=
  (rootChart flipped q he (if a = (if flipped then 5 else 2) then 1 else 0)).point a

theorem rootSideMetric (flipped : Bool) (q : Vertex → Point3)
    (he : Function.Injective (evaluateTriangles (faceChoice flipped) q))
    (a b : Vertex) (hs : (a,b) ∈ ([(3,6),(6,5),(2,3),(5,2)] : List Edge)) :
    rootEdgeSq flipped q * Complex.normSq (rootPoint flipped q he b-rootPoint flipped q he a) =
      spatialEdgeSq q a b := by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hs
  rcases hs with h|h|h|h <;> obtain ⟨rfl,rfl⟩ := Prod.mk.inj h <;> cases flipped
  · exact (rootChart false q he 0).edge_metric 3 (by decide +kernel) 6 (by decide +kernel)
  · exact (rootChart true q he 0).edge_metric 3 (by decide +kernel) 6 (by decide +kernel)
  · exact (rootChart false q he 0).edge_metric 6 (by decide +kernel) 5 (by decide +kernel)
  · exact (rootChart true q he 1).edge_metric 6 (by decide +kernel) 5 (by decide +kernel)
  · exact (rootChart false q he 1).edge_metric 2 (by decide +kernel) 3 (by decide +kernel)
  · exact (rootChart true q he 0).edge_metric 2 (by decide +kernel) 3 (by decide +kernel)
  · exact (rootChart false q he 1).edge_metric 5 (by decide +kernel) 2 (by decide +kernel)
  · exact (rootChart true q he 1).edge_metric 5 (by decide +kernel) 2 (by decide +kernel)

set_option maxHeartbeats 3000000 in
/-- Extend either pair of root charts along the common branches of the dual tree. -/
noncomputable def markedDevelopment (flipped : Bool) (q : Vertex → Point3)
    (he : Function.Injective (evaluateTriangles (faceChoice flipped) q)) (j : Fin 16) :
    DevelopedFace q (rootEdgeSq flipped q) (markedFace flipped j) true := by
  let put := placeFace flipped q he
  let hface (a b c : Vertex) (hf : (a ≠ b ∧ a ≠ c ∧ b ≠ c) ∧
      ∀ s : Bool, ∃ f ∈ faceChoice s, triangleVertexSet (a,b,c) ⊆ triangleVertexSet f) :=
    And.intro hf.1 (hf.2 flipped)
  let P := rootPoint flipped q he
  let F2 := put 3 6 4 true (P 3) (P 6) (hface 3 6 4 (by decide +kernel))
    (rootSideMetric flipped q he 3 6 (by decide +kernel))
  let F6 := put 6 5 0 true (P 6) (P 5) (hface 6 5 0 (by decide +kernel))
    (rootSideMetric flipped q he 6 5 (by decide +kernel))
  let F3 := put 2 3 0 true (P 2) (P 3) (hface 2 3 0 (by decide +kernel))
    (rootSideMetric flipped q he 2 3 (by decide +kernel))
  let F7 := put 5 2 4 true (P 5) (P 2) (hface 5 2 4 (by decide +kernel))
    (rootSideMetric flipped q he 5 2 (by decide +kernel))
  let F10 := put 4 6 7 true (F2.point 4) (F2.point 6) (hface 4 6 7 (by decide +kernel))
    (F2.edge_metric 4 (by decide +kernel) 6 (by decide +kernel))
  let F4 := put 3 4 1 true (F2.point 3) (F2.point 4) (hface 3 4 1 (by decide +kernel))
    (F2.edge_metric 3 (by decide +kernel) 4 (by decide +kernel))
  let F5 := put 3 1 0 true (F4.point 3) (F4.point 1) (hface 3 1 0 (by decide +kernel))
    (F4.edge_metric 3 (by decide +kernel) 1 (by decide +kernel))
  let F13 := put 4 2 1 true (F7.point 4) (F7.point 2) (hface 4 2 1 (by decide +kernel))
    (F7.edge_metric 4 (by decide +kernel) 2 (by decide +kernel))
  let F8 := put 5 4 7 true (F7.point 5) (F7.point 4) (hface 5 4 7 (by decide +kernel))
    (F7.edge_metric 5 (by decide +kernel) 4 (by decide +kernel))
  let F9 := put 5 7 0 true (F8.point 5) (F8.point 7) (hface 5 7 0 (by decide +kernel))
    (F8.edge_metric 5 (by decide +kernel) 7 (by decide +kernel))
  let F12 := put 7 6 1 true (F10.point 7) (F10.point 6) (hface 7 6 1 (by decide +kernel))
    (F10.edge_metric 7 (by decide +kernel) 6 (by decide +kernel))
  let F11 := put 1 6 0 true (F12.point 1) (F12.point 6) (hface 1 6 0 (by decide +kernel))
    (F12.edge_metric 1 (by decide +kernel) 6 (by decide +kernel))
  let F15 := put 7 1 2 true (F12.point 7) (F12.point 1) (hface 7 1 2 (by decide +kernel))
    (F12.edge_metric 7 (by decide +kernel) 1 (by decide +kernel))
  let F14 := put 7 2 0 true (F15.point 7) (F15.point 2) (hface 7 2 0 (by decide +kernel))
    (F15.edge_metric 7 (by decide +kernel) 2 (by decide +kernel))
  have same (j : Fin 16) (hj : 2 ≤ j.val) : markedFace flipped j = markedFace false j := by
    cases flipped
    · rfl
    · have h0 : j ≠ 0 := by intro h; subst j; simp at hj
      have h1 : j ≠ 1 := by intro h; subst j; simp at hj
      simp only [markedFace,chartLifts,ite_true,Bool.false_eq_true,ite_false,Type4.markedLiftedFaces,h0,h1]
  revert j
  refine Fin.cons (rootChart flipped q he 0) ?_
  refine Fin.cons (rootChart flipped q he 1) ?_
  refine Fin.cons ((same 2 (by decide)).symm ▸ F2) ?_
  refine Fin.cons ((same 3 (by decide)).symm ▸ F3.rotate) ?_
  refine Fin.cons ((same 4 (by decide)).symm ▸ F4) ?_
  refine Fin.cons ((same 5 (by decide)).symm ▸ F5) ?_
  refine Fin.cons ((same 6 (by decide)).symm ▸ F6.rotate) ?_
  refine Fin.cons ((same 7 (by decide)).symm ▸ F7) ?_
  refine Fin.cons ((same 8 (by decide)).symm ▸ F8) ?_
  refine Fin.cons ((same 9 (by decide)).symm ▸ F9) ?_
  refine Fin.cons ((same 10 (by decide)).symm ▸ F10.rotate) ?_
  refine Fin.cons ((same 11 (by decide)).symm ▸ F11.rotate) ?_
  refine Fin.cons ((same 12 (by decide)).symm ▸ F12.rotate) ?_
  refine Fin.cons ((same 13 (by decide)).symm ▸ F13.rotate) ?_
  refine Fin.cons ((same 14 (by decide)).symm ▸ F14.rotate) ?_
  exact Fin.cons ((same 15 (by decide)).symm ▸ F15.rotate.rotate) (fun j => Fin.elim0 j)

/-- Each entry names a parent, its child, and the labels on their common side. -/
def developmentTree (flipped : Bool) : Fin 15 → (Fin 16 × Fin 16) × Edge :=
  ![((0,1),rootEdge flipped), ((0,2),(3,6)), ((if flipped then 1 else 0,6),(5,6)),
    ((if flipped then 0 else 1,3),(2,3)), ((1,7),(2,5)), ((2,10),(4,6)), ((2,4),(3,4)),
    ((4,5),(1,3)), ((7,13),(2,4)), ((7,8),(4,5)), ((8,9),(5,7)), ((10,12),(6,7)),
    ((12,11),(1,6)), ((12,15),(1,7)), ((15,14),(2,7))]

/-- The two copies of each dual-tree edge coincide. -/
theorem markedDevelopment_tree (flipped : Bool) (q : Vertex → Point3)
    (he : Function.Injective (evaluateTriangles (faceChoice flipped) q)) (j : Fin 15) :
    let ((f,g),(a,b)) := developmentTree flipped j
    let P (i : Fin 16) := (markedDevelopment flipped q he i).point
    P f a = P g a ∧ P f b = P g b := by
  cases flipped <;> fin_cases j <;> exact ⟨rfl,rfl⟩

noncomputable def chartMarkingDisplacements (flipped : Bool) (s : Vertex → Vertex → ℝ) : ℂ × ℂ :=
  if flipped then Type4.flippedMarkingDisplacements s else markingDisplacements s

/-- The two displacements measured in the full development agree with the local marking. -/
theorem markedDevelopment_displacements (flipped : Bool) (q : Vertex → Point3)
    (he : Function.Injective (evaluateTriangles (faceChoice flipped) q)) :
    let P (i : Fin 16) := (markedDevelopment flipped q he i).point
    chartMarkingDisplacements flipped (spatialEdgeSq q) = (P 2 4-P 7 4,P 3 0-P 6 0) := by
  let s := spatialEdgeSq q
  cases flipped
  · let z₂ := triangleCorner s false 3 5 2
    let z₆ := triangleCorner s true 3 5 6
    apply Prod.ext
    · change z₆*triangleCorner s true 3 6 4 - (1+(z₂-1)*triangleCorner s true 5 2 4) =
          0+((0+(1-0)*z₆)-0)*triangleCorner s true 3 6 4 -
            (1+(0+(1-0)*z₂-1)*triangleCorner s true 5 2 4)
      ring
    · change z₂-z₂*triangleCorner s true 2 3 0 - (z₆+(1-z₆)*triangleCorner s true 6 5 0) =
          (0+(1-0)*z₂)+(0-(0+(1-0)*z₂))*triangleCorner s true 2 3 0 -
            ((0+(1-0)*z₆)+(1-(0+(1-0)*z₆))*triangleCorner s true 6 5 0)
      ring
  · let z₃ := triangleCorner s true 2 6 3
    let z₅ := triangleCorner s false 2 6 5
    apply Prod.ext
    · change (z₃+(1-z₃)*triangleCorner s true 3 6 4)-(z₅-z₅*triangleCorner s true 5 2 4) =
          ((0+(1-0)*z₃)+(1-(0+(1-0)*z₃))*triangleCorner s true 3 6 4) -
            ((0+(1-0)*z₅)+(0-(0+(1-0)*z₅))*triangleCorner s true 5 2 4)
      ring
    · change z₃*triangleCorner s true 2 3 0-(1+(z₅-1)*triangleCorner s true 6 5 0) =
          (0+((0+(1-0)*z₃)-0)*triangleCorner s true 2 3 0)-
            (1+((0+(1-0)*z₅)-1)*triangleCorner s true 6 5 0)
      ring

theorem chart_periodicTotalArea (flipped : Bool) (x w : ℝ) (p : Vertex → ℝ × ℝ) :
    ∑ j : Fin 16, periodicFaceArea x w p (chartLifts flipped j) = 2*w := by
  cases flipped
  · exact marked_periodicTotalArea x w p
  · exact Type4.marked_periodicTotalArea x w p

noncomputable def chartHomeomorph (flipped : Bool) (x w : ℝ) (hw : 0 < w)
    (p : Vertex → ℝ × ℝ) (hpos : ∀ j, 0 < periodicFaceArea x w p (chartLifts flipped j)) :
    triangleWeightSpace (faceChoice flipped) ≃ₜ MarkedTorus := by
  apply (chartFaceSystem flipped).homeomorph x w hw p hpos
  simp_rw [latticeFaceArea_eq x w hw.ne']
  rw [← Finset.sum_div,chart_periodicTotalArea,mul_div_cancel_right₀ _ hw.ne']

theorem chartHomeomorph_apply (flipped : Bool) (x w : ℝ) (hw : 0 < w) (p : Vertex → ℝ × ℝ)
    (hpos : ∀ j, 0 < periodicFaceArea x w p (chartLifts flipped j))
    (u : triangleWeightSpace (faceChoice flipped)) :
    chartHomeomorph flipped x w hw p hpos u =
      periodicDevelopment (chartLifts flipped) (chartFaceSystem flipped).cover x w p u := by
  unfold chartHomeomorph
  exact (chartFaceSystem flipped).homeomorph_apply x w hw p hpos _ u

end OrigamiTorus.Type7
