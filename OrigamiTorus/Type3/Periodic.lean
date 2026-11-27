module

public import OrigamiTorus.Type3.Rank
public import OrigamiTorus.Lattice.PeriodicArea
import OrigamiTorus.Type6.Signs
import Mathlib.Tactic

/-! The lifted triangles of the published Type 3 charts. -/

@[expose] public section

namespace OrigamiTorus.Type3

open Filter
open scoped Topology

/-- The fourteen common lifts and the two original triangles of the quadrilateral. -/
def faceLifts (j : Fin 16) : LiftedFace :=
  if j = 14 then ((0,0),(1,0),(2,0))
  else if j = 15 then ((1,0),(5,0),(2,0))
  else OrigamiTorus.liftedFaces j

theorem has_faceLift (f : Triangle) :
    f ∈ type3Faces ↔ ∃ j : Fin 16, liftedVertices (faceLifts j) = f := by
  revert f
  decide +kernel

def linkCycle : Vertex → List Vertex :=
  ![[1,2,4,3], [0,3,6,7,4,5,2], [0,1,5,7,6,4], [0,4,7,5,6,1],
    [0,2,6,5,1,7,3], [1,4,6,3,7,2], [1,3,5,4,2,7], [1,6,2,5,3,4]]

def edgeShift (a b : Vertex) : Period :=
  ((List.finRange 24).findSome? fun e =>
    let ((u,v),d) := edgeTable e
    if (a,b) = (u,v) then some d else if (b,a) = (u,v) then some (-d) else none).getD 0

def periodicFaceSystem : PeriodicFaceSystem type3Faces faceLifts where
  mem j := (has_faceLift _).mpr ⟨j,rfl⟩
  cover u := by
    obtain ⟨f,hf,hu⟩ := u.property
    obtain ⟨j,rfl⟩ := (has_faceLift f).mp hf
    exact ⟨j,hu⟩
  shared := by
    unfold SharedFacePeriods
    decide +kernel
  distinct := by decide +kernel
  reverseEdge := by decide +kernel
  link := linkCycle
  link_nonempty := by decide +kernel
  edgeShift := edgeShift
  link_corner v i := by
    fin_cases v <;> revert i <;> decide +kernel

set_option maxHeartbeats 0 in
theorem periodicTotalArea (x w : ℝ) (q : Vertex → ℝ × ℝ) :
    (∑ j : Fin 16, periodicFaceArea x w q (faceLifts j)) = 2*w := by
  calc
    _ = ∑ j : Fin 16, periodicFaceArea x w q (OrigamiTorus.liftedFaces j) := by
      norm_num [Fin.sum_univ_succ,periodicFaceArea,faceLifts,OrigamiTorus.liftedFaces,translatePoint]
      ring
    _ = _ := type6_periodicTotalArea x w q

theorem latticeTotalArea (x w : ℝ) (hw : w ≠ 0) (q : Vertex → ℝ × ℝ) :
    (∑ j : Fin 16, latticeFaceArea x w q (faceLifts j)) = 2 := by
  simp_rw [latticeFaceArea_eq x w hw]
  rw [← Finset.sum_div,periodicTotalArea,mul_div_cancel_right₀ _ hw]

/-- The unchanged triangles inherit positivity, and 012 and 152 have the
two opposite signs of the published diagonal, in the correct cyclic orders. -/
theorem intrinsicFacePositive (second : Bool) (x w : ℝ) (hd : chartDomain second x w)
    (j : Fin 16) : 0 < signedFaceArea second x w (faceLifts j) := by
  have hs := type6_flipSigns second x w hd
  have h₀ : signedFaceArea second x w (faceLifts 14) = area (stripPoint second x w) 1 2 0 := by
    norm_num [signedFaceArea,cornerPoint,faceLifts,translatePoint,intrinsicPoint,area]
    ring
  have h₁ : signedFaceArea second x w (faceLifts 15) = -area (stripPoint second x w) 1 2 5 := by
    norm_num [signedFaceArea,cornerPoint,faceLifts,translatePoint,intrinsicPoint,area]
    ring
  by_cases hj : j = 14
  · rw [hj,h₀]
    exact hs.1
  by_cases hk : j = 15
  · rw [hk,h₁]
    exact neg_pos.mpr hs.2.1
  · simpa only [faceLifts,ite_eq_right hj,ite_eq_right hk] using type6_intrinsicFacePositive second x w hd j

theorem eventually_intrinsicPositive (second : Bool) (x w : ℝ) (hd : chartDomain second x w) :
    ∀ᶠ m : SheetMotion in 𝓝 0, ∀ j : Fin 16,
      0 < periodicFaceArea x w (movedIntrinsicPoint second x w m) (faceLifts j) := by
  simp only [eventually_all]
  intro j
  have hbase : movedIntrinsicPoint second x w 0 = intrinsicPoint second x w := by
    funext v
    fin_cases v <;> simp [movedIntrinsicPoint,IntrinsicMotion]
  apply (isOpen_lt continuous_const (periodicFaceArea_continuous second x w (faceLifts j))).mem_nhds
  change 0 < periodicFaceArea x w (movedIntrinsicPoint second x w 0) (faceLifts j)
  rw [hbase]
  exact intrinsicFacePositive second x w hd j

def tableSide (e : EdgeIndex) : LiftedSide :=
  let ((a,b),d) := edgeTable e
  (a,b,d)

theorem side_index (j : Fin 16) (s : LiftedSide) (hs : s ∈ liftedSides (faceLifts j)) :
    ∃ e : EdgeIndex, s = tableSide e ∨ reverseSide s = tableSide e := by
  let table := (List.finRange 24).map tableSide
  have hc : ((List.finRange 16).flatMap fun j => liftedSides (faceLifts j)).all
      (fun r => table.contains r || table.contains (reverseSide r)) = true := by decide +kernel
  have hm : s ∈ (List.finRange 16).flatMap (fun j => liftedSides (faceLifts j)) :=
    List.mem_flatMap.mpr ⟨j, by simp, hs⟩
  have hor := List.all_eq_true.mp hc _ hm
  simp only [Bool.or_eq_true] at hor
  rcases hor with h | h
  · obtain ⟨e,_,he⟩ := List.mem_map.mp (List.contains_iff_mem.mp h)
    exact ⟨e, Or.inl he.symm⟩
  · obtain ⟨e,_,he⟩ := List.mem_map.mp (List.contains_iff_mem.mp h)
    exact ⟨e, Or.inr he.symm⟩

end OrigamiTorus.Type3
