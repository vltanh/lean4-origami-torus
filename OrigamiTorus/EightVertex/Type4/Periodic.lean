module

public import OrigamiTorus.EightVertex.Type7.Periodic
import Mathlib.Tactic

/-! The periodic Type 4 face list in the marking shared with Type 7. -/

@[expose] public section

namespace OrigamiTorus.Type4

/-- The diagonal flip replaces the two triangles at zero shift. All other
corners retain their Type 7 period shifts. -/
def markedLiftedFaces (j : Fin 16) : LiftedFace :=
  if j = 0 then ((6,0),(3,0),(2,0))
  else if j = 1 then ((6,0),(2,0),(5,0))
  else Type7.markedLiftedFaces j

theorem has_markedFace (f : Triangle) :
    f ∈ Type7.flippedFaces ↔ ∃ j : Fin 16, liftedVertices (markedLiftedFaces j) = f := by
  revert f
  decide +kernel

def markedLinkCycle : Vertex → List Vertex :=
  ![[2,3,1,6,5,7], [4,2,7,6,0,3], [0,7,1,4,5,6,3], [6,4,1,0,2],
    [3,6,7,5,2,1], [2,4,7,0,6], [3,2,5,0,1,7,4], [0,5,4,6,1,2]]

def markedEdgeShift (a b : Vertex) : Period :=
  let sides := (List.finRange 16).flatMap (fun i => liftedSides (markedLiftedFaces i))
  (sides.findSome? (fun e => if e.1 = a ∧ e.2.1 = b then some e.2.2 else none)).getD 0

def markedWalkShift (path : List Vertex) : Period :=
  (path.zip (path.drop 1)).foldl (fun d e => d+markedEdgeShift e.1 e.2) 0

theorem markedWalkShifts :
    markedWalkShift [4,2,3,4] = (1,0) ∧ markedWalkShift [5,2,0,5] = (0,1) := by
  decide +kernel

def markedPeriodicFaceSystem : PeriodicFaceSystem Type7.flippedFaces markedLiftedFaces where
  mem j := (has_markedFace _).mpr ⟨j,rfl⟩
  cover u := by
    obtain ⟨f,hf,hu⟩ := u.property
    obtain ⟨j,rfl⟩ := (has_markedFace f).mp hf
    exact ⟨j,hu⟩
  shared := by
    unfold SharedFacePeriods
    decide +kernel
  distinct := by decide +kernel
  reverseEdge := by decide +kernel
  link := markedLinkCycle
  link_nonempty := by decide +kernel
  edgeShift := markedEdgeShift
  link_corner v i := by
    fin_cases v <;> revert i <;> decide +kernel

/-- The oriented areas of the two replacement triangles add to the same
area as the two original triangles. -/
theorem marked_periodicTotalArea (x w : ℝ) (q : Vertex → ℝ × ℝ) :
    (∑ j : Fin 16, periodicFaceArea x w q (markedLiftedFaces j)) = 2*w := by
  calc
    _ = ∑ j : Fin 16, periodicFaceArea x w q (Type7.markedLiftedFaces j) := by
      norm_num [Fin.sum_univ_succ,periodicFaceArea,markedLiftedFaces,Type7.markedLiftedFaces,translatePoint]
      ring
    _ = _ := Type7.marked_periodicTotalArea x w q

/-- Positive Type 4 lifts with the marked shifts give degree one on the quotient. -/
noncomputable def markedHomeomorph (x w : ℝ) (hw : 0 < w) (q : Vertex → ℝ × ℝ)
    (hpos : ∀ j, 0 < periodicFaceArea x w q (markedLiftedFaces j)) :
    triangleWeightSpace Type7.flippedFaces ≃ₜ MarkedTorus := by
  apply markedPeriodicFaceSystem.homeomorph x w hw q hpos
  simp_rw [latticeFaceArea_eq x w hw.ne']
  rw [← Finset.sum_div,marked_periodicTotalArea,mul_div_cancel_right₀ _ hw.ne']

end OrigamiTorus.Type4
