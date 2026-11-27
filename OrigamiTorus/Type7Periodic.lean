module

public import OrigamiTorus.PeriodicArea
public import OrigamiTorus.Type7Rectangular
import Mathlib.Tactic

/-! The period shifts supplied by developing the marked Type 7 face list. -/

@[expose] public section

namespace OrigamiTorus.Type7

/-- Face lifts in the marking given by the walks 4234 and 5205. -/
def markedLiftedFaces : Fin 16 → LiftedFace :=
  ![((3,0),(5,0),(6,0)), ((3,0),(2,0),(5,0)), ((3,0),(6,0),(4,(1,0))),
    ((3,0),(0,0),(2,0)), ((3,0),(4,(1,0)),(1,0)), ((3,0),(1,0),(0,0)),
    ((5,0),(0,(0,-1)),(6,0)), ((5,0),(2,0),(4,0)), ((5,0),(4,0),(7,(-1,0))),
    ((5,0),(7,(-1,0)),(0,(0,-1))), ((6,0),(7,0),(4,(1,0))),
    ((6,0),(0,(0,-1)),(1,(0,-1))), ((6,0),(1,(0,-1)),(7,0)),
    ((2,0),(1,(-1,0)),(4,0)), ((2,(1,-1)),(0,(1,-1)),(7,0)),
    ((2,(1,-1)),(7,0),(1,(0,-1)))]

theorem markedLiftedFaces_labels :
    (List.finRange 16).map (fun j => liftedVertices (markedLiftedFaces j)) = faces := by
  decide +kernel

/-- The ordinary link cycles in positive face order. -/
def markedLinkCycle : Vertex → List Vertex :=
  ![[2,3,1,6,5,7], [4,2,7,6,0,3], [0,7,1,4,5,3], [5,6,4,1,0,2],
    [3,6,7,5,2,1], [3,2,4,7,0,6], [3,5,0,1,7,4], [0,5,4,6,1,2]]

def markedEdgeShift (a b : Vertex) : Period :=
  let sides := (List.finRange 16).flatMap (fun i => liftedSides (markedLiftedFaces i))
  (sides.findSome? (fun e => if e.1 = a ∧ e.2.1 = b then some e.2.2 else none)).getD 0

def markedWalkShift (path : List Vertex) : Period :=
  (path.zip (path.drop 1)).foldl (fun d e => d+markedEdgeShift e.1 e.2) 0

theorem markedWalkShifts :
    markedWalkShift [4,2,3,4] = (1,0) ∧ markedWalkShift [5,2,0,5] = (0,1) := by
  decide +kernel

def markedPeriodicFaceSystem : PeriodicFaceSystem faces markedLiftedFaces where
  mem j := by
    rw [← markedLiftedFaces_labels]
    exact List.mem_map.mpr ⟨j,by simp,rfl⟩
  cover u := by
    obtain ⟨f,hf,hu⟩ := u.property
    rw [← markedLiftedFaces_labels] at hf
    obtain ⟨j,_,rfl⟩ := List.mem_map.mp hf
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

/-- The sum of lifted doubled areas is twice the area of the period cell. -/
theorem marked_periodicTotalArea (x w : ℝ) (q : Vertex → ℝ × ℝ) :
    (∑ j : Fin 16, periodicFaceArea x w q (markedLiftedFaces j)) = 2*w := by
  simp [Fin.sum_univ_succ,periodicFaceArea,markedLiftedFaces,translatePoint]
  ring

/-- Positive periodic lifts with the marked shifts give a triangulation of
the quotient by the two periods. -/
noncomputable def markedHomeomorph (x w : ℝ) (hw : 0 < w) (q : Vertex → ℝ × ℝ)
    (hpos : ∀ j, 0 < periodicFaceArea x w q (markedLiftedFaces j)) :
    triangleWeightSpace faces ≃ₜ MarkedTorus := by
  apply markedPeriodicFaceSystem.homeomorph x w hw q hpos
  simp_rw [latticeFaceArea_eq x w hw.ne']
  rw [← Finset.sum_div,marked_periodicTotalArea,mul_div_cancel_right₀ _ hw.ne']

theorem markedHomeomorph_apply (x w : ℝ) (hw : 0 < w) (q : Vertex → ℝ × ℝ)
    (hpos : ∀ j, 0 < periodicFaceArea x w q (markedLiftedFaces j)) (u : triangleWeightSpace faces) :
    markedHomeomorph x w hw q hpos u = periodicDevelopment markedLiftedFaces
      markedPeriodicFaceSystem.cover x w q u := by
  unfold markedHomeomorph
  exact markedPeriodicFaceSystem.homeomorph_apply x w hw q hpos _ u

end OrigamiTorus.Type7
