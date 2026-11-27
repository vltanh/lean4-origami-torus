module

public import OrigamiTorus.Type7.WideData
import Mathlib.Tactic

/-! Kernel replay of the disjoint edge–face tests for the endpoint chart. -/

public section

namespace OrigamiTorus.Type7

open Type4.StripLift

def endpointExtraPairs : List (Edge × Triangle) :=
  (disjointPairs faces).filter (fun p => !(disjointPairs flippedFaces).contains p)

def endpointExtraChunk (i : Fin 5) : List (Edge × Triangle) :=
  (endpointExtraPairs.drop (5*i.val)).take 5

set_option maxHeartbeats 0 in
check_wide_chunks endpointExtraChecks for 5 using endpointExtraChunk with (separationCheck endP endZ sgn)

/-- Check the 24 pairs specific to Type 7 and reuse the Type 4 endpoint
certificate for the pairs common to both face lists. -/
theorem endpointPairs : (disjointPairs faces).all (separationCheck endP endZ sgn) = true := by
  have hc : (List.finRange 5).flatMap endpointExtraChunk = endpointExtraPairs := by decide +kernel
  apply List.all_eq_true.mpr
  intro p hp
  by_cases hm : p ∈ disjointPairs flippedFaces
  · exact (List.all_eq_true.mp allPairs) p hm
  · have he : p ∈ endpointExtraPairs := by simp [endpointExtraPairs,hp,hm]
    rw [← hc] at he
    obtain ⟨i,_,hi⟩ := List.mem_flatMap.mp he
    exact (List.all_eq_true.mp (endpointExtraChecks i)) p hi

end OrigamiTorus.Type7
