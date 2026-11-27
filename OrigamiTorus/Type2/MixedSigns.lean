module

public import OrigamiTorus.Type2.BracketSigns
import Mathlib.Tactic

/-! The mixed-side witness clauses in the Type 2 determinant-sign formula. -/

public section

namespace OrigamiTorus.Type2

attribute [local irreducible] markedFaces quadruples

private def localFaces (v : ℕ) : List (List ℕ) := faces.filter (·.contains v)

private def eligibleNeighbors (v : ℕ) (f : List ℕ) : List ℕ :=
  vertices.filter fun w => isEdge v w && !f.contains w

private def faceAtom (v : ℕ) (f : List ℕ) : Sign :=
  (70 + markedFaces.idxOf (v,f),true)

private def chosenMarker (selected : ℕ → List ℕ) (i : ℕ) : Bool :=
  match markedFaces[i - 70]? with
  | some (v,f) => selected v == f
  | none => false

set_option maxHeartbeats 800000 in
private theorem faceAtom_truth (p : ℕ → Point3) (selected : ℕ → List ℕ)
    (v : ℕ) (hv : v ∈ ([0,1,2] : List ℕ)) {f : List ℕ} (hf : f ∈ localFaces v) :
    determinantAssignment p (chosenMarker selected) (70 + markedFaces.idxOf (v,f)) = true ↔
      selected v = f := by
  have hm : (v,f) ∈ markedFaces := by
    unfold markedFaces
    exact List.mem_flatMap.mpr ⟨v,hv,List.mem_map.mpr ⟨f,hf,rfl⟩⟩
  have hi := List.getElem?_idxOf hm
  rw [determinantAssignment_mark p (chosenMarker selected) (Nat.le_add_right 70 _)]
  simp only [chosenMarker,Nat.add_sub_cancel_left,hi,beq_iff_eq]

private theorem faceNeighbor_data {v w : ℕ} {f : List ℕ}
    (hf : f ∈ localFaces v) (hw : w ∈ eligibleNeighbors v f) :
    (f ++ [w]).length = 4 ∧ (f ++ [w]).Nodup ∧ ∀ a ∈ f ++ [w], a < 8 := by
  have hf' := (List.mem_filter.mp hf).1
  obtain ⟨hlen,hn,hbounds⟩ :
      f.length = 3 ∧ f.Nodup ∧ ∀ a ∈ f, a < 8 :=
    (show ∀ f ∈ faces, f.length = 3 ∧ f.Nodup ∧ ∀ a ∈ f, a < 8 by decide +kernel) f hf'
  have hw' := List.mem_filter.mp hw
  have hwf : w ∉ f := by
    have hn := hw'.2
    simp only [Bool.and_eq_true] at hn
    have hnot := hn.2
    simpa using hnot
  refine ⟨by simp [hlen],List.nodup_append'.mpr ⟨hn,by simp,?_⟩,?_⟩
  · intro x hx h
    obtain rfl := List.mem_singleton.mp h
    exact hwf hx
  · intro a ha
    rcases List.mem_append.mp ha with hf | hw
    · exact hbounds a hf
    · obtain rfl := List.mem_singleton.mp hw
      exact List.mem_range.mp hw'.1

/-- A choice of one genuinely mixed incident face at each marked vertex
satisfies every mixed-side clause of the formula. -/
theorem exists_assignment_satisfying_mixedClauses (p : ℕ → Point3)
    (hp : ∀ a b c d : ℕ, a < b → b < c → c < d → d < 8 →
      affineBracket (p a) (p b) (p c) (p d) ≠ 0)
    (h : ∀ v ∈ ([0,1,2] : List ℕ), ∃ f ∈ faces.filter (·.contains v),
      (∃ a ∈ vertices.filter (fun w => isEdge v w && !f.contains w), 0 < bracketValue p (f ++ [a])) ∧
      (∃ b ∈ vertices.filter (fun w => isEdge v w && !f.contains w), bracketValue p (f ++ [b]) < 0)) :
    ∃ mark : ℕ → Bool, ∀ C ∈ mixedClauses, ∃ l ∈ C, determinantAssignment p mark l.1 = l.2 := by
  classical
  let selected (v : ℕ) := if hv : v ∈ ([0,1,2] : List ℕ) then (h v hv).choose else []
  have hs (v : ℕ) (hv : v ∈ ([0,1,2] : List ℕ)) :
      selected v ∈ localFaces v ∧
        (∃ a ∈ eligibleNeighbors v (selected v), 0 < bracketValue p (selected v ++ [a])) ∧
        (∃ b ∈ eligibleNeighbors v (selected v), bracketValue p (selected v ++ [b]) < 0) := by
    simpa only [selected,dite_eq_left hv,localFaces,eligibleNeighbors] using (h v hv).choose_spec
  let mark := chosenMarker selected
  let A := determinantAssignment p mark
  refine ⟨mark,?_⟩
  intro C hC
  simp only [mixedClauses,List.mem_flatMap] at hC
  obtain ⟨v,hv,hC⟩ := hC
  let signs (f : List ℕ) := (eligibleNeighbors v f).map (fun w => bracket (f ++ [w]))
  change C ∈ ((localFaces v).flatMap (fun f =>
    [negate (faceAtom v f) :: signs f,negate (faceAtom v f) :: (signs f).map negate])) ++
    [(localFaces v).map (faceAtom v)] at hC
  rcases List.mem_append.mp hC with hC | hC
  · obtain ⟨f,hf,hC⟩ := List.mem_flatMap.mp hC
    have ht : A (faceAtom v f).1 = (faceAtom v f).2 ↔ selected v = f :=
      faceAtom_truth p selected v hv hf
    have hs' := hs v hv
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hC
    by_cases hm : selected v = f
    · rw [hm] at hs'
      rcases hC with rfl | rfl
      · obtain ⟨a,ha,hpos⟩ := hs'.2.1
        obtain ⟨hL,hn,hV⟩ := faceNeighbor_data hf ha
        have hnz := bracketValue_ne_zero_of_ordered_minors p hp hL hn hV
        exact ⟨bracket (f ++ [a]),List.mem_cons_of_mem _ (List.mem_map.mpr ⟨a,ha,rfl⟩),
          (determinantAssignment_bracket p mark hL hn hV hnz).mpr hpos⟩
      · obtain ⟨b,hb,hneg⟩ := hs'.2.2
        obtain ⟨hL,hn,hV⟩ := faceNeighbor_data hf hb
        have hnz := bracketValue_ne_zero_of_ordered_minors p hp hL hn hV
        have hmem : bracket (f ++ [b]) ∈ signs f := List.mem_map.mpr ⟨b,hb,rfl⟩
        exact ⟨negate (bracket (f ++ [b])),List.mem_cons_of_mem _ (List.mem_map_of_mem hmem),
          (determinantAssignment_negate_bracket p mark hL hn hV hnz).mpr hneg⟩
    · have hneg := (literal_negate_iff A (faceAtom v f)).mpr (fun h => hm (ht.mp h))
      rcases hC with rfl | rfl <;> exact ⟨negate (faceAtom v f),List.mem_cons_self,hneg⟩
  · obtain rfl := List.mem_singleton.mp hC
    have hmem := (hs v hv).1
    exact ⟨faceAtom v (selected v),List.mem_map.mpr ⟨_,hmem,rfl⟩,
      (faceAtom_truth p selected v hv hmem).mpr rfl⟩

end OrigamiTorus.Type2
