module

public import OrigamiTorus.Type2.BracketSigns
public import OrigamiTorus.Geometry.TriangleIntersections
import Mathlib.Tactic

/-! The affine dependence and sign partitions of Type 2 circuits. -/

public section

open Set
open scoped BigOperators

namespace OrigamiTorus.Type2

private def label (Q : List ℕ) (hQ : Q.length = 5) (i : Fin 5) : ℕ :=
  Q[i.val]'(by simpa only [hQ] using i.isLt)

private def coefficient (p : ℕ → Point3) (Q : List ℕ) (i : Fin 5) : ℝ :=
  if i.val % 2 = 0 then bracketValue p (Q.eraseIdx i.val) else -bracketValue p (Q.eraseIdx i.val)

private def coefficientLiteral (Q : List ℕ) (i : Fin 5) : Sign :=
  if i.val % 2 == 0 then bracket (Q.eraseIdx i.val) else negate (bracket (Q.eraseIdx i.val))

private theorem coefficient_relation (p : ℕ → Point3) (Q : List ℕ) (hlen : Q.length = 5) :
    (∑ i, coefficient p Q i) = 0 ∧
      (∑ i, coefficient p Q i • p (label Q hlen i)) = 0 := by
  rcases Q with _ | ⟨a,_ | ⟨b,_ | ⟨c,_ | ⟨d,_ | ⟨e,_ | ⟨f,Q⟩⟩⟩⟩⟩⟩ <;>
    simp only [List.length_cons,List.length_nil] at hlen <;> try omega
  constructor
  · simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero]
    change affineBracket (p b) (p c) (p d) (p e) +
      (-affineBracket (p a) (p c) (p d) (p e) +
      (affineBracket (p a) (p b) (p d) (p e) +
      (-affineBracket (p a) (p b) (p c) (p e) + affineBracket (p a) (p b) (p c) (p d)))) = 0
    linarith [affineBracket_circuitSum (p a) (p b) (p c) (p d) (p e)]
  · simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero]
    change affineBracket (p b) (p c) (p d) (p e) • p a +
      ((-affineBracket (p a) (p c) (p d) (p e)) • p b +
      (affineBracket (p a) (p b) (p d) (p e) • p c +
      ((-affineBracket (p a) (p b) (p c) (p e)) • p d + affineBracket (p a) (p b) (p c) (p d) • p e))) = 0
    simpa only [sub_eq_add_neg,neg_smul,add_assoc] using
      affineBracket_circuitVector (p a) (p b) (p c) (p d) (p e)

private theorem coefficientLiteral_truth (p : ℕ → Point3) (mark : ℕ → Bool)
    (hp : ∀ a b c d : ℕ, a < b → b < c → c < d → d < 8 →
      affineBracket (p a) (p b) (p c) (p d) ≠ 0)
    (Q : List ℕ) (hL : Q.length = 5) (hn : Q.Nodup) (hV : ∀ x ∈ Q, x < 8)
    (i : Fin 5) :
    coefficient p Q i ≠ 0 ∧
      (determinantAssignment p mark (coefficientLiteral Q i).1 = (coefficientLiteral Q i).2 ↔
        0 < coefficient p Q i) := by
  have hsub := List.eraseIdx_sublist Q i.val
  have hlen : (Q.eraseIdx i.val).length = 4 := by
    have hi : i.val < Q.length := by simpa only [hL] using i.isLt
    rw [List.length_eraseIdx_of_lt hi,hL]
  have hn' := hsub.nodup hn
  have hv' : ∀ x ∈ Q.eraseIdx i.val, x < 8 := fun x hx => hV x (hsub.subset hx)
  have hb := bracketValue_ne_zero_of_ordered_minors p hp hlen hn' hv'
  by_cases he : i.val % 2 = 0
  · simp only [coefficient,coefficientLiteral,beq_iff_eq,he,ite_true]
    exact ⟨hb,determinantAssignment_bracket p mark hlen hn' hv' hb⟩
  · simp only [coefficient,coefficientLiteral,beq_iff_eq,he,ite_false]
    exact ⟨neg_ne_zero.mpr hb,
      (determinantAssignment_negate_bracket p mark hlen hn' hv' hb).trans neg_pos.symm⟩

private def partitionLiterals (Q : List ℕ) (side : ℕ → Bool) : SignClause :=
  List.zipWith (fun l v => if side v then l else negate l) (circuit Q) Q

private theorem coefficientLiteral_mem_partition (Q : List ℕ) (hL : Q.length = 5)
    (side : ℕ → Bool) (i : Fin 5) :
    (if side (label Q hL i) then coefficientLiteral Q i else negate (coefficientLiteral Q i)) ∈
      partitionLiterals Q side := by
  have hcl : (circuit Q).length = 5 := by simp [circuit]
  have hi : i.val < (partitionLiterals Q side).length := by simp [partitionLiterals,hcl,hL]
  have hh : (partitionLiterals Q side)[i.val]'hi =
      (if side (label Q hL i) then coefficientLiteral Q i else negate (coefficientLiteral Q i)) := by
    simp only [partitionLiterals,List.getElem_zipWith,circuit,List.getElem_map,List.getElem_range,
      label,coefficientLiteral]
    rfl
  rw [← hh]
  exact List.getElem_mem hi

private theorem forbidden_partition_sound (p : ℕ → Point3) (mark : ℕ → Bool)
    (hp : ∀ a b c d : ℕ, a < b → b < c → c < d → d < 8 →
      affineBracket (p a) (p b) (p c) (p d) ≠ 0)
    (Q : List ℕ) (hL : Q.length = 5) (hn : Q.Nodup) (hV : ∀ x ∈ Q, x < 8) (side : ℕ → Bool)
    (hd : Disjoint (vertexHull p (Q.filter side).toFinset)
      (vertexHull p (Q.filter fun v => !side v).toFinset)) :
    ∀ C ∈ forbid (partitionLiterals Q side), ∃ l ∈ C, determinantAssignment p mark l.1 = l.2 := by
  classical
  let A := determinantAssignment p mark
  let vals := coefficient p Q
  let labels := label Q hL
  let ls := partitionLiterals Q side
  intro C hC
  by_contra! hc
  change ∀ l ∈ C, ¬ A l.1 = l.2 at hc
  have ho : ∃ orient : Bool, ∀ l ∈ ls, (A l.1 = l.2) ↔ orient = true := by
    change C ∈ [ls,ls.map negate] at hC
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hC
    rcases hC with hC | hC
    · exact ⟨false,fun l hl => by simp [hc l (hC.symm ▸ hl)]⟩
    · refine ⟨true,fun l hl => ?_⟩
      have hA : A l.1 = l.2 := not_not.mp (fun hf => hc (negate l)
        (hC.symm ▸ (List.mem_map_of_mem hl : negate l ∈ ls.map negate)) ((literal_negate_iff A l).mpr hf))
      simp [hA]
  obtain ⟨orient,ho⟩ := ho
  have hSem (i : Fin 5) := coefficientLiteral_truth p mark hp Q hL hn hV i
  have hAlign (i : Fin 5) : 0 < vals i ↔ side (labels i) = orient := by
    have hsign : A (coefficientLiteral Q i).1 = (coefficientLiteral Q i).2 ↔ 0 < vals i := (hSem i).2
    have ht := ho _ (coefficientLiteral_mem_partition Q hL side i)
    change (A (if side (labels i) then coefficientLiteral Q i else negate (coefficientLiteral Q i)).1 =
      (if side (labels i) then coefficientLiteral Q i else negate (coefficientLiteral Q i)).2) ↔ orient = true at ht
    cases orient <;> cases hs : side (labels i) <;>
      simp only [hs,Bool.false_eq_true,Bool.true_eq_false,ite_true,ite_false,literal_negate_iff,hsign,
        iff_false,iff_true,not_not] at ht ⊢ <;> tauto
  have hnz : vals ≠ 0 := fun he => (hSem 0).1 (congrFun he 0)
  have hrel := coefficient_relation p Q hL
  obtain ⟨x,hx,hy⟩ := vertexHull_inter_of_signed_relation (p ∘ labels) vals hnz hrel.1 hrel.2
  have hmono {S : Finset (Fin 5)} {T : Finset ℕ} (hST : ∀ i ∈ S, labels i ∈ T) :
      vertexHull (p ∘ labels) S ⊆ vertexHull p T := by
    apply convexHull_mono
    rintro _ ⟨i,hi,rfl⟩
    exact ⟨labels i,hST i hi,rfl⟩
  have hmem (i : Fin 5) : labels i ∈ Q := List.getElem_mem _
  have hpos : x ∈ vertexHull p (Q.filter fun v => side v == orient).toFinset := by
    apply hmono ?_ hx
    intro i hi
    have h := (hAlign i).mp (Finset.mem_filter.mp hi).2
    exact List.mem_toFinset.mpr (List.mem_filter.mpr ⟨hmem i,by simp [h]⟩)
  have hneg : x ∈ vertexHull p (Q.filter fun v => side v == !orient).toFinset := by
    apply hmono ?_ hy
    intro i hi
    have hn' : side (labels i) ≠ orient := fun he =>
      (Finset.mem_filter.mp hi).2.not_gt ((hAlign i).mpr he)
    have hne : side (labels i) = !orient := by
      cases hEq : side (labels i) <;> cases orient <;> simp_all only [Bool.not_true,Bool.not_false,
        Bool.true_eq_false,Bool.false_eq_true]
    exact List.mem_toFinset.mpr (List.mem_filter.mpr ⟨hmem i,by simp [hne]⟩)
  cases orient
  · exact Set.disjoint_left.mp hd.symm (by simpa using hpos) (by simpa using hneg)
  · exact Set.disjoint_left.mp hd (by simpa using hpos) (by simpa using hneg)

private theorem partitionLiterals_true (Q : List ℕ) (hL : Q.length = 5) :
    partitionLiterals Q (fun _ => true) = circuit Q := by
  have hlen : (circuit Q).length = Q.length := by simp [circuit,hL]
  have hzip (L : SignClause) (R : List ℕ) (he : L.length = R.length) :
      List.zipWith (fun (l : Sign) (_ : ℕ) => l) L R = L := by
    induction L generalizing R with
    | nil => simp
    | cons l L ih =>
      cases R with
      | nil => simp at he
      | cons a R => simp [List.zipWith,ih R (by simpa using he)]
  exact hzip _ _ hlen

private theorem circuitAt_sound (p : ℕ → Point3) (mark : ℕ → Bool)
    (hp : ∀ a b c d : ℕ, a < b → b < c → c < d → d < 8 →
      affineBracket (p a) (p b) (p c) (p d) ≠ 0)
    (hEF : ∀ a b f, a < 8 → b < 8 → isEdge a b = true → f ∈ faces → Disjoint ({a,b} : Finset ℕ) f.toFinset →
      Disjoint (vertexHull p {a,b}) (vertexHull p f.toFinset))
    (hSup : ∀ v (s : List ℕ), v < 8 → (∀ w ∈ s, w < 8 ∧ isEdge v w = true) → p v ∉ vertexHull p s.toFinset)
    (Q : List ℕ) (hL : Q.length = 5) (hn : Q.Nodup) (hV : ∀ x ∈ Q, x < 8) :
    ∀ C ∈ circuitAt Q, ∃ l ∈ C, determinantAssignment p mark l.1 = l.2 := by
  intro C hC
  simp only [circuitAt,List.append_assoc,List.mem_append,List.mem_flatMap,List.mem_filter] at hC
  rcases hC with hC | ⟨E,⟨hE,hEF'⟩,hC⟩ | ⟨v,⟨hv,hs⟩,hC⟩
  · have hD : Disjoint (vertexHull p (Q.filter fun _ => true).toFinset)
        (vertexHull p (Q.filter fun _ => !true).toFinset) := by simp [vertexHull]
    have hpart := forbidden_partition_sound p mark hp Q hL hn hV (fun _ => true) hD C
    rw [partitionLiterals_true Q hL] at hpart
    exact hpart hC
  · have hE' := (mem_choose_iff _ _ _).mp hE
    have hElen := hE'.2
    rcases E with _ | ⟨a,_ | ⟨b,_ | ⟨c,E⟩⟩⟩ <;>
      simp only [List.length_nil,List.length_cons] at hElen <;> try omega
    let f := Q.filter (fun v => !([a,b] : List ℕ).contains v)
    change (isEdge a b && faces.contains f) = true at hEF'
    simp only [Bool.and_eq_true,List.contains_iff_mem] at hEF'
    have hD : Disjoint ({a,b} : Finset ℕ) f.toFinset := by
      apply Finset.disjoint_left.mpr
      intro i hi hj
      have hHi : i ∈ ([a,b] : List ℕ) := by simpa using hi
      have hHj := (List.mem_filter.mp (List.mem_toFinset.mp hj)).2
      simp [hHi] at hHj
    have hLeft : (Q.filter (fun v => ([a,b] : List ℕ).contains v)).toFinset = {a,b} := by
      ext i
      simp only [List.mem_toFinset,List.mem_filter,List.contains_iff_mem]
      constructor
      · intro hi
        simpa using hi.2
      · intro hi
        have hMem : i ∈ ([a,b] : List ℕ) := by simpa using hi
        exact ⟨hE'.1.subset hMem,hMem⟩
    apply forbidden_partition_sound p mark hp Q hL hn hV (fun v => ([a,b] : List ℕ).contains v) _ C hC
    rw [hLeft]
    exact hEF a b f (hV a (hE'.1.subset (by simp))) (hV b (hE'.1.subset (by simp))) hEF'.1 hEF'.2 hD
  · let f := Q.filter (· != v)
    have hSup' : p v ∉ vertexHull p f.toFinset := hSup v f (hV v hv)
      (fun w hw => ⟨hV w (List.mem_filter.mp hw).1,List.all_eq_true.mp hs w hw⟩)
    have hLeft : (Q.filter (fun w => ([v] : List ℕ).contains w)).toFinset = {v} := by
      ext i
      simp only [List.mem_toFinset,List.mem_filter,List.contains_iff_mem,List.mem_singleton,Finset.mem_singleton]
      constructor
      · exact And.right
      · rintro rfl
        exact ⟨hv,rfl⟩
    have hRight : Q.filter (fun w => !([v] : List ℕ).contains w) = f := by
      congr 1
      funext w
      by_cases h : w = v <;> simp [bne,h]
    apply forbidden_partition_sound p mark hp Q hL hn hV (fun w => ([v] : List ℕ).contains w) _ C hC
    rw [hLeft,hRight]
    apply disjoint_left.mpr
    intro x hx hy
    have hx' : x = p v := by simpa [vertexHull] using hx
    exact hSup' (hx' ▸ hy)

/-- The circuit clauses hold for every general-position placement that
separates disjoint edges and faces and has a strict support at every vertex. -/
theorem determinantAssignment_satisfies_circuitClauses (p : ℕ → Point3) (mark : ℕ → Bool)
    (hp : ∀ a b c d : ℕ, a < b → b < c → c < d → d < 8 →
      affineBracket (p a) (p b) (p c) (p d) ≠ 0)
    (hEF : ∀ a b f, a < 8 → b < 8 → isEdge a b = true → f ∈ faces → Disjoint ({a,b} : Finset ℕ) f.toFinset →
      Disjoint (vertexHull p {a,b}) (vertexHull p f.toFinset))
    (hSup : ∀ v (s : List ℕ), v < 8 → (∀ w ∈ s, w < 8 ∧ isEdge v w = true) → p v ∉ vertexHull p s.toFinset) :
    ∀ C ∈ circuitClauses, ∃ l ∈ C, determinantAssignment p mark l.1 = l.2 := by
  intro C hC
  obtain ⟨Q,hQ,hC⟩ := List.mem_flatMap.mp hC
  have hQ' := (mem_choose_iff _ _ _).mp hQ
  exact circuitAt_sound p mark hp hEF hSup Q hQ'.2 (hQ'.1.nodup List.nodup_range)
    (fun x hx => List.mem_range.mp (hQ'.1.subset hx)) C hC

end OrigamiTorus.Type2
