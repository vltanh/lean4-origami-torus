module

public import OrigamiTorus.Geometry.AffineDeterminants
public import OrigamiTorus.Defs
import Mathlib.Data.List.Sort
import Mathlib.Data.List.Sublists
import Mathlib.Tactic

/-! The sign atoms for ordered affine determinants in the Type 2 encoding. -/

public section

namespace OrigamiTorus.Type2

/-- The determinant of four points indexed by a list of labels. -/
@[expose] def bracketValue (p : ℕ → Point3) : List ℕ → ℝ
  | [a,b,c,d] => affineBracket (p a) (p b) (p c) (p d)
  | _ => 0

private def signed (parity : Bool) (x : ℝ) : ℝ := if parity then -x else x

private theorem signed_xor (a b : Bool) (x : ℝ) :
    signed a (signed b x) = signed (a ^^ b) x := by
  cases a <;> cases b <;> simp [signed]

private theorem signed_not (a : Bool) (x : ℝ) : signed (!a) x = -signed a x := by
  cases a <;> simp [signed]

private theorem affineBracket_swap_first (a b c d : Point3) :
    affineBracket a b c d = -affineBracket b a c d := by
  simp only [affineBracket,determinant3,Prod.fst_sub,Prod.snd_sub]
  ring

private theorem affineBracket_swap_middle (a b c d : Point3) :
    affineBracket a b c d = -affineBracket a c b d := by
  simp only [affineBracket,determinant3,Prod.fst_sub,Prod.snd_sub]
  ring

private theorem affineBracket_swap_last (a b c d : Point3) :
    affineBracket a b c d = -affineBracket a b d c := by
  simp only [affineBracket,determinant3,Prod.fst_sub,Prod.snd_sub]
  ring

private theorem bracketValue_swap (p : ℕ → Point3) (left right : List ℕ) (a b : ℕ) :
    bracketValue p (left ++ a :: b :: right) = -bracketValue p (left ++ b :: a :: right) := by
  rcases left with _ | ⟨x,_ | ⟨y,_ | ⟨z,_ | ⟨w,_ | ⟨t,left⟩⟩⟩⟩⟩ <;>
    rcases right with _ | ⟨u,_ | ⟨v,_ | ⟨r,right⟩⟩⟩ <;>
    simp only [List.nil_append,List.cons_append,bracketValue,neg_zero] <;>
    first | exact affineBracket_swap_first _ _ _ _ | exact affineBracket_swap_middle _ _ _ _ |
      exact affineBracket_swap_last _ _ _ _

private theorem insertVertex_eq_orderedInsert (a : ℕ) (xs : List ℕ) :
    insertVertex a xs = xs.orderedInsert (· ≤ ·) a := by
  induction xs with
  | nil => simp only [insertVertex,List.orderedInsert_nil]
  | cons b xs ih => simp only [insertVertex,List.orderedInsert_cons,ih]

private theorem sortVertices_eq_insertionSort (xs : List ℕ) :
    sortVertices xs = xs.insertionSort (· ≤ ·) := by
  induction xs with
  | nil => simp only [sortVertices,List.insertionSort_nil]
  | cons b xs ih => simp only [sortVertices,List.insertionSort_cons,insertVertex_eq_orderedInsert,ih]

private theorem bracketValue_insert (p : ℕ → Point3) (a : ℕ) (xs : List ℕ)
    (hs : xs.Pairwise (· ≤ ·)) (left : List ℕ) :
    bracketValue p (left ++ a :: xs) =
      signed (xs.countP (· < a) % 2 == 1) (bracketValue p (left ++ insertVertex a xs)) := by
  induction xs generalizing left with
  | nil => simp [insertVertex,signed]
  | cons b xs ih =>
    by_cases hab : a ≤ b
    · have hzero : (b :: xs).countP (· < a) = 0 := by
        apply List.countP_eq_zero.mpr
        intro x hx
        simp only [decide_eq_true_eq]
        rcases List.mem_cons.mp hx with rfl | hx
        · exact not_lt_of_ge hab
        · exact not_lt_of_ge (hab.trans ((List.pairwise_cons.mp hs).1 _ hx))
      simp [insertVertex,signed,hab,hzero]
    · have hba : b < a := lt_of_not_ge hab
      have hc : (b :: xs).countP (· < a) = xs.countP (· < a) + 1 :=
        List.countP_cons_of_pos (by simpa using hba)
      have hpar (n : ℕ) : ((n + 1) % 2 == 1) = !(n % 2 == 1) := by
        by_cases h : n % 2 = 1
        · have hn : (n + 1) % 2 = 0 := by omega
          simp [h,hn]
        · have hn : (n + 1) % 2 = 1 := by omega
          simp [h,hn]
      have hstep := ih (List.pairwise_cons.mp hs).2 (left ++ [b])
      simp only [List.append_assoc,List.singleton_append] at hstep
      rw [bracketValue_swap p left xs a b,hstep,insertVertex,ite_eq_right hab,hc,hpar,signed_not]

private theorem bracketValue_sort_aux (p : ℕ → Point3) (xs left : List ℕ) :
    bracketValue p (left ++ xs) =
      signed (inversionParity xs) (bracketValue p (left ++ sortVertices xs)) := by
  induction xs generalizing left with
  | nil => simp [inversionParity,sortVertices,signed]
  | cons a xs ih =>
    have hsort : (sortVertices xs).Pairwise (· ≤ ·) := by
      rw [sortVertices_eq_insertionSort]
      exact List.pairwise_insertionSort _ _
    have hcount : (sortVertices xs).countP (· < a) = xs.countP (· < a) := by
      rw [sortVertices_eq_insertionSort]
      exact (List.perm_insertionSort (· ≤ ·) _).countP_eq _
    have ht := ih (left ++ [a])
    simp only [List.append_assoc,List.singleton_append] at ht
    rw [ht,bracketValue_insert p a _ hsort left,hcount,signed_xor,inversionParity,
      sortVertices,Bool.xor_comm]

/-- The inversion parity in the encoding is the sign of the actual
permutation used to sort the four determinant arguments. -/
private theorem bracketValue_sort (p : ℕ → Point3) (xs : List ℕ) :
    bracketValue p xs = signed (inversionParity xs) (bracketValue p (sortVertices xs)) := by
  simpa only [List.nil_append] using bracketValue_sort_aux p xs []

theorem mem_choose_iff {α : Type*} (k : ℕ) (xs ys : List α) :
    ys ∈ choose k xs ↔ ys.Sublist xs ∧ ys.length = k := by
  induction xs generalizing k ys with
  | nil => cases ys <;> cases k <;> simp [choose]
  | cons a xs ih =>
    cases k with
    | zero =>
      simp only [choose,List.mem_singleton,List.length_eq_zero_iff]
      exact ⟨fun he => ⟨he.symm ▸ List.nil_sublist _,he⟩,And.right⟩
    | succ k =>
      simp only [choose,List.mem_append,List.mem_map,List.sublist_cons_iff]
      constructor
      · rintro (⟨zs,hz,rfl⟩ | h)
        · obtain ⟨hS,hL⟩ := (ih k zs).mp hz
          exact ⟨Or.inr ⟨zs,rfl,hS⟩,by simpa using hL⟩
        · obtain ⟨hS,hL⟩ := (ih (k + 1) ys).mp h
          exact ⟨Or.inl hS,hL⟩
      · rintro ⟨hS | ⟨zs,rfl,hS⟩,hL⟩
        · exact Or.inr ((ih (k + 1) ys).mpr ⟨hS,hL⟩)
        · exact Or.inl ⟨zs,(ih k zs).mpr ⟨hS,by simpa using hL⟩,rfl⟩

private theorem sortVertices_mem_quadruples {xs : List ℕ}
    (hL : xs.length = 4) (hn : xs.Nodup) (hV : ∀ a ∈ xs, a < 8) :
    sortVertices xs ∈ quadruples := by
  rw [quadruples,mem_choose_iff,sortVertices_eq_insertionSort]
  have hp := List.perm_insertionSort (· ≤ ·) xs
  refine ⟨List.sublist_of_subperm_of_pairwise (List.subperm_of_subset (hp.nodup_iff.mpr hn) ?_)
      (List.pairwise_insertionSort _ _) (List.pairwise_lt_range.imp Nat.le_of_lt),hp.length_eq.trans hL⟩
  intro a ha
  exact List.mem_range.mpr (hV a (hp.mem_iff.mp ha))

/-- The first seventy atoms are the signs of the ordered minors. The remaining
atoms record the chosen incident faces. -/
@[expose] noncomputable def determinantAssignment (p : ℕ → Point3) (mark : ℕ → Bool)
    (i : ℕ) : Bool := by
  classical
  exact match quadruples[i]? with
  | some q => decide (0 < bracketValue p q)
  | none => mark i

/-- A literal for four distinct labels is true exactly when the ordered
determinant is positive. -/
theorem determinantAssignment_bracket (p : ℕ → Point3) (mark : ℕ → Bool) {xs : List ℕ}
    (hL : xs.length = 4) (hn : xs.Nodup) (hV : ∀ a ∈ xs, a < 8) (hB : bracketValue p xs ≠ 0) :
    determinantAssignment p mark (bracket xs).1 = (bracket xs).2 ↔ 0 < bracketValue p xs := by
  classical
  have hidx := List.getElem?_idxOf (sortVertices_mem_quadruples hL hn hV)
  rw [bracketValue_sort] at hB ⊢
  simp only [bracket,determinantAssignment,hidx]
  cases hp : inversionParity xs
  · simp [signed]
  · simp only [hp,Bool.not_true,signed,ite_true,decide_eq_false_iff_not,neg_pos] at hB ⊢
    exact ⟨fun h => lt_of_le_of_ne (not_lt.mp h) (fun he => hB (neg_eq_zero.mpr he)),not_lt_of_ge ∘ le_of_lt⟩

theorem literal_negate_iff (a : ℕ → Bool) (l : Sign) :
    a (negate l).1 = (negate l).2 ↔ ¬ a l.1 = l.2 := by
  rcases l with ⟨i,b⟩
  cases b <;> cases h : a i <;> simp [negate,h]

theorem determinantAssignment_negate_bracket (p : ℕ → Point3) (mark : ℕ → Bool) {xs : List ℕ}
    (hL : xs.length = 4) (hn : xs.Nodup) (hV : ∀ a ∈ xs, a < 8) (hB : bracketValue p xs ≠ 0) :
    determinantAssignment p mark (negate (bracket xs)).1 = (negate (bracket xs)).2 ↔
      bracketValue p xs < 0 := by
  rw [literal_negate_iff,determinantAssignment_bracket p mark hL hn hV hB,not_lt]
  exact ⟨fun h => lt_of_le_of_ne h hB,le_of_lt⟩

theorem bracketValue_ne_zero_of_ordered_minors (p : ℕ → Point3)
    (hp : ∀ a b c d : ℕ, a < b → b < c → c < d → d < 8 →
      affineBracket (p a) (p b) (p c) (p d) ≠ 0)
    {xs : List ℕ} (hL : xs.length = 4) (hn : xs.Nodup) (hV : ∀ a ∈ xs, a < 8) :
    bracketValue p xs ≠ 0 := by
  have hmem := sortVertices_mem_quadruples hL hn hV
  rw [quadruples,mem_choose_iff] at hmem
  have hs := List.pairwise_lt_range.sublist hmem.1
  have hd : ∀ d ∈ sortVertices xs, d < 8 := fun _ h => List.mem_range.mp (hmem.1.subset h)
  rw [bracketValue_sort]
  generalize he : sortVertices xs = ys at hmem hs hd ⊢
  obtain ⟨_,h⟩ := hmem
  rcases ys with _ | ⟨a,_ | ⟨b,_ | ⟨c,_ | ⟨d,_ | ⟨e,ys⟩⟩⟩⟩⟩ <;>
    simp only [List.length_nil,List.length_cons] at h <;> try omega
  have h := List.pairwise_iff_getElem.mp hs
  have hb := hp a b c d (h 0 1 (by simp) (by simp) (by decide))
    (h 1 2 (by simp) (by simp) (by decide)) (h 2 3 (by simp) (by simp) (by decide))
    (hd d (by simp))
  change signed (inversionParity xs) (affineBracket (p a) (p b) (p c) (p d)) ≠ 0
  cases inversionParity xs <;> simp [signed,hb]

theorem determinantAssignment_mark (p : ℕ → Point3) (mark : ℕ → Bool) {i : ℕ}
    (hi : 70 ≤ i) : determinantAssignment p mark i = mark i := by
  have hlen : quadruples.length = 70 := by decide +kernel
  have he : quadruples[i]? = none := List.getElem?_eq_none_iff.mpr (hlen ▸ hi)
  simp only [determinantAssignment,he]

theorem determinantAssignment_normalized (p : ℕ → Point3) (mark : ℕ → Bool)
    (h : 0 < affineBracket (p 0) (p 1) (p 2) (p 3)) :
    determinantAssignment p mark 0 = true := by
  have h0 : quadruples[0]? = some [0,1,2,3] := by decide +kernel
  simp [determinantAssignment,h0,bracketValue,h]

end OrigamiTorus.Type2
