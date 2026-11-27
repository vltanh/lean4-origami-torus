module

public import OrigamiTorus.Type2BracketSigns
import Mathlib.Tactic

/-! Interpreting the Grassmann–Plücker clauses on actual affine determinants. -/

public section

namespace OrigamiTorus.Type2

private theorem truthVectors_length {n : ℕ} {p : List Bool} (hp : p ∈ truthVectors n) :
    p.length = n := by
  induction n generalizing p with
  | zero =>
    simpa [truthVectors,List.length_eq_zero_iff] using hp
  | succ n ih =>
    simp only [truthVectors,List.mem_append,List.mem_map] at hp
    rcases hp with ⟨q,hq,rfl⟩ | ⟨q,hq,rfl⟩ <;> rw [List.length_cons,ih hq]

private theorem decide_mul_pos (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) :
    decide (0 < a * b) = (decide (0 < a) == decide (0 < b)) := by
  rcases lt_or_gt_of_ne ha with ha | ha <;> rcases lt_or_gt_of_ne hb with hb | hb
  · simp [ha.not_gt,hb.not_gt,mul_pos_of_neg_of_neg ha hb]
  · simp [ha.not_gt,hb,(mul_neg_of_neg_of_pos ha hb).not_gt]
  · simp [ha,hb.not_gt,(mul_neg_of_pos_of_neg ha hb).not_gt]
  · simp [ha,hb,mul_pos ha hb]

private theorem unequal_product_signs_of_sum_zero (a b c d e f : ℝ)
    (ha : a ≠ 0) (hb : b ≠ 0)
    (h : a * b + c * d + e * f = 0) :
    ¬ (decide (0 < a * b) = decide (0 < c * d) ∧
      decide (0 < c * d) = decide (0 < e * f)) := by
  rintro ⟨h₁,h₂⟩
  by_cases ha' : 0 < a*b
  · have hc' : 0 < c*d := of_decide_eq_true (h₁.symm.trans (decide_eq_true ha'))
    have he' : 0 < e*f := of_decide_eq_true (h₂.symm.trans (decide_eq_true hc'))
    linarith
  · have hc' : ¬ 0 < c*d := of_decide_eq_false (h₁.symm.trans (decide_eq_false ha'))
    have he' : ¬ 0 < e*f := of_decide_eq_false (h₂.symm.trans (decide_eq_false hc'))
    linarith [lt_of_le_of_ne (not_lt.mp ha') (mul_ne_zero ha hb),not_lt.mp hc',not_lt.mp he']

private theorem truth_of_falsified_pattern (assignment : ℕ → Bool) (l : Sign) (b : Bool)
    (h : ¬ assignment (if b then negate l else l).1 = (if b then negate l else l).2) :
    decide (assignment l.1 = l.2) = b := by
  cases b
  · exact decide_eq_false h
  · exact decide_eq_true (not_not.mp (fun hn => h ((literal_negate_iff assignment l).mpr hn)))

private theorem pluckerAt_sound (p : ℕ → Point3) (mark : ℕ → Bool)
    (hp : ∀ a b c d : ℕ, a < b → b < c → c < d → d < 8 →
      affineBracket (p a) (p b) (p c) (p d) ≠ 0)
    (s t a b c d : ℕ) (hlabels : ∀ x ∈ [s,t,a,b,c,d], x < 8) (hn : [s,t,a,b,c,d].Nodup)
    (C : SignClause) (hC : C ∈ pluckerAt [s,t] [a,b,c,d]) :
    ∃ l ∈ C, determinantAssignment p mark l.1 = l.2 := by
  classical
  let assignment := determinantAssignment p mark
  let vals := fun u v => bracketValue p [s,t,u,v]
  let atom := fun u v => bracket [s,t,u,v]
  let ls := [atom a b,atom c d,negate (atom a c),atom b d,atom a d,atom b c]
  let toggle := fun (l : Sign) (b : Bool) => if b then negate l else l
  simp only [pluckerAt,List.mem_map,List.mem_filter] at hC
  obtain ⟨pat,⟨hp₆,hsame⟩,rfl⟩ := hC
  have hlen := truthVectors_length hp₆
  rcases pat with _ | ⟨p₁,_ | ⟨p₂,_ | ⟨p₃,_ | ⟨p₄,_ | ⟨p₅,_ | ⟨p₆,_ | ⟨p₇,pat⟩⟩⟩⟩⟩⟩⟩ <;>
    simp only [List.length_cons,List.length_nil] at hlen <;> try omega
  simp only [Bool.and_eq_true] at hsame
  have hargs {u v : ℕ} (hs : [u,v].Sublist [a,b,c,d]) :
      [s,t,u,v].Nodup ∧ (∀ x ∈ [s,t,u,v], x < 8) ∧ vals u v ≠ 0 := by
    have hsub : [s,t,u,v].Sublist [s,t,a,b,c,d] := hs.cons_cons t |>.cons_cons s
    have hn' := hsub.nodup hn
    have hv' : ∀ x ∈ [s,t,u,v], x < 8 := fun x hx => hlabels x (hsub.subset hx)
    exact ⟨hn',hv',bracketValue_ne_zero_of_ordered_minors p hp rfl hn' hv'⟩
  have hab := hargs (u := a) (v := b) (by simp)
  have hcd := hargs (u := c) (v := d) (by simp)
  have hac := hargs (u := a) (v := c) (by simp [List.sublist_cons_iff])
  have hbd := hargs (u := b) (v := d) (by simp [List.sublist_cons_iff])
  have had := hargs (u := a) (v := d) (by simp [List.sublist_cons_iff])
  have hbc := hargs (u := b) (v := c) (by simp [List.sublist_cons_iff])
  have htrue {u v : ℕ} (h : [s,t,u,v].Nodup ∧ (∀ x ∈ [s,t,u,v], x < 8) ∧ vals u v ≠ 0) :
      assignment (atom u v).1 = (atom u v).2 ↔ 0 < vals u v :=
    determinantAssignment_bracket p mark rfl h.1 h.2.1 h.2.2
  have hneg : assignment (negate (atom a c)).1 = (negate (atom a c)).2 ↔ 0 < -vals a c :=
    (determinantAssignment_negate_bracket p mark rfl hac.1 hac.2.1 hac.2.2).trans neg_pos.symm
  by_contra! hfail
  change ∀ l ∈ List.zipWith toggle ls [p₁,p₂,p₃,p₄,p₅,p₆], ¬ assignment l.1 = l.2 at hfail
  have hat (l : Sign) (b : Bool) (h : toggle l b ∈ List.zipWith toggle ls [p₁,p₂,p₃,p₄,p₅,p₆]) :
      decide (assignment l.1 = l.2) = b := truth_of_falsified_pattern assignment l b (hfail _ h)
  have hvalue {l : Sign} {b : Bool} {w : ℝ} (he : assignment l.1 = l.2 ↔ 0 < w)
      (hb : toggle l b ∈ List.zipWith toggle ls [p₁,p₂,p₃,p₄,p₅,p₆]) :
      decide (0 < w) = b := by
    simpa only [he] using hat l b hb
  have h₁ : decide (0 < vals a b) = p₁ := hvalue (htrue hab) (by simp [ls,List.zipWith])
  have h₂ : decide (0 < vals c d) = p₂ := hvalue (htrue hcd) (by simp [ls,List.zipWith])
  have h₃ : decide (0 < -vals a c) = p₃ := hvalue hneg (by simp [ls,List.zipWith])
  have h₄ : decide (0 < vals b d) = p₄ := hvalue (htrue hbd) (by simp [ls,List.zipWith])
  have h₅ : decide (0 < vals a d) = p₅ := hvalue (htrue had) (by simp [ls,List.zipWith])
  have h₆ : decide (0 < vals b c) = p₆ := hvalue (htrue hbc) (by simp [ls,List.zipWith])
  have hsum : vals a b * vals c d + (-vals a c) * vals b d + vals a d * vals b c = 0 := by
    rw [neg_mul,← sub_eq_add_neg]
    exact affineBracket_plucker (p s) (p t) (p a) (p b) (p c) (p d)
  refine unequal_product_signs_of_sum_zero _ _ _ _ _ _ hab.2.2 hcd.2.2 hsum ?_
  rw [decide_mul_pos _ _ hab.2.2 hcd.2.2,decide_mul_pos _ _ (neg_ne_zero.mpr hac.2.2) hbd.2.2,
    decide_mul_pos _ _ had.2.2 hbc.2.2,h₁,h₂,h₃,h₄,h₅,h₆]
  exact ⟨eq_of_beq hsame.1,eq_of_beq hsame.2⟩

/-- Every Plücker clause in the formula holds for the signs of an actual
placement in general position. -/
theorem determinantAssignment_satisfies_pluckerClauses (p : ℕ → Point3) (mark : ℕ → Bool)
    (hp : ∀ a b c d : ℕ, a < b → b < c → c < d → d < 8 →
      affineBracket (p a) (p b) (p c) (p d) ≠ 0) :
    ∀ C ∈ pluckerClauses, ∃ l ∈ C, determinantAssignment p mark l.1 = l.2 := by
  intro C hC
  simp only [pluckerClauses,List.mem_flatMap] at hC
  obtain ⟨S,hS,Q,hQ,hC⟩ := hC
  have hS' := (mem_choose_iff _ _ _).mp hS
  have hQ' := (mem_choose_iff _ _ _).mp hQ
  have hQv := hQ'.1.trans List.filter_sublist
  have hlabel (x : ℕ) (hx : x ∈ S ++ Q) : x < 8 := by
    apply List.mem_range.mp
    rcases List.mem_append.mp hx with hs | hq
    · exact hS'.1.subset hs
    · exact hQv.subset hq
  have hn : (S ++ Q).Nodup := by
    apply List.nodup_append'.mpr
    refine ⟨hS'.1.nodup List.nodup_range,hQv.nodup List.nodup_range,?_⟩
    intro x hx hy
    have hy' := (List.mem_filter.mp (hQ'.1.subset hy)).2
    simp [hx] at hy'
  obtain ⟨_,hSlen⟩ := hS'
  obtain ⟨_,hQlen⟩ := hQ'
  rcases S with _ | ⟨s,_ | ⟨t,_ | ⟨u,S⟩⟩⟩ <;>
    simp only [List.length_cons,List.length_nil] at hSlen <;> try omega
  rcases Q with _ | ⟨a,_ | ⟨b,_ | ⟨c,_ | ⟨d,_ | ⟨e,Q⟩⟩⟩⟩⟩ <;>
    simp only [List.length_cons,List.length_nil] at hQlen <;> try omega
  exact pluckerAt_sound p mark hp s t a b c d hlabel hn C hC

end OrigamiTorus.Type2
