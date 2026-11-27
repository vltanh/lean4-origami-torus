module

public import OrigamiTorus.Defs

/-! Kernel-reducible reverse unit propagation for the determinant-sign certificate. -/

@[expose] public section

namespace OrigamiTorus.Type2.RUP

/-- The usual signed representation of a literal, with atom numbers starting at 1. -/
def decode (i : Int) : Sign := (i.natAbs - 1, i > 0)

def trueLiteral (a : Nat → Bool) (l : Sign) : Prop := a l.1 = l.2

def trueClause (a : Nat → Bool) (c : SignClause) : Prop := ∃ l ∈ c, trueLiteral a l

private theorem not_trueLiteral_negate (a : Nat → Bool) (l : Sign) :
    ¬ trueLiteral a (negate l) ↔ trueLiteral a l := by
  cases l with
  | mk i b => cases b <;> cases h : a i <;> simp [trueLiteral, negate, h]

def remaining (trail c : SignClause) : SignClause :=
  c.filter fun l => !(trail.contains (negate l))

private theorem remaining_true {a : Nat → Bool} {trail c : SignClause}
    (ht : ∀ l ∈ trail, trueLiteral a l) (hc : trueClause a c) : trueClause a (remaining trail c) := by
  obtain ⟨l, hl, htrue⟩ := hc
  refine ⟨l, List.mem_filter.mpr ⟨hl, ?_⟩, htrue⟩
  simp only [Bool.not_eq_true', List.contains_eq_mem, decide_eq_false_iff_not]
  exact fun hm => ((not_trueLiteral_negate a l).mpr htrue) (ht _ hm)

/-- In each cited clause, delete literals whose negations are already on the trail.
An empty remainder is a contradiction. A singleton extends the trail. -/
def propagate (db : Array SignClause) (trail : SignClause) : List Nat → Bool
  | [] => false
  | j :: hints =>
    match db[j]? with
    | none => false
    | some c =>
      match remaining trail c with
      | [] => true
      | [l] => propagate db (l :: trail) hints
      | _ => false

private theorem propagate_sound {db : Array SignClause} {a : Nat → Bool}
    (hdb : ∀ c ∈ db, trueClause a c) (trail : SignClause)
    (ht : ∀ l ∈ trail, trueLiteral a l) (hints : List Nat)
    (h : propagate db trail hints = true) : False := by
  induction hints generalizing trail with
  | nil => simp [propagate] at h
  | cons j hints ih =>
    simp only [propagate] at h
    split at h
    · contradiction
    · rename_i c hget
      have hmem : c ∈ db := by
        obtain ⟨hj, hval⟩ := Array.getElem?_eq_some_iff.mp hget
        subst c
        exact Array.getElem_mem hj
      obtain ⟨l, hl, htrue⟩ := remaining_true ht (hdb c hmem)
      split at h
      · simp_all
      · rename_i lit heq
        apply ih (lit :: trail) _ h
        simp only [List.mem_cons, forall_eq_or_imp]
        have he : l = lit := by simpa [heq] using hl
        exact ⟨he ▸ htrue, ht⟩
      · contradiction



private theorem trueClause_of_propagate {db : Array SignClause} {a : Nat → Bool}
    (hdb : ∀ c ∈ db, trueClause a c) {c : SignClause} {hints : List Nat}
    (h : propagate db (c.map negate) hints = true) : trueClause a c := by
  refine Classical.byContradiction (fun hc => ?_)
  apply propagate_sound hdb _ _ _ h
  intro l hl
  obtain ⟨lit, hmem, rfl⟩ := List.mem_map.mp hl
  refine Classical.byContradiction (fun hfalse => ?_)
  exact hc ⟨lit, hmem, (not_trueLiteral_negate a lit).mp hfalse⟩

def checkLocal (premises : List (List Int)) (c : List Int) : Bool :=
  propagate (premises.map (List.map decode)).toArray
    (c.map (fun i => negate (decode i))) (List.range premises.length)

theorem derive {a : Nat → Bool} {premises : List (List Int)} {c : List Int}
    (hcheck : checkLocal premises c = true)
    (hpre : ∀ p ∈ premises, trueClause a (p.map decode)) :
    trueClause a (c.map decode) := by
  apply trueClause_of_propagate (hints := List.range premises.length)
    (db := (premises.map (List.map decode)).toArray) _ ?_
  · intro k hk
    rw [← Array.mem_toList_iff, List.toList_toArray] at hk
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hk
    exact hpre p hp
  · simpa only [checkLocal, List.map_map, Function.comp_def] using hcheck

end OrigamiTorus.Type2.RUP
