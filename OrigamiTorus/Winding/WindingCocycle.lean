module

public import OrigamiTorus.EightVertex.Type5.Reconstruction
public import OrigamiTorus.EightVertex.Type7.Rectangular
import Mathlib.Tactic

/-! Integral cocycles on the Lutz Type 4, 5, and 7 face lists. -/

@[expose] public section

namespace OrigamiTorus.Winding

inductive Triangulation where
  | type4
  | type5
  | type7
  deriving DecidableEq

abbrev PeriodMatrix := Period × Period
abbrev EdgeCochain := Vertex → Vertex → Period

/-- Apply a matrix to a row of winding coordinates. -/
def mapPeriod (M : PeriodMatrix) (u : Period) : Period :=
  u.1 • M.1 + u.2 • M.2

def cyclePeriod (K : EdgeCochain) (f : Triangle) : Period :=
  K f.1 f.2.1 + K f.2.1 f.2.2 + K f.2.2 f.1

theorem mapPeriod_add (M : PeriodMatrix) (u v : Period) :
    mapPeriod M (u+v) = mapPeriod M u+mapPeriod M v := by
  simp only [mapPeriod,Prod.fst_add,Prod.snd_add,add_zsmul]
  abel

@[simp] theorem mapPeriod_zero (M : PeriodMatrix) : mapPeriod M 0 = 0 := by
  simp [mapPeriod]

theorem mapPeriod_neg (M : PeriodMatrix) (u : Period) : mapPeriod M (-u) = -mapPeriod M u := by
  simp only [mapPeriod,Prod.fst_neg,Prod.snd_neg,neg_zsmul,neg_add_rev]
  exact add_comm _ _

theorem cyclePeriod_mapPeriod (M : PeriodMatrix) (K : EdgeCochain) (f : Triangle) :
    cyclePeriod (fun a b => mapPeriod M (K a b)) f = mapPeriod M (cyclePeriod K f) := by
  simp only [cyclePeriod,mapPeriod_add]

namespace Triangulation

def faces : Triangulation → List Triangle
  | .type4 => Type7.type4Faces
  | .type5 => Type5.faces
  | .type7 => Type7.faces

def edges (k : Triangulation) : List Edge := (k.faces.flatMap faceEdges).eraseDups

/-- The parent of each nonzero label in a tree rooted at 0. -/
def parent (k : Triangulation) (v : Vertex) : Vertex :=
  match k, v with
  | .type4, 6 | .type5, 6 | .type5, 7 | .type7, 4 => 1
  | .type4, 7 => 2
  | _, _ => 0

def tree (k : Triangulation) : List Edge :=
  (List.finRange 8).tail.map fun v => (k.parent v,v)

def basisCycles : Triangulation → Triangle × Triangle
  | .type4 | .type5 => ((0,1,4),(0,1,5))
  | .type7 => ((0,1,2),(0,2,5))

def basisEdge (f : Triangle) : Edge := (f.2.1,f.2.2)

/-- All nonzero coefficients of the integral cocycle dual to the basis cycles. -/
def coefficients : Triangulation → List (Edge × Period)
  | .type4 => [((1,4),(1,0)),((1,5),(0,1)),((2,5),(0,1)),((2,6),(-1,0)),
      ((3,4),(1,0)),((3,6),(0,-1)),((3,7),(1,-1)),((4,6),(-1,0)),
      ((4,7),(0,-1)),((5,6),(0,-1)),((5,7),(0,-1)),((6,7),(1,0))]
  | .type5 => [((1,4),(1,0)),((1,5),(0,1)),((2,3),(-1,1)),((2,5),(0,1)),
      ((2,6),(-1,1)),((2,7),(-1,0)),((3,7),(0,-1)),((4,6),(-1,0)),
      ((4,7),(-1,0)),((5,6),(-1,0)),((5,7),(0,-1))]
  | .type7 => [((1,2),(1,0)),((1,7),(1,0)),((2,4),(-1,0)),((2,5),(0,1)),
      ((3,5),(0,1)),((3,6),(0,1)),((4,5),(1,1)),((4,6),(0,1)),
      ((4,7),(1,1)),((6,7),(1,0))]

def dualCocycle (k : Triangulation) (a b : Vertex) : Period :=
  if a = b then 0 else
    let v := ((coefficients k).lookup (orderedEdge a b)).getD 0
    if a < b then v else -v

def IsCocycle (k : Triangulation) (K : EdgeCochain) : Prop :=
  (∀ a b, K b a = -K a b) ∧ ∀ f ∈ k.faces, cyclePeriod K f = 0

def IsTreeNormalized (k : Triangulation) (K : EdgeCochain) : Prop :=
  ∀ e ∈ k.tree, K e.1 e.2 = 0

/-- Change vertex representatives by the specified lattice shifts. -/
def gaugeCochain (K : EdgeCochain) (p : Vertex → Period) (a b : Vertex) : Period :=
  K a b+p a-p b

theorem cyclePeriod_gauge (K : EdgeCochain) (p : Vertex → Period) (f : Triangle) :
    cyclePeriod (gaugeCochain K p) f = cyclePeriod K f := by
  simp only [cyclePeriod,gaugeCochain]
  abel

theorem gaugeCochain_valid {k : Triangulation} {K : EdgeCochain} (hK : k.IsCocycle K)
    (p : Vertex → Period) : k.IsCocycle (gaugeCochain K p) := by
  constructor
  · intro a b
    simp only [gaugeCochain,hK.1 a b]
    abel
  · intro f hf
    exact (cyclePeriod_gauge K p f).trans (hK.2 f hf)

private theorem tree_parent (k : Triangulation) : ∀ e ∈ k.tree,
    e.2 ≠ 0 ∧ e.1 = k.parent e.2 ∧ k.parent e.1 = 0 := by
  cases k <;> decide +kernel

private theorem cocycle_diagonal {k : Triangulation} {K : EdgeCochain} (hK : k.IsCocycle K)
    (a : Vertex) : K a a = 0 := by
  have h₁ := congrArg Prod.fst (hK.1 a a)
  have h₂ := congrArg Prod.snd (hK.1 a a)
  simp only [Prod.fst_neg,Prod.snd_neg] at h₁ h₂
  exact Prod.ext (by change (K a a).1 = 0; omega) (by change (K a a).2 = 0; omega)

/-- Period of the path from 0 to `v` in the chosen tree. Each path has
at most two edges. -/
def treePotential (k : Triangulation) (K : EdgeCochain) (v : Vertex) : Period :=
  if v = 0 then 0 else K 0 (k.parent v)+K (k.parent v) v

theorem gaugeCochain_normalized {k : Triangulation} {K : EdgeCochain} (hK : k.IsCocycle K) :
    k.IsTreeNormalized (gaugeCochain K (k.treePotential K)) := by
  rintro ⟨a,b⟩ he
  obtain ⟨hb,hab,ha⟩ := tree_parent k (a,b) he
  have hp : k.treePotential K a = K 0 a := by
    by_cases h : a = 0
    · subst a
      simp [treePotential,cocycle_diagonal hK]
    · simp [treePotential,h,ha,cocycle_diagonal hK]
  have hq : k.treePotential K b = K 0 a+K a b := by
    simp only [treePotential,ite_eq_right hb,← hab]
  rw [gaugeCochain,hp,hq]
  abel

theorem dualCocycle_valid (k : Triangulation) : k.IsCocycle k.dualCocycle := by
  constructor
  · cases k <;> decide +kernel
  · have h : ∀ f ∈ k.faces, cyclePeriod k.dualCocycle f = 0 := by
      cases k <;> decide +kernel
    exact h

theorem dualCocycle_normalized (k : Triangulation) : k.IsTreeNormalized k.dualCocycle := by
  unfold IsTreeNormalized
  cases k <;> decide +kernel

theorem dualCocycle_basis (k : Triangulation) :
    cyclePeriod k.dualCocycle k.basisCycles.1 = (1,0) ∧
    cyclePeriod k.dualCocycle k.basisCycles.2 = (0,1) := by
  cases k <;> decide +kernel

private def rotations (f : Triangle) : List Triangle :=
  let (a,b,c) := f
  [(a,b,c),(b,c,a),(c,a,b)]

private theorem cyclePeriod_eq_of_rotation {K : EdgeCochain} {f g : Triangle}
    (h : g ∈ rotations f) : cyclePeriod K g = cyclePeriod K f := by
  rcases f with ⟨a,b,c⟩
  simp only [rotations,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl | rfl | rfl <;> simp only [cyclePeriod] <;> abel

private def faceStep (S : List Edge) (f : Triangle) : List Edge :=
  (rotations f).filterMap fun (a,b,c) =>
    if S.contains (orderedEdge b c) && S.contains (orderedEdge c a)
    then some (orderedEdge a b) else none

private def extend (k : Triangulation) (S : List Edge) : List Edge :=
  (S ++ k.faces.flatMap (faceStep S)).eraseDups

private def seeds (k : Triangulation) : List Edge :=
  k.tree ++ [basisEdge k.basisCycles.1,basisEdge k.basisCycles.2]

private theorem directed_agreement {K L : EdgeCochain} {k : Triangulation}
    (hK : k.IsCocycle K) (hL : k.IsCocycle L) {a b : Vertex}
    (h : K (orderedEdge a b).1 (orderedEdge a b).2 = L (orderedEdge a b).1 (orderedEdge a b).2) :
    K a b = L a b := by
  rcases le_total a b with hle | hle
  · simpa [orderedEdge,min_eq_left hle,max_eq_right hle] using h
  · simp only [orderedEdge,min_eq_right hle,max_eq_left hle,hK.1 a b,hL.1 a b,neg_inj] at h
    exact h

private theorem ordered_agreement {K L : EdgeCochain} {k : Triangulation}
    (hK : k.IsCocycle K) (hL : k.IsCocycle L) {a b : Vertex}
    (h : K a b = L a b) :
    K (orderedEdge a b).1 (orderedEdge a b).2 = L (orderedEdge a b).1 (orderedEdge a b).2 := by
  rcases le_total a b with hle | hle
  · simpa [orderedEdge,min_eq_left hle,max_eq_right hle] using h
  · simp only [orderedEdge,min_eq_right hle,max_eq_left hle,hK.1 a b,hL.1 a b,h]

private theorem extend_agreement {K L : EdgeCochain} {k : Triangulation}
    (hK : k.IsCocycle K) (hL : k.IsCocycle L) {S : List Edge}
    (hS : ∀ e ∈ S, K e.1 e.2 = L e.1 e.2) :
    ∀ e ∈ k.extend S, K e.1 e.2 = L e.1 e.2 := by
  intro e he
  have hm : e ∈ S ++ k.faces.flatMap (faceStep S) := by simpa [extend] using he
  rcases List.mem_append.mp hm with hm | hm
  · exact hS e hm
  obtain ⟨f,hf,hstep⟩ := List.mem_flatMap.mp hm
  obtain ⟨⟨a,b,c⟩,hr,he⟩ := List.mem_filterMap.mp hstep
  dsimp only at he
  split at he
  next hbc =>
    rw [Bool.and_eq_true] at hbc
    have hKb := directed_agreement hK hL (hS (orderedEdge b c) (List.contains_iff_mem.mp hbc.1))
    have hKc := directed_agreement hK hL (hS (orderedEdge c a) (List.contains_iff_mem.mp hbc.2))
    have h₁ := (cyclePeriod_eq_of_rotation hr).trans (hK.2 f hf)
    have h₂ := (cyclePeriod_eq_of_rotation hr).trans (hL.2 f hf)
    change K a b+K b c+K c a = 0 at h₁
    change L a b+L b c+L c a = 0 at h₂
    have h := add_right_cancel (add_right_cancel (by simpa only [hKb,hKc] using h₁.trans h₂.symm))
    cases Option.some.inj he
    exact ordered_agreement hK hL h
  next => contradiction

private theorem seeds_cover (k : Triangulation) :
    ∀ e ∈ k.edges, e ∈ (k.extend^[16]) k.seeds := by
  cases k <;> decide +kernel

private theorem iterate_agreement {K L : EdgeCochain} {k : Triangulation}
    (hK : k.IsCocycle K) (hL : k.IsCocycle L) {S : List Edge}
    (hS : ∀ e ∈ S, K e.1 e.2 = L e.1 e.2) (n : ℕ) :
    ∀ e ∈ (k.extend^[n]) S, K e.1 e.2 = L e.1 e.2 := by
  induction n with
  | zero => exact hS
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact extend_agreement hK hL ih

private theorem basis_edge_tree (k : Triangulation) (f : Triangle)
    (hf : f = k.basisCycles.1 ∨ f = k.basisCycles.2) :
    (f.1,f.2.1) ∈ k.tree ∧ (f.1,f.2.2) ∈ k.tree := by
  cases k <;> rcases hf with rfl | rfl <;> decide +kernel

private theorem basis_period_eq_edge {k : Triangulation} {K : EdgeCochain}
    (hK : k.IsCocycle K) (ht : k.IsTreeNormalized K) {f : Triangle}
    (hf : f = k.basisCycles.1 ∨ f = k.basisCycles.2) :
    cyclePeriod K f = K f.2.1 f.2.2 := by
  obtain ⟨h₁,h₂⟩ := basis_edge_tree k f hf
  have ha := ht _ h₁
  have hb := ht _ h₂
  simp only [cyclePeriod,ha,zero_add,hK.1 f.1 f.2.2,hb,neg_zero,add_zero]

/-- A tree-normalized integral cocycle is determined on every edge by the
winding vectors of the two specified triangular cycles. -/
theorem cocycle_eq_mapPeriod {k : Triangulation} {K : EdgeCochain}
    (hK : k.IsCocycle K) (ht : k.IsTreeNormalized K) {a b : Vertex}
    (he : orderedEdge a b ∈ k.edges) :
    K a b = mapPeriod (cyclePeriod K k.basisCycles.1,cyclePeriod K k.basisCycles.2)
      (k.dualCocycle a b) := by
  let M := (cyclePeriod K k.basisCycles.1,cyclePeriod K k.basisCycles.2)
  let L : EdgeCochain := fun a b => mapPeriod M (k.dualCocycle a b)
  have hL : k.IsCocycle L := by
    constructor
    · intro a b
      simp only [L,(k.dualCocycle_valid).1 a b,mapPeriod_neg]
    · intro f hf
      simp only [L,cyclePeriod_mapPeriod,(k.dualCocycle_valid).2 f hf,mapPeriod_zero]
  have htL : k.IsTreeNormalized L := by
    intro e he
    simp only [L,k.dualCocycle_normalized e he,mapPeriod_zero]
  have hb₁ : cyclePeriod L k.basisCycles.1 = M.1 := by
    simp only [L,cyclePeriod_mapPeriod,(k.dualCocycle_basis).1]
    simp [mapPeriod]
  have hb₂ : cyclePeriod L k.basisCycles.2 = M.2 := by
    simp only [L,cyclePeriod_mapPeriod,(k.dualCocycle_basis).2]
    simp [mapPeriod]
  have hs : ∀ e ∈ k.seeds, K e.1 e.2 = L e.1 e.2 := by
    intro e he
    change e ∈ k.tree ++ [basisEdge k.basisCycles.1,basisEdge k.basisCycles.2] at he
    rcases List.mem_append.mp he with he | he
    · exact (ht e he).trans (htL e he).symm
    simp only [List.mem_cons,List.not_mem_nil,or_false] at he
    rcases he with rfl | rfl
    · exact (basis_period_eq_edge hK ht (Or.inl rfl)).symm.trans
        (hb₁.symm.trans (basis_period_eq_edge hL htL (Or.inl rfl)))
    · exact (basis_period_eq_edge hK ht (Or.inr rfl)).symm.trans
        (hb₂.symm.trans (basis_period_eq_edge hL htL (Or.inr rfl)))
  exact directed_agreement hK hL (iterate_agreement hK hL hs 16 _ (seeds_cover k _ he))

end Triangulation
end OrigamiTorus.Winding
