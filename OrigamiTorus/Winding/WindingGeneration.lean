module

public import OrigamiTorus.Winding.WindingOrbits
public import OrigamiTorus.Lattice.PeriodicFaceConnectivity
import Mathlib.Tactic

/-! Testing unimodularity by closed edge walks. -/

@[expose] public section

namespace OrigamiTorus.Winding

open Triangulation (gaugeCochain)

theorem periodDet_mul (A B : PeriodMatrix) :
    periodDet (mulPeriodMatrix A B) = periodDet A*periodDet B := by
  simp only [periodDet,mulPeriodMatrix,mapPeriod_fst,mapPeriod_snd]
  ring

def walkPeriod (K : EdgeCochain) : Vertex → List Vertex → Period
  | _, [] => 0
  | a, b::tail => K a b+walkPeriod K b tail

def walkEnd : Vertex → List Vertex → Vertex
  | a, [] => a
  | _, b::tail => walkEnd b tail

private theorem walkEnd_snoc (a b : Vertex) (path : List Vertex) : walkEnd a (path++[b]) = b := by
  induction path generalizing a with
  | nil => rfl
  | cons t path ih => exact ih t

private theorem walkPeriod_snoc (K : EdgeCochain) (a b : Vertex) (path : List Vertex) :
    walkPeriod K a (path++[b]) = walkPeriod K a path+K (walkEnd a path) b := by
  induction path generalizing a with
  | nil => simp [walkPeriod,walkEnd]
  | cons t path ih =>
    simp only [List.cons_append,walkPeriod,walkEnd,ih,add_assoc]

theorem walkPeriod_gauge (K : EdgeCochain) (p : Vertex → Period) (a : Vertex) (path : List Vertex) :
    walkPeriod (gaugeCochain K p) a path = walkPeriod K a path + p a - p (walkEnd a path) := by
  induction path generalizing a with
  | nil => simp [walkPeriod,walkEnd]
  | cons b path ih =>
    simp only [walkPeriod,walkEnd,ih,gaugeCochain]
    abel

namespace Triangulation

def IsEdgeWalk (k : Triangulation) (a : Vertex) (path : List Vertex) : Prop :=
  (a::path).IsChain fun b c => orderedEdge b c ∈ k.edges

private theorem isEdgeWalk_snoc {k : Triangulation} {a b : Vertex} {path : List Vertex}
    (h : k.IsEdgeWalk a path) (he : orderedEdge (walkEnd a path) b ∈ k.edges) :
    k.IsEdgeWalk a (path++[b]) := by
  induction path generalizing a with
  | nil => exact List.isChain_cons_cons.mpr ⟨he,by simp⟩
  | cons t path ih =>
    have hp := List.isChain_cons_cons.mp h
    exact List.isChain_cons_cons.mpr ⟨hp.1,ih hp.2 he⟩

/-- A bijective quotient development with coherent marked edge shifts
has a closed edge walk for every period of the lattice. -/
theorem generating_walks_of_quotient {k : Triangulation} {K : EdgeCochain}
    {ι : Type*} [Finite ι] {lift : ι → LiftedFace} (S : PeriodicFaceSystem k.faces lift)
    (x w : ℝ) (q : Vertex → ℝ × ℝ) (F : triangleWeightSpace k.faces → MarkedTorus)
    (hf : Function.Bijective F)
    (hF : ∀ j u, u.val ∈ faceWeights (triangleVertexSet (liftedVertices (lift j))) →
      F u = projectPeriods (facePeriodPoint x w q (lift j) u.val))
    (hLift : ∀ j a b, a ∈ triangleVertexSet (liftedVertices (lift j)) →
      b ∈ triangleVertexSet (liftedVertices (lift j)) → a ≠ b →
      K a b = facePeriod (lift j) b-facePeriod (lift j) a)
    (j₀ : ι) (d : Period) :
    ∃ a path, k.IsEdgeWalk a path ∧ walkEnd a path = a ∧ walkPeriod K a path = d := by
  let a := (lift j₀).1.1
  let base := facePeriod (lift j₀) a
  have ha : a ∈ triangleVertexSet (liftedVertices (lift j₀)) := by
    rcases h : lift j₀ with ⟨u,v,w⟩
    simp [a,h,liftedVertices,triangleVertexSet_eq]
  let Labels (p : ι × Period) := triangleVertexSet (liftedVertices (lift p.1))
  let P (p : ι × Period) (b : Vertex) := facePeriod (lift p.1) b+p.2
  let Reach (p : ι × Period) (b : Vertex) :=
    ∃ path, k.IsEdgeWalk a path ∧ walkEnd a path = b ∧ walkPeriod K a path = P p b-base
  have extendReach (p : ι × Period) (c b : Vertex) (hc : c ∈ Labels p) (hb : b ∈ Labels p)
      (hr : Reach p c) : Reach p b := by
    by_cases h : c = b
    · simpa only [h] using hr
    obtain ⟨path,hp,hend,hperiod⟩ := hr
    have he : orderedEdge c b ∈ k.edges := (edge_in_face k c b).mpr
      ⟨h,liftedVertices (lift p.1),S.mem p.1,hc,hb⟩
    have he' : orderedEdge (walkEnd a path) b ∈ k.edges := by rw [hend]; exact he
    refine ⟨path++[b],isEdgeWalk_snoc hp he',walkEnd_snoc a b path,?_⟩
    rw [walkPeriod_snoc,hend,hperiod,hLift p.1 c b hc hb h]
    dsimp [P]
    abel
  have hinit : Reach (j₀,0) a := ⟨[],by simp [IsEdgeWalk],rfl,by simp [walkPeriod,P,base]⟩
  let Shares (p r : ι × Period) := ∃ b : Vertex, b ∈ Labels p ∧ b ∈ Labels r ∧ P p b = P r b
  have h := S.translated_tiles_connected x w q F hf hF (j₀,0) (j₀,d)
  have hr {r : ι × Period} (hh : Relation.ReflTransGen Shares (j₀,0) r) :
      ∀ b ∈ Labels r, Reach r b := by
    induction hh with
    | refl =>
      intro b hb
      exact extendReach (j₀,0) a b ha hb hinit
    | tail _ hstep ih =>
      obtain ⟨c,hc₁,hc₂,hc⟩ := hstep
      intro b hb
      obtain ⟨path,hw,he,hm⟩ := ih c hc₁
      exact extendReach _ c b hc₂ hb ⟨path,hw,he,hm.trans (congrArg (fun v : Period => v-base) hc)⟩
  obtain ⟨path,hpath,hend,hperiod⟩ := hr h a ha
  refine ⟨a,path,hpath,hend,hperiod.trans ?_⟩
  simp [P,base,add_comm]

theorem walkPeriod_eq_mapPeriod {k : Triangulation} {K : EdgeCochain} (hK : k.IsCocycle K)
    (ht : k.IsTreeNormalized K) {a : Vertex} {path : List Vertex} (hp : k.IsEdgeWalk a path) :
    walkPeriod K a path = mapPeriod (cyclePeriod K k.basisCycles.1,cyclePeriod K k.basisCycles.2)
      (walkPeriod k.dualCocycle a path) := by
  induction path generalizing a with
  | nil => simp [walkPeriod]
  | cons b path ih =>
    have h := List.isChain_cons_cons.mp hp
    simp only [walkPeriod,mapPeriod_add,cocycle_eq_mapPeriod hK ht h.1,ih h.2]

/-- Two closed edge walks with the primitive coordinate periods suffice to
prove that the marking matrix is unimodular. -/
theorem marking_unimodular_of_generating_walks {k : Triangulation} {K : EdgeCochain}
    (hK : k.IsCocycle K)
    (hgen : ∀ u ∈ ({(1,0),(0,1)} : Finset Period),
      ∃ a path, k.IsEdgeWalk a path ∧ walkEnd a path = a ∧ walkPeriod K a path = u) :
    (periodDet (cyclePeriod K k.basisCycles.1,cyclePeriod K k.basisCycles.2)).natAbs = 1 := by
  let M : PeriodMatrix := (cyclePeriod K k.basisCycles.1,cyclePeriod K k.basisCycles.2)
  let p := k.treePotential K
  let K' := gaugeCochain K p
  have hK' : k.IsCocycle K' := gaugeCochain_valid hK p
  have ht : k.IsTreeNormalized K' := gaugeCochain_normalized hK
  have hs (u : Period) (hu : u ∈ ({(1,0),(0,1)} : Finset Period)) : ∃ v, mapPeriod M v = u := by
    obtain ⟨a,path,hp,hend,hpath⟩ := hgen u hu
    have hh := walkPeriod_eq_mapPeriod hK' ht hp
    change walkPeriod (gaugeCochain K p) a path = mapPeriod
      (cyclePeriod (gaugeCochain K p) k.basisCycles.1,cyclePeriod (gaugeCochain K p) k.basisCycles.2) _ at hh
    simp only [walkPeriod_gauge,cyclePeriod_gauge,hend,add_sub_cancel_right,hpath] at hh
    exact ⟨_,hh.symm⟩
  obtain ⟨u,hu⟩ := hs (1,0) (by simp)
  obtain ⟨v,hv⟩ := hs (0,1) (by simp)
  have he : mulPeriodMatrix (u,v) M = periodIdentity := Prod.ext hu hv
  have hd : periodDet (u,v)*periodDet M = 1 := by
    rw [← periodDet_mul,he]
    decide +kernel
  have habs := congrArg Int.natAbs hd
  rw [Int.natAbs_mul] at habs
  change (periodDet (u,v)).natAbs*(periodDet M).natAbs = 1 at habs
  change (periodDet M).natAbs = 1
  exact Nat.dvd_one.mp ⟨(periodDet (u,v)).natAbs,by simpa only [mul_comm] using habs.symm⟩

/-- Coherent marked faces of a bijective quotient development determine
a unimodular marking without a separate hypothesis on primitive walks. -/
theorem marking_unimodular_of_quotient {k : Triangulation} {K : EdgeCochain} (hK : k.IsCocycle K)
    {ι : Type*} [Finite ι] {lift : ι → LiftedFace} (S : PeriodicFaceSystem k.faces lift)
    (x w : ℝ) (q : Vertex → ℝ × ℝ) (F : triangleWeightSpace k.faces → MarkedTorus)
    (hf : Function.Bijective F)
    (hF : ∀ j u, u.val ∈ faceWeights (triangleVertexSet (liftedVertices (lift j))) →
      F u = projectPeriods (facePeriodPoint x w q (lift j) u.val))
    (hLift : ∀ j a b, a ∈ triangleVertexSet (liftedVertices (lift j)) →
      b ∈ triangleVertexSet (liftedVertices (lift j)) → a ≠ b →
      K a b = facePeriod (lift j) b-facePeriod (lift j) a)
    (j : ι) : (periodDet (cyclePeriod K k.basisCycles.1,cyclePeriod K k.basisCycles.2)).natAbs = 1 :=
  marking_unimodular_of_generating_walks hK fun d _ =>
    generating_walks_of_quotient S x w q F hf hF hLift j d

end Triangulation
end OrigamiTorus.Winding
