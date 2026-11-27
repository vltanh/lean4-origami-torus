module

public import OrigamiTorus.WindingCocycle
public import OrigamiTorus.ShortestWinding
import Mathlib.Tactic

/-! Finite candidate windings from the three-edge cycles. -/

@[expose] public section

namespace OrigamiTorus.Winding

def periodDet (M : PeriodMatrix) : ℤ := M.1.1*M.2.2-M.1.2*M.2.1

theorem mapPeriod_fst (M : PeriodMatrix) (u : Period) :
    (mapPeriod M u).1 = u.1*M.1.1+u.2*M.2.1 := by
  simp only [mapPeriod,Prod.fst_add,zsmul_eq_mul,Prod.fst_mul,Prod.fst_intCast,Int.cast_id]

theorem mapPeriod_snd (M : PeriodMatrix) (u : Period) :
    (mapPeriod M u).2 = u.1*M.1.2+u.2*M.2.2 := by
  simp only [mapPeriod,Prod.snd_add,zsmul_eq_mul,Prod.snd_mul,Prod.snd_intCast,Int.cast_id]

theorem mapPeriod_injective {M : PeriodMatrix} (hM : periodDet M ≠ 0) :
    Function.Injective (mapPeriod M) := by
  intro u v huv
  have h₁ := congrArg Prod.fst huv
  have h₂ := congrArg Prod.snd huv
  simp only [mapPeriod_fst,mapPeriod_snd] at h₁ h₂
  have hu : (u.1-v.1)*periodDet M = 0 := by
    unfold periodDet
    linear_combination (norm := ring) M.2.2*h₁-M.2.1*h₂
  have hv : (u.2-v.2)*periodDet M = 0 := by
    unfold periodDet
    linear_combination (norm := ring) M.1.1*h₂-M.1.2*h₁
  exact Prod.ext (sub_eq_zero.mp ((mul_eq_zero.mp hu).resolve_right hM))
    (sub_eq_zero.mp ((mul_eq_zero.mp hv).resolve_right hM))

namespace Triangulation

def threeCycles (k : Triangulation) : List Triangle :=
  (List.finRange 8).flatMap fun a =>
    (List.finRange 8).flatMap fun b =>
      ((List.finRange 8).map fun c => (a,b,c)).filter fun f =>
        decide (f.1 < f.2.1 ∧ f.2.1 < f.2.2) && (faceEdges f).all k.edges.contains

theorem edges_of_threeCycle {k : Triangulation} {f : Triangle} (hf : f ∈ k.threeCycles) :
    ∀ e ∈ faceEdges f, e ∈ k.edges := by
  obtain ⟨_,_,hm⟩ := List.mem_flatMap.mp hf
  obtain ⟨_,_,hm⟩ := List.mem_flatMap.mp hm
  have h := (List.mem_filter.mp hm).2
  rw [Bool.and_eq_true] at h
  intro e he
  exact List.contains_iff_mem.mp (List.all_eq_true.mp h.2 e he)

theorem basis_threeCycles (k : Triangulation) :
    k.basisCycles.1 ∈ k.threeCycles ∧ k.basisCycles.2 ∈ k.threeCycles := by
  cases k <;> decide +kernel

def nonzeroClasses (k : Triangulation) : Finset Period :=
  ((k.threeCycles.map (cyclePeriod k.dualCocycle)).toFinset).erase 0

theorem mem_nonzeroClasses (k : Triangulation) (u : Period) :
    u ∈ k.nonzeroClasses ↔ u ≠ 0 ∧ ∃ f ∈ k.threeCycles, cyclePeriod k.dualCocycle f = u := by
  simp [nonzeroClasses,List.mem_map]

/-- Unimodular matrices satisfying every nonzero triangular period bound. -/
def candidates (k : Triangulation) (sharp : Bool) : Finset PeriodMatrix :=
  ((allowed sharp).product (allowed sharp)).filter fun M =>
    (periodDet M).natAbs = 1 ∧ ∀ u ∈ k.nonzeroClasses, mapPeriod M u ∈ allowed sharp

theorem candidate_count (k : Triangulation) (sharp : Bool) : (k.candidates sharp).card =
    match k, sharp with
    | .type4, false | .type5, false | .type7, true => 24
    | .type4, true | .type5, true => 12
    | .type7, false => 40 := by
  cases k <;> cases sharp <;> decide +kernel

theorem cycle_eq_mapPeriod_of_edges {k : Triangulation} {K : EdgeCochain} (hK : k.IsCocycle K)
    (ht : k.IsTreeNormalized K) {f : Triangle} (hf : ∀ e ∈ faceEdges f, e ∈ k.edges) :
    cyclePeriod K f = mapPeriod (cyclePeriod K k.basisCycles.1,cyclePeriod K k.basisCycles.2)
      (cyclePeriod k.dualCocycle f) := by
  rw [← cyclePeriod_mapPeriod]
  rcases f with ⟨a,b,c⟩
  have hab := cocycle_eq_mapPeriod hK ht (hf (orderedEdge a b) (by simp [faceEdges]))
  have hbc := cocycle_eq_mapPeriod hK ht (hf (orderedEdge b c) (by simp [faceEdges]))
  have hca := cocycle_eq_mapPeriod hK ht (hf (orderedEdge c a) (by simp [faceEdges]))
  simp only [cyclePeriod,hab,hbc,hca]

theorem cycle_eq_mapPeriod {k : Triangulation} {K : EdgeCochain} (hK : k.IsCocycle K)
    (ht : k.IsTreeNormalized K) {f : Triangle} (hf : f ∈ k.threeCycles) :
    cyclePeriod K f = mapPeriod (cyclePeriod K k.basisCycles.1,cyclePeriod K k.basisCycles.2)
      (cyclePeriod k.dualCocycle f) :=
  cycle_eq_mapPeriod_of_edges hK ht (edges_of_threeCycle hf)

theorem marking_mem_candidates {k : Triangulation} {K : EdgeCochain} (hK : k.IsCocycle K)
    (ht : k.IsTreeNormalized K) {sharp : Bool}
    (hw : ∀ f ∈ k.threeCycles, cyclePeriod K f ≠ 0 → cyclePeriod K f ∈ allowed sharp)
    (hdet : (periodDet (cyclePeriod K k.basisCycles.1,cyclePeriod K k.basisCycles.2)).natAbs = 1) :
    (cyclePeriod K k.basisCycles.1,cyclePeriod K k.basisCycles.2) ∈ k.candidates sharp := by
  let M : PeriodMatrix := (cyclePeriod K k.basisCycles.1,cyclePeriod K k.basisCycles.2)
  have hd : periodDet M ≠ 0 := by
    intro hz
    change (periodDet M).natAbs = 1 at hdet
    simp [hz] at hdet
  have hl : M.1 ≠ 0 := by
    intro hz
    exact hd (by simp [periodDet,hz])
  have hr : M.2 ≠ 0 := by
    intro hz
    exact hd (by simp [periodDet,hz])
  change M ∈ k.candidates sharp
  refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
    ⟨hw _ (basis_threeCycles k).1 hl,hw _ (basis_threeCycles k).2 hr⟩,hdet,?_⟩
  intro u hu
  obtain ⟨hne,f,hf,rfl⟩ := (mem_nonzeroClasses k u).mp hu
  have hc : cyclePeriod K f = mapPeriod M (cyclePeriod k.dualCocycle f) := cycle_eq_mapPeriod hK ht hf
  rw [← hc]
  exact hw f hf fun hz => hne (mapPeriod_injective hd (hc.symm.trans (hz.trans (mapPeriod_zero M).symm)))

/-- The displacement in coordinates of the chosen ordered lattice basis. -/
def edgeDisplacement (P : Vertex → ℝ × ℝ) (K : EdgeCochain) (a b : Vertex) : ℝ × ℝ :=
  P b-P a+realPeriod (K a b)

private theorem sum_edgeDisplacements (P : Vertex → ℝ × ℝ) (K : EdgeCochain) (a b c : Vertex) :
    edgeDisplacement P K a b+edgeDisplacement P K b c+edgeDisplacement P K c a =
      realPeriod (cyclePeriod K (a,b,c)) := by
  apply Prod.ext
  · simp only [edgeDisplacement,cyclePeriod,realPeriod,Prod.fst_add,Prod.fst_sub,Int.cast_add]
    ring
  · simp only [edgeDisplacement,cyclePeriod,realPeriod,Prod.snd_add,Prod.snd_sub,Int.cast_add]
    ring

/-- A unimodular marking of an intrinsic realization with strictly shortest
edges is among the finite candidates. The edge cochain may use any gauge. -/
theorem marking_mem_candidates_of_shortest_edges {k : Triangulation} {K : EdgeCochain}
    (hK : k.IsCocycle K) {x y : ℝ} (hx : 0 ≤ x) (hx' : x ≤ 1/2) (hr : 1 ≤ x^2+y^2)
    (P : Vertex → ℝ × ℝ)
    (hshort : ∀ a b, orderedEdge a b ∈ k.edges →
      let d := edgeDisplacement P K a b
      StrictShortest x y (d.1+x*d.2) d.2)
    (hdet : (periodDet (cyclePeriod K k.basisCycles.1,cyclePeriod K k.basisCycles.2)).natAbs = 1) :
    (cyclePeriod K k.basisCycles.1,cyclePeriod K k.basisCycles.2) ∈
      k.candidates (decide (x = 1/2)) := by
  have hw : ∀ f ∈ k.threeCycles, cyclePeriod K f ≠ 0 →
      cyclePeriod K f ∈ allowed (decide (x = 1/2)) := by
    rintro ⟨a,b,c⟩ hf hne
    let d₁ := edgeDisplacement P K a b
    let d₂ := edgeDisplacement P K b c
    let d₃ := edgeDisplacement P K c a
    let u := cyclePeriod K (a,b,c)
    have hab := hshort a b (edges_of_threeCycle hf _ (by simp [faceEdges]))
    have hbc := hshort b c (edges_of_threeCycle hf _ (by simp [faceEdges]))
    have hca := hshort c a (edges_of_threeCycle hf _ (by simp [faceEdges]))
    have hsum := sum_edgeDisplacements P K a b c
    have h₁ := congrArg Prod.fst hsum
    have h₂ := congrArg Prod.snd hsum
    change d₁.1+d₂.1+d₃.1 = (u.1 : ℝ) at h₁
    change d₁.2+d₂.2+d₃.2 = (u.2 : ℝ) at h₂
    have hX : (d₁.1+x*d₁.2)+(d₂.1+x*d₂.2)+(d₃.1+x*d₃.2) = (u.1 : ℝ)+(u.2 : ℝ)*x := by
      linear_combination (norm := ring) h₁+x*h₂
    exact triangle_mem_allowed hx hx' hr hab hbc hca hne hX h₂
  let K' := gaugeCochain K (k.treePotential K)
  have hw' : ∀ f ∈ k.threeCycles, cyclePeriod K' f ≠ 0 →
      cyclePeriod K' f ∈ allowed (decide (x = 1/2)) := by
    intro f hf
    simpa only [K',cyclePeriod_gauge] using hw f hf
  have hdet' : (periodDet (cyclePeriod K' k.basisCycles.1,cyclePeriod K' k.basisCycles.2)).natAbs = 1 := by
    simpa only [K',cyclePeriod_gauge] using hdet
  simpa only [K',cyclePeriod_gauge] using
    marking_mem_candidates (gaugeCochain_valid hK _) (gaugeCochain_normalized hK) hw' hdet'

end Triangulation
end OrigamiTorus.Winding
