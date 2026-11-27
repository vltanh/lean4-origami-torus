module

public import OrigamiTorus.Type5Reconstruction
public import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Topology.Connected.Clopen
import Mathlib.Tactic

/-! Every direction lies in a finite cyclic fan of positively oriented wedges. -/

public section

open Set
open scoped Topology

namespace OrigamiTorus

open Type5 (Plane cross)

private theorem cross_continuous_left (u : Plane ℝ) : Continuous (fun p => cross p u) := by
  unfold cross
  fun_prop

private theorem cross_continuous_right (u : Plane ℝ) : Continuous (cross u) := by
  unfold cross
  fun_prop

private theorem cross_swap (u v : Plane ℝ) : cross u v = -cross v u := by
  simp only [cross]
  ring

/-- Cramer's rule for the coordinates in a planar basis. -/
theorem coordinates_in_wedge (u v p : Plane ℝ) (h : cross u v ≠ 0) :
    p = (cross p v / cross u v) • u + (cross u p / cross u v) • v := by
  have hc (a : ℝ) (q : Plane ℝ) : a • q = (a*q.1,a*q.2) := rfl
  apply Prod.ext <;> simp only [hc, Prod.fst_add, Prod.snd_add] <;> field_simp [h] <;>
    unfold cross <;> ring

/-- A cyclic list of positively oriented wedges covers the whole plane. The
successor permutation supplies the two adjacent sectors along each ray. -/
theorem positiveFan_covers {ι : Type*} [Finite ι] [Nonempty ι]
    (next : Equiv.Perm ι) (edge : ι → Plane ℝ)
    (h : ∀ i, 0 < cross (edge i) (edge (next i))) (p : Plane ℝ) :
    ∃ i, 0 ≤ cross (edge i) p ∧ 0 ≤ cross p (edge (next i)) := by
  classical
  let wedge (i : ι) : Set (Plane ℝ) := {q | 0 ≤ cross (edge i) q ∧ 0 ≤ cross q (edge (next i))}
  let S := ⋃ i, wedge i
  let P := ({0}ᶜ : Set (Plane ℝ))
  let T : Set P := Subtype.val ⁻¹' S
  have hclosed : IsClosed T := by
    apply IsClosed.preimage continuous_subtype_val
    apply isClosed_iUnion_of_finite
    intro i
    exact (isClosed_le continuous_const (cross_continuous_right (edge i))).inter
      (isClosed_le continuous_const (cross_continuous_left (edge (next i))))
  have ray (i : ι) (t : ℝ) (ht : 0 < t) (q : P) (hq : q.val = t • edge i) :
      T ∈ 𝓝 q := by
    let j := next.symm i
    have hj : next j = i := next.apply_symm_apply i
    have hL : 0 < cross (edge j) q.val := by
      have h' := h j
      rw [hj] at h'
      rw [hq]
      have he (a b : Plane ℝ) : cross a (t • b) = t * cross a b := by
        change a.1*(t*b.2)-a.2*(t*b.1) = _
        unfold cross
        ring
      rw [he]
      exact mul_pos ht h'
    have hR : 0 < cross q.val (edge (next i)) := by
      rw [hq]
      have he (a b : Plane ℝ) : cross (t • a) b = t * cross a b := by
        change (t*a.1)*b.2-(t*a.2)*b.1 = _
        unfold cross
        ring
      rw [he]
      exact mul_pos ht (h i)
    have hOL := (isOpen_lt continuous_const ((cross_continuous_right (edge j)).comp
      continuous_subtype_val)).mem_nhds hL
    have hOR := (isOpen_lt continuous_const ((cross_continuous_left (edge (next i))).comp
      continuous_subtype_val)).mem_nhds hR
    refine Filter.mem_of_superset (Filter.inter_mem hOL hOR) ?_
    rintro a ⟨haL,haR⟩
    change a.val ∈ S
    apply mem_iUnion.mpr
    by_cases hA : 0 ≤ cross (edge i) a.val
    · exact ⟨i,hA,haR.le⟩
    · refine ⟨j,haL.le,?_⟩
      rw [hj, cross_swap]
      exact neg_nonneg.mpr (lt_of_not_ge hA).le
  have hopen : IsOpen T := by
    rw [isOpen_iff_mem_nhds]
    intro q hq
    obtain ⟨i,h₁,h₂⟩ := mem_iUnion.mp (show q.val ∈ S from hq)
    by_cases hA : cross (edge i) q.val = 0
    · have hpos : 0 < cross q.val (edge (next i)) := by
        by_contra! hn
        have he := le_antisymm hn h₂
        have hz := coordinates_in_wedge (edge i) (edge (next i)) q.val (h i).ne'
        simp [hA, he] at hz
        exact q.property hz
      apply ray i (cross q.val (edge (next i)) / cross (edge i) (edge (next i))) (div_pos hpos (h i))
      simpa [hA] using coordinates_in_wedge (edge i) (edge (next i)) q.val (h i).ne'
    · by_cases hB : cross q.val (edge (next i)) = 0
      · have hpos : 0 < cross (edge i) q.val := lt_of_le_of_ne h₁ (Ne.symm hA)
        apply ray (next i) (cross (edge i) q.val / cross (edge i) (edge (next i))) (div_pos hpos (h i))
        simpa [hB] using coordinates_in_wedge (edge i) (edge (next i)) q.val (h i).ne'
      · have hOL := (isOpen_lt continuous_const ((cross_continuous_right (edge i)).comp
          continuous_subtype_val)).mem_nhds (lt_of_le_of_ne h₁ (Ne.symm hA))
        have hOR := (isOpen_lt continuous_const ((cross_continuous_left (edge (next i))).comp
          continuous_subtype_val)).mem_nhds (lt_of_le_of_ne h₂ (Ne.symm hB))
        exact Filter.mem_of_superset (Filter.inter_mem hOL hOR)
          (fun a ⟨ha,hb⟩ => mem_iUnion.mpr ⟨i,ha.le,hb.le⟩)
  have hr : 1 < Module.rank ℝ (Plane ℝ) := by
    rw [← Module.finrank_eq_rank]
    norm_num [Plane, Module.finrank_prod]
  let _ : PreconnectedSpace P := Subtype.preconnectedSpace
    (isPathConnected_compl_singleton_of_one_lt_rank hr 0).isConnected.isPreconnected
  let i : ι := Classical.arbitrary _
  have hi : edge i ≠ 0 := by
    intro hz
    have he := h i
    simp [hz,cross] at he
  have hne : T.Nonempty := ⟨⟨edge i,hi⟩, mem_iUnion.mpr ⟨i,by simp [cross,mul_comm],(h i).le⟩⟩
  have hT : T = univ := IsClopen.eq_univ ⟨hclosed,hopen⟩ hne
  by_cases hp : p = 0
  · exact ⟨i,by simp [hp,cross],by simp [hp,cross]⟩
  · have he : (⟨p,hp⟩ : P) ∈ T := hT.symm ▸ mem_univ _
    exact mem_iUnion.mp (show p ∈ S from he)

/-- Every uniformly truncated positive fan contains a neighborhood of its center. -/
theorem positiveFan_truncated_mem_nhds {ι : Type*} [Finite ι] [Nonempty ι]
    (next : Equiv.Perm ι) (edge : ι → Plane ℝ)
    (h : ∀ i, 0 < cross (edge i) (edge (next i))) {ε : ℝ} (hε : 0 < ε) :
    {p | ∃ (i : ι) (a b : ℝ), 0 ≤ a ∧ 0 ≤ b ∧ a+b < ε ∧
      p = a • edge i + b • edge (next i)} ∈ 𝓝 (0 : Plane ℝ) := by
  let A (i : ι) (p : Plane ℝ) := cross p (edge (next i)) / cross (edge i) (edge (next i))
  let B (i : ι) (p : Plane ℝ) := cross (edge i) p / cross (edge i) (edge (next i))
  let W := ⋂ i, {p | A i p + B i p < ε}
  have hopen : IsOpen W := isOpen_iInter_of_finite fun i => isOpen_lt
    (((cross_continuous_left (edge (next i))).div_const _).add
      ((cross_continuous_right (edge i)).div_const _)) continuous_const
  have hzero : (0 : Plane ℝ) ∈ W := mem_iInter.mpr fun i => by simpa [A,B,cross] using hε
  refine Filter.mem_of_superset (hopen.mem_nhds hzero) (fun p hp => ?_)
  obtain ⟨i,ha,hb⟩ := positiveFan_covers next edge h p
  exact ⟨i,A i p,B i p,div_nonneg hb (h i).le,div_nonneg ha (h i).le,mem_iInter.mp hp i,
    coordinates_in_wedge (edge i) (edge (next i)) p (h i).ne'⟩

end OrigamiTorus
