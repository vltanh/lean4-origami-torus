module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Permutation
import Mathlib.Data.List.Sublists
import Mathlib.Tactic

/-! The seven-vertex triangulation of the torus is unique up to relabeling. -/

@[expose] public section

namespace OrigamiTorus.SevenVertex

abbrev Label := Fin 7
abbrev Faces := Finset (Finset Label)

/-- The number of faces containing the edge `e`. -/
def incidence (fs : Faces) (e : Finset Label) : ℕ :=
  (fs.filter (e ⊆ ·)).card

/-- Combinatorial conditions satisfied by a simplicial triangulation of the
torus on seven vertices. Each triangle is recorded by its set of labels.
The face count comes from Euler characteristic zero and two faces per edge. -/
def IsTorusTriangulation (fs : Faces) : Prop :=
  (∀ f ∈ fs, f.card = 3) ∧ fs.card = 14 ∧
    ∀ e : Finset Label, e.card = 2 → incidence fs e = 0 ∨ incidence fs e = 2

/-- The Möbius triangulation, with the collapsed Type 1 labels shifted down by one. -/
def moebius : Faces :=
  {{0,1,2}, {0,3,1}, {0,2,4}, {0,5,3}, {0,4,6}, {0,6,5}, {1,5,2},
   {1,3,6}, {1,4,5}, {1,6,4}, {2,3,4}, {2,6,3}, {2,5,6}, {3,5,4}}

end OrigamiTorus.SevenVertex

section

namespace OrigamiTorus.SevenVertex

open Finset

private def allEdges : Faces := (univ : Finset Label).powersetCard 2

private def allTriangles : Faces := (univ : Finset Label).powersetCard 3

private theorem incidence_sum (fs : Faces) (h : ∀ f ∈ fs, f.card = 3) :
    ∑ e ∈ allEdges, incidence fs e = 3 * fs.card := by
  have count (f : Finset Label) (hf : f ∈ fs) :
      (allEdges.filter (· ⊆ f)).card = 3 := by
    have hset : allEdges.filter (· ⊆ f) = f.powersetCard 2 := by
      ext e
      simp [allEdges, and_comm]
    rw [hset, card_powersetCard, h f hf]
    decide
  calc
    _ = ∑ e ∈ allEdges, ∑ f ∈ fs, if e ⊆ f then 1 else 0 :=
      sum_congr rfl (fun e _ => by rw [incidence, card_eq_sum_ones, sum_filter])
    _ = ∑ f ∈ fs, (allEdges.filter (· ⊆ f)).card := by
      rw [sum_comm]
      exact sum_congr rfl (fun f _ => by rw [card_eq_sum_ones, sum_filter])
    _ = 3 * fs.card := by
      rw [sum_congr rfl count]
      simp [Nat.mul_comm]

/-- Euler characteristic zero and the closed-surface edge condition imply
the fourteen-face condition used by the classification. -/
public theorem isTorusTriangulation_of_euler {fs : Faces}
    (hfaces : ∀ f ∈ fs, f.card = 3)
    (hclosed : ∀ e : Finset Label, e.card = 2 → incidence fs e = 0 ∨ incidence fs e = 2)
    (hEuler : 7 + fs.card = (((univ : Finset Label).powersetCard 2).filter
      fun e => 0 < incidence fs e).card) :
    IsTorusTriangulation fs := by
  let edges := allEdges.filter fun e => 0 < incidence fs e
  have hsum : ∑ e ∈ allEdges, incidence fs e = 2 * edges.card := by
    calc
      _ = ∑ e ∈ allEdges, if 0 < incidence fs e then 2 else 0 := by
        apply sum_congr rfl
        intro e he
        rcases hclosed e (mem_powersetCard.mp he).2 with h | h <;> simp [h]
      _ = ∑ _e ∈ edges, 2 := (sum_filter ..).symm
      _ = 2 * edges.card := by simp [Nat.mul_comm]
  change 7 + fs.card = edges.card at hEuler
  have hcount := incidence_sum fs hfaces
  exact ⟨hfaces, by omega, hclosed⟩

/-- In a seven-vertex torus triangulation all 21 edges occur twice. -/
public theorem complete_incidence {fs : Faces} (h : IsTorusTriangulation fs)
    {e : Finset Label} (he : e.card = 2) : incidence fs e = 2 := by
  have hmem : e ∈ allEdges := by simp [allEdges, he]
  have hbound (d) (hd : d ∈ allEdges) : incidence fs d ≤ 2 := by
    have hcard : d.card = 2 := (mem_powersetCard.mp hd).2
    rcases h.2.2 d hcard with hd | hd <;> simp [hd]
  by_contra hn
  have hz := (h.2.2 e he).resolve_right hn
  have hsum := incidence_sum fs h.1
  rw [h.2.1, ← sum_erase_add _ _ hmem, hz, add_zero] at hsum
  have hb := sum_le_sum (s := allEdges.erase e)
    (fun d hd => hbound d (mem_of_mem_erase hd))
  have hcard : allEdges.card = 21 := by decide +kernel
  rw [sum_const, smul_eq_mul, card_erase_of_mem hmem, hcard, hsum] at hb
  omega

private def triangleList : List (Finset Label) :=
  (List.finRange 7).flatMap fun a =>
    (List.finRange 7).flatMap fun b =>
      ((List.finRange 7).filter fun c => a < b && b < c).map fun c => {a,b,c}

private theorem triangleList_nodup : triangleList.Nodup := by decide +kernel

private theorem triangleList_toFinset : triangleList.toFinset = allTriangles := by decide +kernel

private theorem triangleList_length : triangleList.length = 35 := by decide +kernel

private def triangleAt (i : Fin 35) : Finset Label :=
  triangleList[i.val]'(by exact i.isLt)

private theorem triangleAt_surj (f : Finset Label) (hf : f ∈ allTriangles) :
    ∃ i, triangleAt i = f := by
  have hmem : f ∈ triangleList := by simpa [← triangleList_toFinset] using hf
  obtain ⟨i, hi, hh⟩ := List.getElem_of_mem hmem
  exact ⟨⟨i, hi⟩, hh⟩

private def edgeList : List (Finset Label) :=
  (List.finRange 7).flatMap fun a => ((List.finRange 7).filter (a < ·)).map fun b => {a,b}

private theorem edgeList_toFinset : edgeList.toFinset = allEdges := by decide +kernel

private abbrev Mask := BitVec 35

private def encode (fs : Faces) : Mask :=
  (BitVec.ofBoolListLE (triangleList.map fun f => decide (f ∈ fs))).cast (by simp [triangleList_length])

private theorem encode_bit (fs : Faces) (i : Nat) :
    (encode fs).getLsbD i = if hi : i < 35 then decide (triangleAt ⟨i,hi⟩ ∈ fs) else false := by
  unfold encode
  simp only [BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE]
  split_ifs with hi
  · rw [List.getD_eq_getElem _ _ (by simpa [triangleList_length] using hi), List.getElem_map]
    rfl
  · exact List.getD_eq_default _ _ (by simpa [triangleList_length] using Nat.le_of_not_gt hi)

private theorem encode_inj {fs gs : Faces} (hfs : fs ⊆ allTriangles) (hgs : gs ⊆ allTriangles)
    (h : encode fs = encode gs) : fs = gs := by
  ext f
  by_cases hf : f ∈ allTriangles
  · obtain ⟨i, rfl⟩ := triangleAt_surj f hf
    have hb := congrArg (fun m : Mask => m.getLsbD i.val) h
    simpa only [encode_bit, dite_eq_left i.isLt, decide_eq_decide] using hb
  · exact iff_of_false (fun hf' => hf (hfs hf')) (fun hf' => hf (hgs hf'))

private theorem encode_empty : encode ∅ = 0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [encode_bit, dite_eq_left hi]
  simp

private theorem encode_union (fs gs : Faces) : encode (fs ∪ gs) = encode fs ||| encode gs := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_or, encode_bit, encode_bit, encode_bit]
  simp [hi]

private theorem encode_disjoint {fs gs : Faces} (h : Disjoint fs gs) : encode fs &&& encode gs = 0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_and, encode_bit, dite_eq_left hi]
  rw [show (0 : Mask).getLsbD i = false from BitVec.getLsbD_zero]
  by_cases hf : triangleAt ⟨i,hi⟩ ∈ fs
  · simp [hf, disjoint_left.mp h hf]
  · simp [hf]

/-- At an edge, choose its two incident triangles and forbid the other three. -/
private def choices (e : Finset Label) : List (Mask × Mask) :=
  let incident := triangleList.filter fun f => e ⊆ f
  (incident.sublistsLen 2).map fun selected =>
    (encode selected.toFinset, encode (incident.toFinset \ selected.toFinset))

/-- Track required and forbidden triangles. Choices with conflicting assignments
are discarded before descending to the next edge. -/
private def search : List (List (Mask × Mask)) → Mask → Mask → List Mask
  | [], yes, _ => [yes]
  | opts :: rest, yes, no => opts.flatMap fun (selected, rejected) =>
      if selected &&& no = 0 ∧ rejected &&& yes = 0 then
        search rest (yes ||| selected) (no ||| rejected)
      else []

private theorem search_complete (fs : Faces) (hfs : fs ⊆ allTriangles) (es : List (Finset Label))
    (hcount : ∀ e ∈ es, incidence fs e = 2) (yes no : Faces)
    (hyes : yes ⊆ fs) (hno : Disjoint fs no)
    (hcover : ∀ f ∈ fs, f ∈ yes ∨ ∃ e ∈ es, e ⊆ f) :
    encode fs ∈ search (es.map choices) (encode yes) (encode no) := by
  induction es generalizing yes no with
  | nil =>
    have he : fs = yes :=
      Subset.antisymm (fun f hf => (hcover f hf).resolve_right (by simp)) hyes
    simp [search, he]
  | cons e rest ih =>
    let incident := triangleList.filter fun f => e ⊆ f
    let selected := incident.filter (· ∈ fs)
    let rejected := incident.toFinset \ selected.toFinset
    have hselected : selected.toFinset = fs.filter (e ⊆ ·) := by
      ext f
      simp only [selected, incident, List.mem_toFinset, List.mem_filter, mem_filter,
        decide_eq_true_eq]
      rw [← List.mem_toFinset, triangleList_toFinset]
      exact ⟨fun ⟨⟨_,he⟩,hf⟩ => ⟨hf,he⟩, fun ⟨hf,he⟩ => ⟨⟨hfs hf,he⟩,hf⟩⟩
    have hsub : selected.toFinset ⊆ fs := by rw [hselected]; exact filter_subset _ _
    have hr : Disjoint fs rejected := by
      rw [disjoint_left]
      intro f hf hfr
      obtain ⟨hi, hn⟩ := mem_sdiff.mp hfr
      apply hn
      rw [hselected]
      exact mem_filter.mpr ⟨hf, of_decide_eq_true (List.mem_filter.mp (List.mem_toFinset.mp hi)).2⟩
    have hlen : selected.length = 2 := by
      rw [← List.toFinset_card_of_nodup ((triangleList_nodup.filter _).filter _),
        hselected]
      exact hcount e (by simp)
    have hchoice : (encode selected.toFinset, encode rejected) ∈ choices e :=
      List.mem_map.mpr ⟨selected, List.mem_sublistsLen.mpr ⟨List.filter_sublist, hlen⟩, rfl⟩
    simp only [List.map_cons, search, List.mem_flatMap]
    refine ⟨_, hchoice, ?_⟩
    rw [ite_eq_left ⟨encode_disjoint (hno.mono_left hsub), encode_disjoint (hr.symm.mono_right hyes)⟩,
      ← encode_union, ← encode_union]
    apply ih (fun d hd => hcount d (List.mem_cons_of_mem _ hd)) _ _
      (union_subset hyes hsub) (disjoint_union_right.mpr ⟨hno,hr⟩)
    intro f hf
    rcases hcover f hf with hy | ⟨d, hd, hdf⟩
    · exact Or.inl (mem_union_left _ hy)
    rcases List.mem_cons.mp hd with rfl | hd
    · exact Or.inl (mem_union_right _ (hselected ▸ mem_filter.mpr ⟨hf,hdf⟩))
    · exact Or.inr ⟨d,hd,hdf⟩

private def relabel (p : Label → Label) (fs : Faces) : Faces :=
  fs.image (fun f => f.image p)

private def permutations : List (List Label) :=
  ((List.finRange 5).map fun i => i.succ.succ).permutations'.map (0 :: 1 :: ·)

private def orbit : List Mask :=
  permutations.map fun p => encode (relabel (fun i => p[i.val]!) moebius)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem search_in_orbit :
    (search (edgeList.map choices) 0 0).all (fun m => orbit.contains m) = true := by
  decide +kernel

private theorem relabel_subset (p : Label → Label) (hp : Function.Injective p) :
    relabel p moebius ⊆ allTriangles := by
  intro f hf
  obtain ⟨g,hg,rfl⟩ := mem_image.mp hf
  have hm : ∀ g ∈ moebius, g.card = 3 := by decide +kernel
  simp [allTriangles, card_image_of_injective _ hp, hm g hg]

/-- Every simplicial seven-vertex torus triangulation is a relabeling of the
Möbius triangulation. The search uses only the triangular face and edge
incidence conditions, so link connectivity and orientability need not be
separate hypotheses. -/
public theorem exists_relabel_moebius {fs : Faces} (hf : IsTorusTriangulation fs) :
    ∃ e : Equiv.Perm Label, fs = moebius.image (fun f => f.image e) := by
  have hsub : fs ⊆ allTriangles := fun f hf' => by simp [allTriangles, hf.1 f hf']
  have hsearch := search_complete fs hsub edgeList
    (fun e he => complete_incidence hf (mem_powersetCard.mp
      (edgeList_toFinset ▸ List.mem_toFinset.mpr he)).2)
    ∅ ∅ (empty_subset _) (disjoint_empty_right _)
    (fun f hf' => Or.inr (by
      have hle : 2 ≤ f.card := by rw [hf.1 f hf']; decide
      obtain ⟨e, hef, he⟩ := exists_subset_card_eq hle
      exact ⟨e, List.mem_toFinset.mp (edgeList_toFinset.symm ▸
        (by simp [allEdges, he] : e ∈ allEdges)), hef⟩))
  rw [encode_empty] at hsearch
  have horbit := List.contains_iff_mem.mp (List.all_eq_true.mp search_in_orbit _ hsearch)
  obtain ⟨p, hp, hm⟩ := List.mem_map.mp horbit
  obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hp
  have hperm := List.mem_permutations'.mp hl
  have hlen : (0 :: 1 :: l).length = 7 := by simp [hperm.length_eq]
  have hnd : (0 :: 1 :: l).Nodup := by
    refine (List.Perm.cons 0 (List.Perm.cons 1 hperm)).nodup_iff.mpr ?_
    decide +kernel
  let funOfList (i : Label) := (0 :: 1 :: l)[i.val]!
  have hinj : Function.Injective funOfList := by
    intro i j hij
    apply Fin.ext
    exact (List.Nodup.getElem!_inj (by simpa only [hlen] using i.isLt)
      (by simpa only [hlen] using j.isLt) hnd).mp hij
  let σ := Equiv.ofBijective funOfList (Finite.injective_iff_bijective.mp hinj)
  exact ⟨σ, encode_inj hsub (relabel_subset _ hinj) hm.symm⟩

end OrigamiTorus.SevenVertex

end
