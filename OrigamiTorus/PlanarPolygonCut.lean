module

public import OrigamiTorus.PlanarCut
public import OrigamiTorus.SphericalPerimeter
public import Mathlib.Data.List.Rotate
import Mathlib.Tactic

/-! The polygon boundary and angular perimeter after selecting the retained arc. -/

public section

open Set
open scoped NNReal

namespace OrigamiTorus

/-- The segments of a polygonal path, including the edges to its two endpoints. -/
@[expose] def segmentPath (a : Point3) (xs : List Point3) (b : Point3) : Set Point3 :=
  match xs with
  | [] => segment ℝ a b
  | x :: xs => segment ℝ a x ∪ segmentPath x xs b

/-- The union of the segments in a closed polygonal boundary list. -/
@[expose] def segmentCycle (xs : List Point3) : Set Point3 :=
  match xs with
  | [] => ∅
  | a :: ys => segmentPath a ys a

theorem segmentPath_append (a b c : Point3) (xs ys : List Point3) :
    segmentPath a (xs ++ b :: ys) c = segmentPath a xs b ∪ segmentPath b ys c := by
  induction xs generalizing a with
  | nil => rfl
  | cons x xs ih => simp [segmentPath,ih,union_assoc]

private theorem segmentPath_endpoints (a : Point3) (xs : List Point3) (b : Point3) :
    a ∈ segmentPath a xs b ∧ b ∈ segmentPath a xs b := by
  induction xs generalizing a with
  | nil => exact ⟨left_mem_segment ℝ a b,right_mem_segment ℝ a b⟩
  | cons x xs ih =>
    exact ⟨Or.inl (left_mem_segment ℝ a x),Or.inr (ih x).2⟩

private theorem segmentPath_positive (L : Point3 →ₗ[ℝ] ℝ) (a b : Point3) (xs : List Point3)
    (ha : 0 ≤ L a) (hb : 0 ≤ L b) (hs : ∀ x ∈ xs, 0 ≤ L x) :
    segmentPath a xs b ⊆ {y | 0 ≤ L y} := by
  induction xs generalizing a with
  | nil => exact (convex_halfSpace_ge L.isLinear 0).segment_subset ha hb
  | cons x xs ih =>
    have hx : 0 ≤ L x := hs x (by simp)
    exact union_subset ((convex_halfSpace_ge L.isLinear 0).segment_subset ha hx)
      (ih x hx (fun y hy => hs y (by simp [hy])))

private theorem segment_zero_neg_cut_eq (L : Point3 →ₗ[ℝ] ℝ) (a b : Point3)
    (ha : L a = 0) (hb : L b < 0) :
    segment ℝ a b ∩ {x | 0 ≤ L x} = {a} := by
  have hna : 0 ≤ L a := ha.ge
  rw [segment_inter_nonnegativeHalfspace,ite_eq_left hna,ite_eq_right (not_le_of_gt hb)]
  simp [linearCutPoint,ha,segment_same]

private theorem segmentPath_neg_to_zero (L : Point3 →ₗ[ℝ] ℝ) (a b : Point3) (xs : List Point3)
    (ha : L a < 0) (hb : L b = 0) (hs : ∀ x ∈ xs, L x < 0) :
    segmentPath a xs b ∩ {y | 0 ≤ L y} ⊆ {b} := by
  induction xs generalizing a with
  | nil =>
    change segment ℝ a b ∩ _ ⊆ _
    rw [segment_symm ℝ a b,segment_zero_neg_cut_eq L b a hb ha]
  | cons x xs ih =>
    have hx : L x < 0 := hs x (by simp)
    change (segment ℝ a x ∪ segmentPath x xs b) ∩ _ ⊆ _
    rw [union_inter_distrib_right, segment_inter_nonnegativeHalfspace,ite_eq_right (not_le_of_gt ha),
      ite_eq_right (not_le_of_gt hx),empty_union]
    exact ih x hx (fun y hy => hs y (by simp [hy]))

private theorem segmentPath_negative_cut_subset (L : Point3 →ₗ[ℝ] ℝ) (a b : Point3)
    (xs : List Point3) (ha : L a = 0) (hb : L b = 0) (hn : xs ≠ [])
    (hs : ∀ x ∈ xs, L x < 0) : segmentPath a xs b ∩ {y | 0 ≤ L y} ⊆ {a,b} := by
  cases xs with
  | nil => exact (hn rfl).elim
  | cons x xs =>
    have hx : L x < 0 := hs x (by simp)
    change (segment ℝ a x ∪ segmentPath x xs b) ∩ _ ⊆ _
    rw [union_inter_distrib_right,segment_zero_neg_cut_eq L a x ha hx]
    exact union_subset (by simp) ((segmentPath_neg_to_zero L x b xs hx hb
      (fun y hy => hs y (by simp [hy]))).trans (by simp))

private theorem chord_eq_of_two_boundary_zeros {K : Set Point3} (hK : IsCompact K)
    (hconv : Convex ℝ K) (hd : Module.finrank ℝ (affineSpan ℝ K).direction = 2)
    (L : Point3 →ₗ[ℝ] ℝ) (hp : ∃ x ∈ K, 0 < L x) (hm : ∃ x ∈ K, L x < 0)
    {a b : Point3} (hab : a ≠ b) (ha : a ∈ intrinsicFrontier ℝ K) (hb : b ∈ intrinsicFrontier ℝ K)
    (hLa : L a = 0) (hLb : L b = 0) : K ∩ {x | L x = 0} = segment ℝ a b := by
  obtain ⟨p,q,_,hsec,hends⟩ := planarCut_chord hK hconv hd L hp hm
  have hpa : a = p ∨ a = q := by
    have h : a ∈ ({p,q} : Set Point3) := hends ▸ ⟨ha,hLa⟩
    simpa only [mem_insert_iff,mem_singleton_iff] using h
  have hpb : b = p ∨ b = q := by
    have h : b ∈ ({p,q} : Set Point3) := hends ▸ ⟨hb,hLb⟩
    simpa only [mem_insert_iff,mem_singleton_iff] using h
  rcases hpa with rfl | rfl <;> rcases hpb with rfl | rfl
  · exact (hab rfl).elim
  · exact hsec
  · exact hsec.trans (segment_symm ℝ _ _)
  · exact (hab rfl).elim

/-- Once the two chord endpoints split a boundary list into its kept and
discarded arcs, deleting the discarded arc gives the exact clipped boundary.
The angular perimeter cannot increase. -/
theorem polygonCut_of_split {K : Set Point3} (hK : IsCompact K) (hconv : Convex ℝ K)
    (hd : Module.finrank ℝ (affineSpan ℝ K).direction = 2) (L : Point3 →ₗ[ℝ] ℝ)
    (hp : ∃ x ∈ K, 0 < L x) (hm : ∃ x ∈ K, L x < 0)
    (a b : Point3) (kept discarded : List Point3) (hab : a ≠ b)
    (ha : L a = 0) (hb : L b = 0) (hn : discarded ≠ [])
    (hk : ∀ x ∈ kept, 0 ≤ L x) (hr : ∀ x ∈ discarded, L x < 0)
    (hF : intrinsicFrontier ℝ K = segmentCycle (a :: (kept ++ b :: discarded)))
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] (f : Point3 → V) :
    intrinsicFrontier ℝ (K ∩ {x | 0 ≤ L x}) = segmentCycle (a :: (kept ++ [b])) ∧
      angularCycleLength ((a :: (kept ++ [b])).map f) ≤
        angularCycleLength ((a :: (kept ++ b :: discarded)).map f) := by
  have hOld : intrinsicFrontier ℝ K = segmentPath a kept b ∪ segmentPath b discarded a := by
    rw [hF]
    exact segmentPath_append a b a kept discarded
  have ae : a ∈ intrinsicFrontier ℝ K := hOld.symm ▸ Or.inl (segmentPath_endpoints a kept b).1
  have be : b ∈ intrinsicFrontier ℝ K := hOld.symm ▸ Or.inl (segmentPath_endpoints a kept b).2
  have hchord := chord_eq_of_two_boundary_zeros hK hconv hd L hp hm hab ae be ha hb
  have hpos := segmentPath_positive L a b kept ha.ge hb.ge hk
  have hneg := segmentPath_negative_cut_subset L b a discarded hb ha hn hr
  refine ⟨?_,?_⟩
  · rw [(planarCut_frontier hK.isClosed hconv L hp hm).2,hOld,hchord,union_inter_distrib_right,
      inter_eq_left.mpr hpos]
    change (segmentPath a kept b ∪ (segmentPath b discarded a ∩ {x | 0 ≤ L x})) ∪
      segment ℝ a b = segmentPath a (kept ++ [b]) a
    rw [segmentPath_append]
    change _ = segmentPath a kept b ∪ segment ℝ b a
    rw [segment_symm ℝ b a,union_assoc]
    have hends : ({b,a} : Set Point3) ⊆ segment ℝ a b := by
      simp only [insert_subset_iff,singleton_subset_iff]
      exact ⟨right_mem_segment ℝ _ _,left_mem_segment ℝ _ _⟩
    rw [union_eq_right.mpr (hneg.trans hends)]
  · apply angularCycleLength_mono
    exact ((List.sublist_append_left (a :: (kept ++ [b])) discarded).trans
      (by simp only [List.cons_append,List.append_assoc]; rfl)).map f

/-- The ordered edges of a path with specified endpoints. -/
@[expose] def polygonPathEdges {α : Type*} (a : α) (xs : List α) (b : α) : List (α × α) :=
  match xs with
  | [] => [(a,b)]
  | x :: xs => (a,x) :: polygonPathEdges x xs b

/-- The ordered edges of a closed boundary list. -/
@[expose] def polygonCycleEdges {α : Type*} (xs : List α) : List (α × α) :=
  match xs with
  | [] => []
  | a :: ys => polygonPathEdges a ys a

theorem polygonPathEdges_append {α : Type*} (a b c : α) (xs ys : List α) :
    polygonPathEdges a (xs ++ b :: ys) c = polygonPathEdges a xs b ++ polygonPathEdges b ys c := by
  induction xs generalizing a with
  | nil => rfl
  | cons x xs ih => simp [polygonPathEdges, ih]

theorem polygonCycleEdges_eq_zip {α : Type*} (xs : List α) :
    polygonCycleEdges xs = xs.zip (xs.drop 1 ++ xs.take 1) := by
  have path (a b : α) (xs : List α) : polygonPathEdges a xs b = (a :: xs).zip (xs ++ [b]) := by
    induction xs generalizing a with
    | nil => rfl
    | cons x xs ih => simp [polygonPathEdges,ih]
  cases xs with
  | nil => rfl
  | cons a xs => exact path a a xs

private theorem polygonCycleEdges_move_head {α : Type*} (a : α) (xs : List α) :
    (polygonCycleEdges (a :: xs)).Perm (polygonCycleEdges (xs ++ [a])) := by
  cases xs with
  | nil => exact List.Perm.refl _
  | cons b xs =>
    change (((a,b) :: polygonPathEdges b xs a)).Perm (polygonPathEdges b (xs ++ [a]) b)
    rw [polygonPathEdges_append]
    exact List.perm_append_comm (l₁ := [(a,b)])

theorem polygonCycleEdges_append_perm {α : Type*} (xs ys : List α) :
    (polygonCycleEdges (xs ++ ys)).Perm (polygonCycleEdges (ys ++ xs)) := by
  induction xs generalizing ys with
  | nil => simp
  | cons a xs ih =>
    refine (polygonCycleEdges_move_head a (xs ++ ys)).trans ?_
    simpa only [List.append_assoc,List.singleton_append] using ih (ys ++ [a])

theorem polygonCycleEdges_perm_of_isRotated {α : Type*} {xs ys : List α} (h : xs ~r ys) :
    (polygonCycleEdges xs).Perm (polygonCycleEdges ys) := by
  obtain ⟨n,hn,rfl⟩ := List.isRotated_iff_mod.mp h
  rw [List.rotate_eq_drop_append_take hn]
  have he := polygonCycleEdges_append_perm (xs.take n) (xs.drop n)
  rwa [List.take_append_drop] at he

private theorem polygonPathEdges_fst {α : Type*} (a b : α) (xs : List α) :
    (polygonPathEdges a xs b).map Prod.fst = a :: xs := by
  induction xs generalizing a with
  | nil => rfl
  | cons x xs ih => simp [polygonPathEdges,ih]

theorem polygonCycleEdges_fst {α : Type*} (xs : List α) :
    (polygonCycleEdges xs).map Prod.fst = xs := by
  cases xs with
  | nil => rfl
  | cons a xs => exact polygonPathEdges_fst a a xs

theorem polygonCycleEdges_mem_fst {α : Type*} {xs : List α} {e : α × α}
    (he : e ∈ polygonCycleEdges xs) : e.1 ∈ xs :=
  polygonCycleEdges_fst xs ▸ List.mem_map_of_mem he

theorem polygonCycleEdges_mem_snd {α : Type*} {xs : List α} {e : α × α}
    (he : e ∈ polygonCycleEdges xs) : e.2 ∈ xs := by
  have path (a b : α) (ls : List α) : (polygonPathEdges a ls b).map Prod.snd = ls ++ [b] := by
    induction ls generalizing a with
    | nil => rfl
    | cons x ls ih => simp [polygonPathEdges,ih]
  cases xs with
  | nil => simp [polygonCycleEdges] at he
  | cons a ls =>
    have hh : e.2 ∈ ls ++ [a] := path a a ls ▸ List.mem_map_of_mem he
    simpa [List.mem_append,or_comm] using hh

theorem segmentCycle_eq_iUnion_edges (xs : List Point3) :
    segmentCycle xs = ⋃ e ∈ polygonCycleEdges xs, segment ℝ e.1 e.2 := by
  have path (a b : Point3) (xs : List Point3) :
      segmentPath a xs b = ⋃ e ∈ polygonPathEdges a xs b, segment ℝ e.1 e.2 := by
    induction xs generalizing a with
    | nil => simp [segmentPath,polygonPathEdges]
    | cons x xs ih =>
      rw [segmentPath,ih x]
      simp [polygonPathEdges]
  cases xs with
  | nil => simp [segmentCycle,polygonCycleEdges]
  | cons a xs => exact path a a xs

theorem mem_segmentCycle_of_mem {xs : List Point3} {x : Point3} (hx : x ∈ xs) :
    x ∈ segmentCycle xs := by
  have hx' : x ∈ (polygonCycleEdges xs).map Prod.fst := by rwa [polygonCycleEdges_fst]
  obtain ⟨e,he,rfl⟩ := List.mem_map.mp hx'
  rw [segmentCycle_eq_iUnion_edges]
  exact mem_iUnion₂.mpr ⟨e,he,left_mem_segment ℝ _ _⟩

theorem segmentCycle_eq_of_isRotated {xs ys : List Point3} (h : xs ~r ys) :
    segmentCycle xs = segmentCycle ys := by
  simp only [segmentCycle_eq_iUnion_edges,(polygonCycleEdges_perm_of_isRotated h).mem_iff]

private theorem angularCycleLength_eq_of_isRotated {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] {xs ys : List V} (h : xs ~r ys) :
    angularCycleLength xs = angularCycleLength ys := by
  obtain ⟨n,hn,rfl⟩ := List.isRotated_iff_mod.mp h
  rw [List.rotate_eq_drop_append_take hn]
  have he := angularCycleLength_append_comm (xs.take n) (xs.drop n)
  rwa [List.take_append_drop] at he

private theorem sign_iff_of_nonnegative_mul {x y : ℝ} (hx : x ≠ 0) (hy : y ≠ 0) (h : 0 ≤ x*y) :
    0 < y ↔ 0 < x := by
  constructor
  · intro hy'
    by_contra! hnx
    exact (not_lt_of_ge h) (mul_neg_of_neg_of_pos (lt_of_le_of_ne hnx hx) hy')
  · intro hx'
    by_contra! hny
    exact (not_lt_of_ge h) (mul_neg_of_pos_of_neg hx' (lt_of_le_of_ne hny hy))

private theorem sign_agrees_on_path {α : Type*} (L : α → ℝ) (a b : α) (xs : List α)
    (hn : ∀ x ∈ a :: xs, L x ≠ 0)
    (hEdges : ∀ e ∈ polygonPathEdges a xs b, 0 ≤ L e.1*L e.2) :
    ∀ x ∈ a :: xs, 0 < L x ↔ 0 < L a := by
  induction xs generalizing a with
  | nil => simp
  | cons u xs ih =>
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact Iff.rfl
    · have hp : 0 ≤ L a*L u := hEdges (a,u) (by simp [polygonPathEdges])
      have he := sign_iff_of_nonnegative_mul (hn a (by simp)) (hn u (by simp)) hp
      exact (ih u (fun v hv => hn v (List.mem_cons_of_mem _ hv))
        (fun e he => hEdges e (List.mem_cons_of_mem _ he)) x hx).trans he

private theorem sign_uniform_between {α : Type*} (L : α → ℝ) (a b : α) (xs : List α)
    (hn : ∀ x ∈ xs, L x ≠ 0)
    (hEdges : ∀ e ∈ polygonPathEdges a xs b, 0 ≤ L e.1*L e.2) :
    (∀ x ∈ xs, 0 < L x) ∨ (∀ x ∈ xs, L x < 0) := by
  cases xs with
  | nil => simp
  | cons u xs =>
    have he := sign_agrees_on_path L u b xs hn (fun e he => hEdges e (List.mem_cons_of_mem _ he))
    by_cases hu : 0 < L u
    · exact Or.inl fun x hx => (he x hx).mpr hu
    · exact Or.inr fun x hx => lt_of_le_of_ne (le_of_not_gt (fun hp => hu ((he x hx).mp hp))) (hn x hx)

/-- If both signs occur on a simple boundary list with two zeros, and no edge
crosses strictly between the two signs, then the zero vertices separate the
positive and negative arcs. The boundary can be rotated to put the kept arc first. -/
theorem exists_signed_polygon_split {α : Type*} (L : α → ℝ) (xs : List α) (a b : α)
    (hab : a ≠ b) (hs : xs.Nodup) (ha : a ∈ xs) (hb : b ∈ xs)
    (hzero : ∀ x ∈ xs, L x = 0 → x = a ∨ x = b)
    (hEdges : ∀ e ∈ polygonCycleEdges xs, 0 ≤ L e.1*L e.2)
    (hp : ∃ x ∈ xs, 0 < L x) (hm : ∃ x ∈ xs, L x < 0)
    (ha₀ : L a = 0) (hb₀ : L b = 0) :
    ∃ u v kept discarded, ((u = a ∧ v = b) ∨ (u = b ∧ v = a)) ∧
      xs ~r (u :: (kept ++ v :: discarded)) ∧
      (∀ x ∈ kept, 0 < L x) ∧ (∀ x ∈ discarded, L x < 0) ∧ discarded ≠ [] := by
  obtain ⟨pre,post,hxs⟩ := List.append_of_mem ha
  have hrot : xs ~r (a :: (post ++ pre)) := by
    rw [hxs,← List.cons_append]
    exact List.isRotated_append
  have hbm : b ∈ post ++ pre := by
    have H := List.mem_cons.mp (hrot.mem_iff.mp hb)
    exact H.resolve_left hab.symm
  obtain ⟨us,vs,h⟩ := List.append_of_mem hbm
  rw [h] at hrot
  have hnodup := hrot.nodup_iff.mp hs
  have hnoa : a ∉ us ++ b :: vs := (List.nodup_cons.mp hnodup).1
  have hnob1 : b ∉ us := by
    have hd := List.disjoint_of_nodup_append (List.nodup_cons.mp hnodup).2
    exact fun he => List.disjoint_left.mp hd he (by simp)
  have hnob2 : b ∉ vs :=
    (List.nodup_cons.mp ((List.nodup_cons.mp hnodup).2.of_append_right)).1
  have hZero (x : α) (hx : x ∈ us ∨ x ∈ vs) : L x ≠ 0 := by
    have hm' : x ∈ us ++ b :: vs := by rcases hx with hx | hx <;> simp [hx]
    intro hL
    rcases hzero x (hrot.mem_iff.mpr (List.mem_cons_of_mem _ hm')) hL with rfl | rfl
    · exact hnoa hm'
    · exact hx.elim hnob1 hnob2
  have hArc : ∀ e ∈ polygonPathEdges a us b ++ polygonPathEdges b vs a, 0 ≤ L e.1*L e.2 := by
    intro e he
    apply hEdges e ((polygonCycleEdges_perm_of_isRotated hrot).mem_iff.mpr ?_)
    change e ∈ polygonPathEdges a (us ++ b :: vs) a
    rwa [polygonPathEdges_append]
  have hu := sign_uniform_between L a b us (fun x hx => hZero x (Or.inl hx))
    (fun e he => hArc e (List.mem_append_left _ he))
  have hv := sign_uniform_between L b a vs (fun x hx => hZero x (Or.inr hx))
    (fun e he => hArc e (List.mem_append_right _ he))
  obtain ⟨xp,hxp,hp'⟩ := hp
  obtain ⟨xm,hxm,hm'⟩ := hm
  have hxp' : xp ∈ us ∨ xp ∈ vs := by
    have H := hrot.mem_iff.mp hxp
    simp only [List.mem_cons,List.mem_append] at H
    rcases H with rfl | H | rfl | H
    · rw [ha₀] at hp'; exact (lt_irrefl _ hp').elim
    · exact Or.inl H
    · rw [hb₀] at hp'; exact (lt_irrefl _ hp').elim
    · exact Or.inr H
  have hxm' : xm ∈ us ∨ xm ∈ vs := by
    have H := hrot.mem_iff.mp hxm
    simp only [List.mem_cons,List.mem_append] at H
    rcases H with rfl | H | rfl | H
    · rw [ha₀] at hm'; exact (lt_irrefl _ hm').elim
    · exact Or.inl H
    · rw [hb₀] at hm'; exact (lt_irrefl _ hm').elim
    · exact Or.inr H
  rcases hu with hu | hu <;> rcases hv with hv | hv
  · exact (not_lt_of_gt (hxm'.elim (hu xm) (hv xm)) hm').elim
  · refine ⟨a,b,us,vs,Or.inl ⟨rfl,rfl⟩,hrot,hu,hv,?_⟩
    have he := hxm'.resolve_left (fun hx => (not_lt_of_gt (hu xm hx)) hm')
    intro hn
    simp [hn] at he
  · have hrot' : xs ~r (b :: (vs ++ a :: us)) := hrot.trans (by
      simpa only [List.cons_append] using
        (List.isRotated_append (l := a :: us) (l' := b :: vs)))
    refine ⟨b,a,vs,us,Or.inr ⟨rfl,rfl⟩,hrot',hv,hu,?_⟩
    have he := hxm'.resolve_right (fun hx => (not_lt_of_gt (hv xm hx)) hm')
    intro hn
    simp [hn] at he
  · exact (not_lt_of_gt hp' (hxp'.elim (hu xp) (hv xp))).elim

/-- A polygon has distinct vertices, no vertex inside an edge, and
no overlap of open edges. -/
structure SimplePolygon (xs : List Point3) : Prop where
  nodup : xs.Nodup
  vertex_outside_open_edge : ∀ e ∈ polygonCycleEdges xs, ∀ x ∈ xs, x ∉ openSegment ℝ e.1 e.2
  disjoint_open_edges : ∀ e ∈ polygonCycleEdges xs, ∀ g ∈ polygonCycleEdges xs, e ≠ g →
    Disjoint (openSegment ℝ e.1 e.2) (openSegment ℝ g.1 g.2)

theorem SimplePolygon.of_isRotated {xs ys : List Point3} (h : SimplePolygon xs) (hr : xs ~r ys) :
    SimplePolygon ys := by
  have he := polygonCycleEdges_perm_of_isRotated hr
  exact ⟨hr.nodup_iff.mp h.nodup,
    fun e he' x hx => h.vertex_outside_open_edge e (he.mem_iff.mpr he') x (hr.mem_iff.mpr hx),
    fun e he' g hg' hne => h.disjoint_open_edges e (he.mem_iff.mpr he') g (he.mem_iff.mpr hg') hne⟩

private theorem polygonSplit_simple {u v : Point3} {kept discarded : List Point3}
    (hs : SimplePolygon (u :: (kept ++ v :: discarded)))
    (hChord : Disjoint (openSegment ℝ v u) (segmentCycle (u :: (kept ++ v :: discarded)))) :
    SimplePolygon (u :: (kept ++ [v])) := by
  let xs := u :: (kept ++ v :: discarded)
  let ys := u :: (kept ++ [v])
  let E := polygonPathEdges u kept v
  have hsub : ys.Sublist xs := by
    exact (List.sublist_append_left (u :: (kept ++ [v])) discarded).trans
      (by simp only [List.cons_append,List.append_assoc]; rfl)
  have he (e : Point3 × Point3) (h : e ∈ E) : e ∈ polygonCycleEdges xs := by
    change e ∈ polygonPathEdges u (kept ++ v :: discarded) u
    rw [polygonPathEdges_append]
    exact List.mem_append_left _ h
  have hyE : polygonCycleEdges ys = E ++ [(v,u)] := polygonPathEdges_append u v u kept []
  have hmem (x : Point3) (hx : x ∈ xs) : x ∈ segmentCycle xs := by
    rw [← polygonCycleEdges_fst xs] at hx
    obtain ⟨e,he,rfl⟩ := List.mem_map.mp hx
    rw [segmentCycle_eq_iUnion_edges]
    exact Set.mem_iUnion₂.mpr ⟨e,he,left_mem_segment ℝ _ _⟩
  have hArcOutsideChord (e : Point3 × Point3) (he' : e ∈ E) :
      Disjoint (openSegment ℝ e.1 e.2) (openSegment ℝ v u) := by
    refine hChord.symm.mono_left ?_
    intro x hx
    rw [segmentCycle_eq_iUnion_edges]
    exact Set.mem_iUnion₂.mpr ⟨e,he e he',openSegment_subset_segment ℝ _ _ hx⟩
  refine ⟨hsub.nodup hs.nodup,?_,?_⟩
  · intro e he' x hx
    rw [hyE,List.mem_append,List.mem_singleton] at he'
    rcases he' with h | rfl
    · exact hs.vertex_outside_open_edge e (he e h) x (hsub.subset hx)
    · exact fun hx' => Set.disjoint_left.mp hChord hx' (hmem x (hsub.subset hx))
  · intro e he' g hg hne
    rw [hyE,List.mem_append,List.mem_singleton] at he' hg
    rcases he' with he' | rfl <;> rcases hg with hg | rfl
    · exact hs.disjoint_open_edges e (he e he') g (he g hg) hne
    · exact hArcOutsideChord e he'
    · exact (hArcOutsideChord g hg).symm
    · exact (hne rfl).elim

/-- Once the chord endpoints are included among the boundary vertices,
an entire half-plane cut is obtained by rotating the list and deleting the
outside arc. Its angular perimeter is at most the original perimeter. -/
theorem polygonCut_of_refined_boundary {K : Set Point3} (hK : IsCompact K) (hconv : Convex ℝ K)
    (hd : Module.finrank ℝ (affineSpan ℝ K).direction = 2) (L : Point3 →ₗ[ℝ] ℝ)
    (xs : List Point3) (hF : intrinsicFrontier ℝ K = segmentCycle xs) (hs : SimplePolygon xs)
    (hRef : ∀ x ∈ intrinsicFrontier ℝ K, L x = 0 → x ∈ xs)
    (hp : ∃ p ∈ xs, 0 < L p) (hm : ∃ m ∈ xs, L m < 0)
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] (f : Point3 → V) :
    ∃ ys : List Point3, SimplePolygon ys ∧ intrinsicFrontier ℝ (K ∩ {x | 0 ≤ L x}) = segmentCycle ys ∧
      angularCycleLength (ys.map f) ≤ angularCycleLength (xs.map f) := by
  have hv (x : Point3) (hx : x ∈ xs) : x ∈ intrinsicFrontier ℝ K := by
    rw [hF,segmentCycle_eq_iUnion_edges]
    rw [← polygonCycleEdges_fst xs] at hx
    obtain ⟨e,he,rfl⟩ := List.mem_map.mp hx
    exact Set.mem_iUnion₂.mpr ⟨e,he,left_mem_segment ℝ _ _⟩
  have hclosed : intrinsicFrontier ℝ K ⊆ K := by
    have he : intrinsicFrontier ℝ K ⊆ closure K :=
      intrinsicFrontier_subset_intrinsicClosure.trans intrinsicClosure_subset_closure
    rwa [hK.isClosed.closure_eq] at he
  have hpK : ∃ p ∈ K, 0 < L p := by
    obtain ⟨p,hp,hL⟩ := hp
    exact ⟨p,hclosed (hv p hp),hL⟩
  have hmK : ∃ m ∈ K, L m < 0 := by
    obtain ⟨m,hm,hL⟩ := hm
    exact ⟨m,hclosed (hv m hm),hL⟩
  obtain ⟨a,b,hab,_,hends⟩ := planarCut_chord hK hconv hd L hpK hmK
  have ha : a ∈ intrinsicFrontier ℝ K ∩ {x | L x = 0} := hends.symm ▸ (by simp : a ∈ {a,b})
  have hb : b ∈ intrinsicFrontier ℝ K ∩ {x | L x = 0} := hends.symm ▸ (by simp : b ∈ {a,b})
  have hzero (x : Point3) (hx : x ∈ xs) (hL : L x = 0) : x = a ∨ x = b := by
    have he : x ∈ intrinsicFrontier ℝ K ∩ {x | L x = 0} := ⟨hv x hx,hL⟩
    rw [hends] at he
    simpa only [mem_insert_iff,mem_singleton_iff] using he
  have hsign (e : Point3 × Point3) (he : e ∈ polygonCycleEdges xs) : 0 ≤ L e.1*L e.2 := by
    by_contra! hn
    have hCut : ∃ z ∈ openSegment ℝ e.1 e.2, L z = 0 := by
      rcases mul_neg_iff.mp hn with ⟨h₁,h₂⟩ | ⟨h₁,h₂⟩
      · exact ⟨_,linearCutPoint_mem_openSegment L e.1 e.2 h₁ h₂,
          (linearCutPoint_mem_segment L e.1 e.2 h₁.le h₂).2⟩
      · rw [openSegment_symm ℝ e.1 e.2]
        exact ⟨_,linearCutPoint_mem_openSegment L e.2 e.1 h₂ h₁,
          (linearCutPoint_mem_segment L e.2 e.1 h₂.le h₁).2⟩
    obtain ⟨z,hz,hL⟩ := hCut
    have hzF : z ∈ intrinsicFrontier ℝ K := by
      rw [hF,segmentCycle_eq_iUnion_edges]
      exact Set.mem_iUnion₂.mpr ⟨e,he,openSegment_subset_segment ℝ _ _ hz⟩
    exact hs.vertex_outside_open_edge e he z (hRef z hzF hL) hz
  obtain ⟨u,v,kept,discarded,huv,hrot,hkeep,hdisc,hdN⟩ :=
    exists_signed_polygon_split L xs a b hab hs.nodup (hRef a ha.1 ha.2) (hRef b hb.1 hb.2)
      hzero hsign hp hm ha.2 hb.2
  have ⟨hne,hu,hv'⟩ : u ≠ v ∧ L u = 0 ∧ L v = 0 := by
    rcases huv with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact ⟨hab,ha.2,hb.2⟩
    · exact ⟨hab.symm,hb.2,ha.2⟩
  have hF' := hF.trans (segmentCycle_eq_of_isRotated hrot)
  have ⟨hB,hC⟩ := polygonCut_of_split hK hconv hd L hpK hmK u v kept discarded hne hu hv'
    hdN (fun x hx => (hkeep x hx).le) hdisc hF' f
  have hEndsUV : intrinsicFrontier ℝ K ∩ {x | L x = 0} = {u,v} := by
    rcases huv with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact hends
    · exact hends.trans (Set.pair_comm _ _)
  have hChord : Disjoint (openSegment ℝ v u) (segmentCycle (u :: (kept ++ v :: discarded))) := by
    rw [← hF']
    apply Set.disjoint_left.mpr
    intro z hseg hz
    have hzL : L z = 0 := by
      obtain ⟨s,t,_,_,_,rfl⟩ := hseg
      simp [hu,hv']
    have hEnd : z ∈ intrinsicFrontier ℝ K ∩ {x | L x = 0} := ⟨hz,hzL⟩
    rw [hEndsUV] at hEnd
    rcases mem_insert_iff.mp hEnd with rfl | hEq
    · exact hne.symm (right_mem_openSegment_iff.mp hseg)
    · rw [mem_singleton_iff.mp hEq] at hseg
      exact hne.symm (left_mem_openSegment_iff.mp hseg)
  exact ⟨_,polygonSplit_simple (hs.of_isRotated hrot) hChord,hB,
    hC.trans_eq (angularCycleLength_eq_of_isRotated (hrot.map f)).symm⟩

private theorem segment_subdivision {a b x : Point3} (hab : a ≠ b) (hx : x ∈ openSegment ℝ a b) :
    segment ℝ a x ∪ segment ℝ x b = segment ℝ a b ∧
    openSegment ℝ a x ⊆ openSegment ℝ a b ∧ openSegment ℝ x b ⊆ openSegment ℝ a b ∧
    Disjoint (openSegment ℝ a x) (openSegment ℝ x b) := by
  rw [openSegment_eq_image_lineMap] at hx
  obtain ⟨t,ht,rfl⟩ := hx
  let f : ℝ →ᵃ[ℝ] Point3 := AffineMap.lineMap a b
  have fa : f 0 = a := AffineMap.lineMap_apply_zero _ _
  have fb : f 1 = b := AffineMap.lineMap_apply_one _ _
  have hs (l r : ℝ) (hlr : l ≤ r) : segment ℝ (f l) (f r) = f '' Icc l r := by
    rw [← segment_eq_Icc hlr,image_segment]
  have ho (l r : ℝ) (hlr : l < r) : openSegment ℝ (f l) (f r) = f '' Ioo l r := by
    rw [← openSegment_eq_Ioo hlr,image_openSegment]
  change (segment ℝ a (f t) ∪ segment ℝ (f t) b = segment ℝ a b) ∧ _
  have hspan : Icc 0 t ∪ Icc t 1 = Icc 0 1 := by
    ext k
    simp only [mem_union,mem_Icc]
    constructor
    · rintro (⟨h₁,h₂⟩ | ⟨h₁,h₂⟩)
      · exact ⟨h₁,h₂.trans ht.2.le⟩
      · exact ⟨ht.1.le.trans h₁,h₂⟩
    · intro hk
      rcases le_total k t with he | he
      · exact Or.inl ⟨hk.1,he⟩
      · exact Or.inr ⟨he,hk.2⟩
  have hlinj : Function.Injective f := AffineMap.lineMap_injective ℝ hab
  refine ⟨?_,?_⟩
  · rw [← fa,← fb,hs _ _ ht.1.le,hs _ _ ht.2.le,hs _ _ zero_le_one,← image_union,hspan]
  · change openSegment ℝ a (f t) ⊆ openSegment ℝ a b ∧ openSegment ℝ (f t) b ⊆ openSegment ℝ a b ∧
      Disjoint (openSegment ℝ a (f t)) (openSegment ℝ (f t) b)
    rw [← fa,← fb,ho _ _ ht.1,ho _ _ ht.2,ho _ _ zero_lt_one]
    refine ⟨image_mono (fun k hk => ⟨hk.1,hk.2.trans ht.2⟩),
      image_mono (fun k hk => ⟨ht.1.trans hk.1,hk.2⟩),?_⟩
    rw [Set.disjoint_image_iff hlinj]
    exact Set.disjoint_left.mpr fun k hl hr => (not_lt_of_gt hl.2) hr.1

private theorem rotates_to_edge {xs : List Point3} (hs : xs.Nodup) {x a b : Point3}
    (hx : x ∉ xs) (he : (a,b) ∈ polygonCycleEdges xs) (hseg : x ∈ segment ℝ a b) :
    ∃ ts : List Point3, xs ~r (a :: b :: ts) := by
  have ha : a ∈ xs := polygonCycleEdges_fst xs ▸ List.mem_map.mpr ⟨(a,b),he,rfl⟩
  obtain ⟨pre,post,hxs⟩ := List.append_of_mem ha
  have hr : xs ~r (a :: (post ++ pre)) := by
    rw [hxs,← List.cons_append]
    exact List.isRotated_append
  have hrot := (polygonCycleEdges_perm_of_isRotated hr).mem_iff.mp he
  generalize hps : post ++ pre = rest at hr hrot
  cases rest with
  | nil =>
    have hb : b = a := by simpa [polygonCycleEdges,polygonPathEdges] using hrot
    subst b
    have hxa : x = a := by simpa only [segment_same,mem_singleton_iff] using hseg
    exact (hx (hxa.symm ▸ ha)).elim
  | cons c ts =>
    have hnot : a ∉ c :: ts := (List.nodup_cons.mp (hr.nodup_iff.mp hs)).1
    change (a,b) ∈ (a,c) :: polygonPathEdges c ts a at hrot
    rcases List.mem_cons.mp hrot with hEq | ht
    · have hbc : b = c := congrArg Prod.snd hEq
      exact ⟨ts,hbc.symm ▸ hr⟩
    · exact (hnot (polygonPathEdges_fst c a ts ▸ List.mem_map.mpr ⟨(a,b),ht,rfl⟩)).elim

private theorem simplePolygon_insert_on_head_edge {a b x : Point3} {ts : List Point3}
    (h : SimplePolygon (a :: b :: ts)) (hx : x ∉ a :: b :: ts)
    (hm : x ∈ openSegment ℝ a b) : SimplePolygon (a :: x :: b :: ts) := by
  have ha : x ≠ a := fun he => hx (by simp [he])
  have hb : x ≠ b := fun he => hx (by simp [he])
  have hab : a ≠ b := fun he => (List.nodup_cons.mp h.nodup).1 (by simp [he])
  have ⟨_,hl,hr,hxy⟩ := segment_subdivision hab hm
  let T := polygonPathEdges b ts a
  have hT (e : Point3 × Point3) (he : e ∈ T) : e ≠ (a,b) := by
    intro hEq
    rw [hEq] at he
    exact (List.nodup_cons.mp h.nodup).1
      (polygonPathEdges_fst b a ts ▸ List.mem_map.mpr ⟨(a,b),he,rfl⟩)
  have hOld (e : Point3 × Point3) (he : e ∈ T) : e ∈ polygonCycleEdges (a :: b :: ts) :=
    List.mem_cons_of_mem _ he
  have h0 : (a,b) ∈ polygonCycleEdges (a :: b :: ts) := List.mem_cons_self
  refine ⟨?_,?_,?_⟩
  · exact List.nodup_cons.mpr ⟨fun he => by
      rcases List.mem_cons.mp he with he | he
      · exact ha he.symm
      · exact (List.nodup_cons.mp h.nodup).1 he,
      List.nodup_cons.mpr ⟨fun he => hx (List.mem_cons_of_mem _ he),(List.nodup_cons.mp h.nodup).2⟩⟩
  · intro e he y hy
    change e ∈ (a,x) :: (x,b) :: T at he
    have hY : y = x ∨ y ∈ a :: b :: ts := by
      rcases List.mem_cons.mp hy with rfl | hy
      · exact Or.inr (by simp)
      · rcases List.mem_cons.mp hy with rfl | hy
        · exact Or.inl rfl
        · exact Or.inr (List.mem_cons_of_mem _ hy)
    rcases List.mem_cons.mp he with rfl | he
    · rcases hY with rfl | hy
      · exact fun he => ha.symm (right_mem_openSegment_iff.mp he)
      · exact fun he => h.vertex_outside_open_edge _ h0 y hy (hl he)
    · rcases List.mem_cons.mp he with rfl | heTail
      · rcases hY with rfl | hy
        · exact fun he => hb (left_mem_openSegment_iff.mp he)
        · exact fun he => h.vertex_outside_open_edge _ h0 y hy (hr he)
      · rcases hY with hEq | hy
        · subst y
          exact fun hy => Set.disjoint_left.mp
            (h.disjoint_open_edges _ h0 e (hOld e heTail) (hT e heTail).symm) hm hy
        · exact h.vertex_outside_open_edge _ (hOld e heTail) y hy
  · intro e he g hg hne
    change e ∈ (a,x) :: (x,b) :: T at he
    change g ∈ (a,x) :: (x,b) :: T at hg
    have hA (e : Point3 × Point3) (he : e ∈ T) :=
      h.disjoint_open_edges _ h0 e (hOld e he) (hT e he).symm
    rcases List.mem_cons.mp he with rfl | he
    · rcases List.mem_cons.mp hg with rfl | hg
      · exact (hne rfl).elim
      · rcases List.mem_cons.mp hg with rfl | hg
        · exact hxy
        · exact (hA g hg).mono_left hl
    · rcases List.mem_cons.mp he with rfl | he
      · rcases List.mem_cons.mp hg with rfl | hg
        · exact hxy.symm
        · rcases List.mem_cons.mp hg with rfl | hg
          · exact (hne rfl).elim
          · exact (hA g hg).mono_left hr
      · rcases List.mem_cons.mp hg with rfl | hg
        · exact ((hA e he).mono_left hl).symm
        · rcases List.mem_cons.mp hg with rfl | hg
          · exact ((hA e he).mono_left hr).symm
          · exact h.disjoint_open_edges e (hOld e he) g (hOld g hg) hne

/-- Add a boundary point to a simple polygon by subdividing the edge that
contains it. The boundary and its angular perimeter are preserved. -/
theorem SimplePolygon.insert_boundary_point {xs : List Point3} (hs : SimplePolygon xs)
    {x : Point3} (hx : x ∈ segmentCycle xs)
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] (f : Point3 →ₗ[ℝ] V)
    (hfx : f x ≠ 0) :
    ∃ ys : List Point3, SimplePolygon ys ∧ (∀ z, z ∈ ys ↔ z = x ∨ z ∈ xs) ∧
      segmentCycle ys = segmentCycle xs ∧ angularCycleLength (ys.map f) = angularCycleLength (xs.map f) := by
  classical
  by_cases hxs : x ∈ xs
  · exact ⟨xs,hs,fun z => ⟨Or.inr,fun h => h.elim (fun he => he.symm ▸ hxs) id⟩,rfl,rfl⟩
  rw [segmentCycle_eq_iUnion_edges] at hx
  obtain ⟨⟨a,b⟩,he,hmem⟩ := Set.mem_iUnion₂.mp hx
  obtain ⟨ts,hrot⟩ := rotates_to_edge hs.nodup hxs he hmem
  have hOld := hs.of_isRotated hrot
  have hnot : x ∉ a :: b :: ts := fun h => hxs (hrot.mem_iff.mpr h)
  have ha : x ≠ a := fun h => hnot (by simp [h])
  have hb : x ≠ b := fun h => hnot (by simp [h])
  have hab : a ≠ b := fun h => (List.nodup_cons.mp hOld.nodup).1 (by simp [h])
  have hOp := mem_openSegment_of_ne_left_right ha.symm hb.symm hmem
  have hz := (segment_subdivision hab hOp).1
  refine ⟨a :: x :: b :: ts,simplePolygon_insert_on_head_edge hOld hnot hOp,?_,?_,?_⟩
  · intro y
    rw [hrot.mem_iff]
    simp only [List.mem_cons]
    tauto
  · rw [segmentCycle_eq_of_isRotated hrot]
    change segment ℝ a x ∪ (segment ℝ x b ∪ segmentPath b ts a) = segment ℝ a b ∪ segmentPath b ts a
    rw [← union_assoc,hz]
  · rw [angularCycleLength_eq_of_isRotated (hrot.map f)]
    have hcone : f x ∈ Submodule.span ℝ≥0 {f a,f b} := by
      obtain ⟨r,s,hr,hs,_,he⟩ := hmem
      refine Submodule.mem_span_pair.mpr ⟨⟨r,hr⟩,⟨s,hs⟩,?_⟩
      change r • f a + s • f b = f x
      rw [← map_smul,← map_smul,← map_add,he]
    exact angularCycleLength_subdivide (f a) (f b) (f x) [] (ts.map f) hfx hcone

private theorem exists_positive_vertex {K : Set Point3} (hK : IsCompact K) (xs : List Point3)
    (hF : intrinsicFrontier ℝ K = segmentCycle xs) (L : Point3 →ₗ[ℝ] ℝ)
    (hp : ∃ p ∈ K, 0 < L p) (hm : ∃ m ∈ K, L m < 0) : ∃ p ∈ xs, 0 < L p := by
  obtain ⟨p,hp,hLp⟩ := hp
  obtain ⟨m,hm,hLm⟩ := hm
  obtain ⟨y,hy,hmax⟩ := hK.exists_isMaxOn ⟨p,hp⟩ L.continuous_of_finiteDimensional.continuousOn
  have hLy : 0 < L y := hLp.trans_le (hmax hp)
  have hyF : y ∈ intrinsicFrontier ℝ K := by
    rw [← closure_sdiff_intrinsicInterior,hK.isClosed.closure_eq]
    refine ⟨hy,?_⟩
    rintro ⟨yA,hyA,rfl⟩
    let A := affineSpan ℝ K
    let _ : Nonempty A := ⟨yA⟩
    let mA : A := ⟨m,subset_affineSpan ℝ K hm⟩
    let g : ℝ →ᵃ[ℝ] A := AffineMap.lineMap mA yA
    have hg : Continuous g := AffineMap.lineMap_continuous
    have h1 : g 1 = yA := AffineMap.lineMap_apply_one _ _
    obtain ⟨t,ht,htK⟩ := (hg.tendsto' _ _ h1).eventually_mem
      (mem_interior_iff_mem_nhds.mp hyA) |>.exists_gt
    have hbound := hmax (show (g t : Point3) ∈ K from htK)
    have he : (g t : Point3) = AffineMap.lineMap m (yA : Point3) t := A.subtype.apply_lineMap mA yA t
    change L (g t : Point3) ≤ L (yA : Point3) at hbound
    rw [he,AffineMap.lineMap_apply_module,map_add,map_smul,map_smul,smul_eq_mul,smul_eq_mul] at hbound
    nlinarith [mul_pos (sub_pos.mpr ht) (sub_pos.mpr (hLm.trans hLy))]
  rw [hF,segmentCycle_eq_iUnion_edges] at hyF
  obtain ⟨e,he,hyS⟩ := Set.mem_iUnion₂.mp hyF
  by_contra! h
  have hneg : L y ≤ 0 := (convex_halfSpace_le L.isLinear 0).segment_subset
    (h _ (polygonCycleEdges_mem_fst he)) (h _ (polygonCycleEdges_mem_snd he)) hyS
  exact (not_le_of_gt hLy) hneg

/-- Cut a simple convex polygon by a closed half-space that contains some
strictly positive point. If the cut removes anything, first insert the two
chord endpoints in the boundary list, then keep the arc on the nonnegative side. -/
theorem polygonCut {K : Set Point3} (hK : IsCompact K) (hconv : Convex ℝ K)
    (hd : Module.finrank ℝ (affineSpan ℝ K).direction = 2) (L : Point3 →ₗ[ℝ] ℝ)
    (xs : List Point3) (hF : intrinsicFrontier ℝ K = segmentCycle xs) (hs : SimplePolygon xs)
    (hp : ∃ p ∈ K, 0 < L p)
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] (f : Point3 →ₗ[ℝ] V)
    (hf : ∀ p ∈ K, f p ≠ 0) :
    let C := K ∩ {x | 0 ≤ L x}
    affineSpan ℝ C = affineSpan ℝ K ∧ ∃ ys : List Point3, SimplePolygon ys ∧
      intrinsicFrontier ℝ C = segmentCycle ys ∧ angularCycleLength (ys.map f) ≤ angularCycleLength (xs.map f) := by
  by_cases hno : ∀ p ∈ K, 0 ≤ L p
  · dsimp only
    have hsub : K ⊆ {x | 0 ≤ L x} := fun _ hx => hno _ hx
    rw [inter_eq_left.mpr hsub]
    exact ⟨rfl,xs,hs,hF,le_rfl⟩
  push Not at hno
  have hC := (planarCut_frontier hK.isClosed hconv L hp hno).1
  obtain ⟨a,b,_,_,hends⟩ := planarCut_chord hK hconv hd L hp hno
  have ha : a ∈ intrinsicFrontier ℝ K ∩ {x | L x = 0} := hends.symm ▸ (by simp : a ∈ {a,b})
  have hb : b ∈ intrinsicFrontier ℝ K ∩ {x | L x = 0} := hends.symm ▸ (by simp : b ∈ {a,b})
  have hKf : intrinsicFrontier ℝ K ⊆ K := by
    have he : intrinsicFrontier ℝ K ⊆ closure K :=
      intrinsicFrontier_subset_intrinsicClosure.trans intrinsicClosure_subset_closure
    rwa [hK.isClosed.closure_eq] at he
  obtain ⟨xs₁,hs₁,hv₁,hF₁,hP₁⟩ := hs.insert_boundary_point (hF ▸ ha.1) f (hf a (hKf ha.1))
  obtain ⟨xs₂,hs₂,hv₂,hF₂,hP₂⟩ := hs₁.insert_boundary_point
    (hF₁.symm ▸ (hF ▸ hb.1)) f (hf b (hKf hb.1))
  have hm₁ (x : Point3) (hx : x ∈ xs) : x ∈ xs₁ := (hv₁ x).mpr (Or.inr hx)
  have hm₂ (x : Point3) (hx : x ∈ xs₁) : x ∈ xs₂ := (hv₂ x).mpr (Or.inr hx)
  have hRef (x : Point3) (hx : x ∈ intrinsicFrontier ℝ K) (hL : L x = 0) : x ∈ xs₂ := by
    have h := (show x ∈ intrinsicFrontier ℝ K ∩ {x | L x = 0} from ⟨hx,hL⟩)
    rw [hends] at h
    rcases mem_insert_iff.mp h with he | he
    · exact (hv₂ x).mpr (Or.inr ((hv₁ x).mpr (Or.inl he)))
    · exact (hv₂ x).mpr (Or.inl (mem_singleton_iff.mp he))
  have hp' := exists_positive_vertex hK xs hF L hp hno
  have hm' : ∃ x ∈ xs, L x < 0 := by
    have hpL : ∃ x ∈ K, 0 < (-L) x := by
      obtain ⟨x,hx,h⟩ := hno
      exact ⟨x,hx,neg_pos.mpr h⟩
    have hmL : ∃ x ∈ K, (-L) x < 0 := by
      obtain ⟨x,hx,h⟩ := hp
      exact ⟨x,hx,neg_lt_zero.mpr h⟩
    simpa only [LinearMap.neg_apply,neg_pos] using exists_positive_vertex hK xs hF (-L) hpL hmL
  have hp₂ : ∃ x ∈ xs₂, 0 < L x := by
    obtain ⟨x,hx,h⟩ := hp'
    exact ⟨x,hm₂ x (hm₁ x hx),h⟩
  have hm₂' : ∃ x ∈ xs₂, L x < 0 := by
    obtain ⟨x,hx,h⟩ := hm'
    exact ⟨x,hm₂ x (hm₁ x hx),h⟩
  obtain ⟨ys,hYs,hY,hP⟩ := polygonCut_of_refined_boundary hK hconv hd L xs₂
    (hF.trans (hF₂.trans hF₁).symm) hs₂ hRef hp₂ hm₂' f
  exact ⟨hC,ys,hYs,hY,hP.trans_eq (hP₂.trans hP₁)⟩

/-- Repeatedly clip an enclosing polygon by a list of half-spaces. A retained
set with a strictly positive point for each cut keeps every intermediate body
two-dimensional, so each step preserves the angular perimeter bound. -/
theorem polygonCut_list {T K : Set Point3} (hK : IsCompact K) (hconv : Convex ℝ K)
    (hd : Module.finrank ℝ (affineSpan ℝ K).direction = 2)
    (xs : List Point3) (hF : intrinsicFrontier ℝ K = segmentCycle xs) (hs : SimplePolygon xs)
    (cuts : List (Point3 →ₗ[ℝ] ℝ)) (hT : T ⊆ K)
    (hkeep : ∀ L ∈ cuts, ∀ p ∈ T, 0 ≤ L p)
    (hpos : ∀ L ∈ cuts, ∃ p ∈ T, 0 < L p)
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] (f : Point3 →ₗ[ℝ] V)
    (hf : ∀ p ∈ K, f p ≠ 0) :
    let C := K ∩ ⋂ L ∈ cuts, {x | 0 ≤ L x}
    affineSpan ℝ C = affineSpan ℝ K ∧ ∃ ys : List Point3, SimplePolygon ys ∧
      intrinsicFrontier ℝ C = segmentCycle ys ∧ angularCycleLength (ys.map f) ≤ angularCycleLength (xs.map f) := by
  induction cuts generalizing K xs with
  | nil => simpa using (show affineSpan ℝ K = affineSpan ℝ K ∧
      ∃ ys : List Point3, SimplePolygon ys ∧ intrinsicFrontier ℝ K = segmentCycle ys ∧
        angularCycleLength (ys.map f) ≤ angularCycleLength (xs.map f) from ⟨rfl,xs,hs,hF,le_rfl⟩)
  | cons L cuts ih =>
    let K' := K ∩ {x | 0 ≤ L x}
    have hT' : T ⊆ K' := fun _ hx => ⟨hT hx,hkeep L List.mem_cons_self _ hx⟩
    have hp : ∃ x ∈ K, 0 < L x := by
      obtain ⟨x,hx,hL⟩ := hpos L List.mem_cons_self
      exact ⟨x,hT hx,hL⟩
    obtain ⟨hspan,ys,hys,hY,hangle⟩ := polygonCut hK hconv hd L xs hF hs hp f hf
    have hd' : Module.finrank ℝ (affineSpan ℝ K').direction = 2 := hspan.symm ▸ hd
    have hc' : IsCompact K' := hK.inter_right (isClosed_le continuous_const L.continuous_of_finiteDimensional)
    have hconv' : Convex ℝ K' := hconv.inter (convex_halfSpace_ge L.isLinear 0)
    have he : K' ∩ ⋂ M ∈ cuts, {x | 0 ≤ M x} = K ∩ ⋂ M ∈ L :: cuts, {x | 0 ≤ M x} := by
      ext x
      simp only [K',mem_inter_iff,mem_iInter,mem_ofPred_eq,List.mem_cons]
      constructor
      · rintro ⟨⟨hx,hL⟩,hcut⟩
        exact ⟨hx,fun M hM => hM.elim (fun he => he.symm ▸ hL) (hcut M)⟩
      · rintro ⟨hx,hcut⟩
        exact ⟨⟨hx,hcut L (Or.inl rfl)⟩,fun M hM => hcut M (Or.inr hM)⟩
    obtain ⟨hspan',zs,hzs,hZ,hangle'⟩ := ih hc' hconv' hd' ys hY hys hT'
      (fun M hM => hkeep M (List.mem_cons_of_mem _ hM))
      (fun M hM => hpos M (List.mem_cons_of_mem _ hM))
      (fun x hx => hf x hx.1)
    dsimp only
    rw [← he]
    exact ⟨hspan'.trans hspan,zs,hzs,hZ,hangle'.trans hangle⟩

end OrigamiTorus
