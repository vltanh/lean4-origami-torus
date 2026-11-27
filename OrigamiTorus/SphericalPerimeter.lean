module

public import Mathlib.Geometry.Euclidean.Angle.Unoriented.TriangleInequality
import Mathlib.Tactic

/-! Angular lengths and equality cases used in the Type 2 geometric reduction. -/

public section

open InnerProductGeometry
open scoped NNReal

namespace OrigamiTorus

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- Angular length along successive shorter great-circle arcs. -/
@[expose] noncomputable def angularPathLength (a : V) (interior : List V) (b : V) : ℝ :=
  match interior with
  | [] => angle a b
  | c :: cs => angle a c + angularPathLength c cs b

theorem angularPathLength_append (a b c : V) (xs ys : List V) :
    angularPathLength a (xs ++ b :: ys) c =
      angularPathLength a xs b + angularPathLength b ys c := by
  induction xs generalizing a with
  | nil => rfl
  | cons x xs ih => simp [angularPathLength, ih, add_assoc]

/-- Replacing a chain by one spherical arc can only decrease its length. -/
theorem angle_le_angularPathLength (a b : V) (xs : List V) :
    angle a b ≤ angularPathLength a xs b := by
  induction xs generalizing a with
  | nil => exact le_rfl
  | cons c cs ih =>
    exact (angle_le_angle_add_angle a c b).trans (add_le_add le_rfl (ih c))

private theorem angularPathLength_insert_first (a b c : V) (xs : List V) :
    angularPathLength a xs c ≤ angle a b + angularPathLength b xs c := by
  cases xs with
  | nil => exact angle_le_angle_add_angle a b c
  | cons x xs =>
    simpa only [angularPathLength, add_assoc] using
      add_le_add (angle_le_angle_add_angle a b x) (le_refl (angularPathLength x xs c))

/-- Deleting intermediate directions cannot increase the angular length. -/
theorem angularPathLength_mono (a b : V) {xs ys : List V} (h : xs.Sublist ys) :
    angularPathLength a xs b ≤ angularPathLength a ys b := by
  induction h generalizing a with
  | slnil => exact le_rfl
  | cons x _ ih =>
    exact (ih a).trans (angularPathLength_insert_first a x b _)
  | cons_cons x _ ih => exact add_le_add le_rfl (ih x)

/-- Perimeter of the cyclic list, closing its last arc at its first point. -/
@[expose] noncomputable def angularCycleLength (xs : List V) : ℝ :=
  match xs with
  | [] => 0
  | a :: ys => angularPathLength a ys a

theorem angularCycleLength_mono {xs ys : List V} (h : xs.Sublist ys) :
    angularCycleLength xs ≤ angularCycleLength ys := by
  induction h with
  | slnil => exact le_rfl
  | @cons xs ys a h ih =>
    apply ih.trans
    cases ys with
    | nil => exact angle_nonneg _ _
    | cons b ys =>
      have hs : ys.Sublist (ys ++ [a]) := List.sublist_append_left ys [a]
      have he := angularPathLength_mono b b hs
      rw [angularPathLength_append] at he
      simpa only [angularCycleLength, angularPathLength, add_comm] using he
  | cons_cons a h _ => exact angularPathLength_mono a a h

theorem angularCycleLength_eq_sum_zip (xs : List V) :
    angularCycleLength xs = ((xs.zip (xs.drop 1 ++ xs.take 1)).map fun (a,b) => angle a b).sum := by
  have hp (a b : V) (zs : List V) :
      angularPathLength a zs b = (((a :: zs).zip (zs ++ [b])).map fun (x,y) => angle x y).sum := by
    induction zs generalizing a with
    | nil => simp [angularPathLength]
    | cons x zs ih => simp [angularPathLength, ih]
  cases xs with
  | nil => rfl
  | cons a xs => simpa [angularCycleLength] using hp a a xs

theorem angularCycleLength_four (a b c d : V) :
    angularCycleLength [a,b,c,d] = angle a b + angle b c + angle c d + angle d a := by
  simp [angularCycleLength, angularPathLength, add_assoc]

private theorem angularCycleLength_move_head (a : V) (xs : List V) :
    angularCycleLength (a :: xs) = angularCycleLength (xs ++ [a]) := by
  cases xs with
  | nil => rfl
  | cons b bs =>
    change angle a b + angularPathLength b bs a = angularPathLength b (bs ++ [a]) b
    rw [angularPathLength_append]
    exact add_comm _ _

theorem angularCycleLength_append_comm (xs ys : List V) :
    angularCycleLength (xs ++ ys) = angularCycleLength (ys ++ xs) := by
  induction xs generalizing ys with
  | nil => simp
  | cons x xs ih =>
    rw [List.cons_append, angularCycleLength_move_head, List.append_assoc, ih]
    simp only [List.append_assoc, List.singleton_append]

theorem angularCycleLength_split_pair (a b : V) (xs ys : List V) :
    angularCycleLength (a :: (xs ++ b :: ys)) =
      angularPathLength a xs b + angularPathLength b ys a :=
  angularPathLength_append a b a xs ys

theorem angularCycleLength_split_triple (a b c : V) (xs ys zs : List V) :
    angularCycleLength (a :: (xs ++ b :: (ys ++ c :: zs))) =
      angularPathLength a xs b + angularPathLength b ys c + angularPathLength c zs a := by
  rw [angularCycleLength_split_pair, angularPathLength_append, add_assoc]

/-- Subdividing an edge at a point of its positive cone leaves the angular
perimeter unchanged. The lists may be empty, including at the ends of a cycle. -/
theorem angularCycleLength_subdivide (a b p : V) (xs ys : List V) (hp : p ≠ 0)
    (hab : p ∈ Submodule.span ℝ≥0 {a,b}) :
    angularCycleLength (xs ++ a :: p :: b :: ys) = angularCycleLength (xs ++ a :: b :: ys) := by
  have h := (angle_eq_angle_add_angle_iff (x := a) (z := b) hp).mpr (Or.inr hab)
  rw [angularCycleLength_append_comm xs, angularCycleLength_append_comm xs]
  change angle a p + (angle p b + angularPathLength b (ys ++ xs) a) =
    angle a b + angularPathLength b (ys ++ xs) a
  rw [h,add_assoc]

/-- A segment in a plane of height one has the same angular length after
any ordered finite subdivision. -/
theorem angularPathLength_eq_angle_of_ordered_segment (l : V →ₗ[ℝ] ℝ) (a b : V)
    (ha : l a = 1) (hb : l b = 1) (s t : ℝ) (xs : List ℝ)
    (hxs : (s :: (xs ++ [t])).Pairwise (· ≤ ·)) :
    let p := AffineMap.lineMap a b
    angularPathLength (p s) (xs.map p) (p t) = angle (p s) (p t) := by
  let p : ℝ →ᵃ[ℝ] V := AffineMap.lineMap a b
  have hpoint (u : ℝ) : p u ≠ 0 := by
    have H : l (p u) = 1 := by
      change l (AffineMap.lineMap a b u) = 1
      rw [AffineMap.lineMap_apply_module, map_add, map_smul, map_smul, ha,hb]
      simp
    intro he
    rw [he,map_zero] at H
    norm_num at H
  have hcone {s u t : ℝ} (hs : s ≤ u) (hu : u ≤ t) :
      p u ∈ Submodule.span ℝ≥0 {p s,p t} := by
    rcases lt_or_eq_of_le (hs.trans hu) with hst | he
    · let k := (u-s)/(t-s)
      have hk : 0 ≤ k := div_nonneg (sub_nonneg.mpr hs) (sub_pos.mpr hst).le
      have hk₁ : k ≤ 1 := (div_le_one (sub_pos.mpr hst)).mpr (by linarith)
      refine Submodule.mem_span_pair.mpr ⟨⟨1-k,sub_nonneg.mpr hk₁⟩,⟨k,hk⟩,?_⟩
      have heq : (1-k)*s+k*t = u := by dsimp [k]; field_simp; ring
      change (1-k) • (p s) + k • (p t) = p u
      calc
        _ = p ((1-k)*s+k*t) := by simp only [p,AffineMap.lineMap_apply_module]; module
        _ = p u := by rw [heq]
    · have he' : u = s := le_antisymm (he ▸ hu) hs
      rw [he']
      exact Submodule.subset_span (by simp)
  change angularPathLength (p s) (xs.map p) (p t) = angle (p s) (p t)
  induction xs generalizing s with
  | nil => rfl
  | cons u us ih =>
    have hsu : s ≤ u := (List.pairwise_cons.mp hxs).1 u (by simp)
    have hu' : (u :: (us ++ [t])).Pairwise (· ≤ ·) := (List.pairwise_cons.mp hxs).2
    have hut : u ≤ t := (List.pairwise_cons.mp hu').1 t (by simp)
    change angle (p s) (p u) + angularPathLength (p u) (us.map p) (p t) = _
    rw [ih u hu']
    exact ((angle_eq_angle_add_angle_iff (hpoint u)).mpr (Or.inr (hcone hsu hut))).symm

/-- A straight cut between two edge points shortens the angular perimeter
when it replaces the path on the other side of the cut. -/
theorem angularCycleLength_clip (a b c d p q : V) (xs ys : List V)
    (hp : p ≠ 0) (hq : q ≠ 0)
    (hab : p ∈ Submodule.span ℝ≥0 {a,b}) (hcd : q ∈ Submodule.span ℝ≥0 {c,d}) :
    angularCycleLength (p :: b :: (xs ++ [c,q])) ≤
      angularCycleLength (a :: b :: (xs ++ c :: d :: ys)) := by
  have hab' := (angle_eq_angle_add_angle_iff (x := a) (z := b) hp).mpr (Or.inr hab)
  have hcd' := (angle_eq_angle_add_angle_iff (x := c) (z := d) hq).mpr (Or.inr hcd)
  have hpath := angle_le_angularPathLength q p ((d :: ys) ++ [a])
  rw [angularPathLength_append q a p (d :: ys) []] at hpath
  change angle q p ≤ angle q d + angularPathLength d ys a + angle a p at hpath
  have hbefore : angularCycleLength (a :: b :: (xs ++ c :: d :: ys)) =
      angle a b + (angularPathLength b xs c + (angle c d + angularPathLength d ys a)) := by
    change angle a b + angularPathLength b (xs ++ c :: d :: ys) a = _
    rw [angularPathLength_append]
    rfl
  have hafter : angularCycleLength (p :: b :: (xs ++ [c,q])) =
      angle p b + (angularPathLength b xs c + (angle c q + angle q p)) := by
    change angle p b + angularPathLength b (xs ++ c :: [q]) p = _
    rw [angularPathLength_append]
    rfl
  rw [hbefore,hafter,hab',hcd']
  linarith

/-- At equality along a nonantipodal arc, each nonzero intermediate vector
is in the positive cone of its two endpoints. -/
theorem mem_span_of_angularPathLength_eq (a b : V) (xs : List V)
    (h : angularPathLength a xs b = angle a b) (hab : angle a b ≠ Real.pi)
    {x : V} (hx : x ∈ xs) (hx₀ : x ≠ 0) : x ∈ Submodule.span ℝ≥0 {a,b} := by
  obtain ⟨ys,zs,rfl⟩ := List.append_of_mem hx
  rw [angularPathLength_append] at h
  have he : angle a b = angle a x + angle x b := by
    have hleft := angle_le_angularPathLength a x ys
    have hright := angle_le_angularPathLength x b zs
    linarith [angle_le_angle_add_angle a x b]
  exact ((angle_eq_angle_add_angle_iff hx₀).mp he).resolve_left hab

/-- In order on a minimizing semicircle, the two intermediate directions lie
in the positive cones of the adjacent endpoint and the other direction. -/
theorem mem_cones_of_ordered_semicircle (a x y b : V) (xs : List V)
    (hab : angle a b = Real.pi) (hmin : angularPathLength a xs b = Real.pi)
    (horder : [x,y].Sublist xs) (hx : x ≠ 0) (hy : y ≠ 0)
    (hay : angle a y ≠ Real.pi) (hxb : angle x b ≠ Real.pi) :
    x ∈ Submodule.span ℝ≥0 {a,y} ∧ y ∈ Submodule.span ℝ≥0 {x,b} := by
  have hshort := angularPathLength_mono a b horder
  rw [hmin] at hshort
  change angle a x + (angle x y + angle y b) ≤ Real.pi at hshort
  have hyπ := angle_add_angle_eq_pi_of_angle_eq_pi y hab
  have hxπ := angle_add_angle_eq_pi_of_angle_eq_pi x hab
  rw [angle_comm b y] at hyπ
  rw [angle_comm b x] at hxπ
  have hy_eq : angle a y = angle a x + angle x y := by
    linarith [angle_le_angle_add_angle a x y]
  have hx_eq : angle x b = angle x y + angle y b := by
    linarith [angle_le_angle_add_angle x y b]
  exact ⟨((angle_eq_angle_add_angle_iff hx).mp hy_eq).resolve_left hay,
    ((angle_eq_angle_add_angle_iff hy).mp hx_eq).resolve_left hxb⟩

/-- The angular perimeter for three vectors in a strictly positive relation is `2π`. -/
theorem triangle_perimeter_eq_of_positive_relation (a b c : V) (hc : c ≠ 0)
    (α β γ : ℝ) (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ)
    (hs : α • a + β • b + γ • c = 0) :
    angle a b + angle b c + angle c a = 2 * Real.pi := by
  have hsum : α • a + β • b = -(γ • c) := eq_neg_iff_add_eq_zero.mpr hs
  have he : (α/γ) • a + (β/γ) • b = -c := by
    calc
      _ = γ⁻¹ • (α • a + β • b) := by simp only [smul_add, smul_smul, div_eq_inv_mul]
      _ = -c := by rw [hsum, smul_neg, smul_smul, inv_mul_cancel₀ hγ.ne', one_smul]
  have hcone : -c ∈ Submodule.span ℝ≥0 {a,b} :=
    Submodule.mem_span_pair.mpr ⟨⟨α/γ,div_nonneg hα.le hγ.le⟩,⟨β/γ,div_nonneg hβ.le hγ.le⟩,he⟩
  have hab : angle a b = angle a (-c) + angle (-c) b :=
    (angle_eq_angle_add_angle_iff (neg_ne_zero.mpr hc)).mpr (Or.inr hcone)
  rw [angle_neg_left, angle_neg_right, angle_comm c b, angle_comm a c] at hab
  linarith

/-- A spherical triangle in a strict hemisphere has perimeter less than one great circle. -/
theorem triangle_perimeter_lt_two_pi (l : V →ₗ[ℝ] ℝ) (a b c : V)
    (ha : 0 < l a) (hb : 0 < l b) (hc : 0 < l c) :
    angle a b + angle b c + angle c a < 2 * Real.pi := by
  have hna : -a ≠ 0 := by
    intro h
    have h' := congrArg l h
    simp at h'
    linarith
  have hp : angle b c ≠ Real.pi := by
    intro h
    obtain ⟨_, s, hs, rfl⟩ := angle_eq_pi_iff.mp h
    rw [map_smul, smul_eq_mul] at hc
    exact (not_lt_of_ge (mul_nonpos_of_nonpos_of_nonneg hs.le hb.le)) hc
  have hspan : -a ∉ Submodule.span ℝ≥0 {b,c} := by
    intro h
    obtain ⟨s,t,he⟩ := Submodule.mem_span_pair.mp h
    have he' := congrArg l he
    simp only [NNReal.smul_def, map_add, map_smul, smul_eq_mul, map_neg] at he'
    linarith [mul_nonneg s.coe_nonneg hb.le, mul_nonneg t.coe_nonneg hc.le]
  have ht : angle b c < angle b (-a) + angle (-a) c := by
    apply lt_of_le_of_ne (angle_le_angle_add_angle _ _ _)
    intro h
    rcases (angle_eq_angle_add_angle_iff hna).mp h with h | h
    · exact hp h
    · exact hspan h
  rw [angle_neg_right, angle_neg_left, angle_comm b a, angle_comm a c] at ht
  linarith

/-- If opposite sides of a spherical quadrilateral contain antipodal points and the
first intervening path bends strictly, its perimeter exceeds one great circle. -/
theorem quadrilateral_perimeter_gt_two_pi (a b c d r : V) (hb : b ≠ 0)
    (hbr : angle r c ≠ Real.pi) (hout : b ∉ Submodule.span ℝ≥0 {r,c})
    (hab : angle a b = angle a r + angle r b)
    (hcd : angle c d = angle c (-r) + angle (-r) d) :
    2 * Real.pi < angle a b + angle b c + angle c d + angle d a := by
  have h₁ : angle r c < angle r b + angle b c := by
    apply lt_of_le_of_ne (angle_le_angle_add_angle _ _ _)
    intro h
    rcases (angle_eq_angle_add_angle_iff hb).mp h with h | h
    · exact hbr h
    · exact hout h
  have h₂ := angle_le_angle_add_angle (-r) d a
  rw [angle_neg_left, angle_comm r a] at h₂
  rw [hab, hcd, angle_neg_right, angle_comm c r]
  linarith

/-- Four directions with a positive dependence and three independent members
have perimeter greater than one great circle in the specified cyclic order. -/
theorem quadrilateral_perimeter_gt_of_positive_relation (a b c d : V)
    (α β γ δ : ℝ) (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ) (hδ : 0 < δ)
    (hs : α • a + β • b + γ • c + δ • d = 0)
    (hi : LinearIndependent ℝ (![a,b,c] : Fin 3 → V)) :
    2 * Real.pi < angle a b + angle b c + angle c d + angle d a := by
  have independent (x y z : ℝ) (h : x • a + y • b + z • c = 0) : x = 0 ∧ y = 0 ∧ z = 0 := by
    have hz := Fintype.linearIndependent_iff.mp hi ![x,y,z] (by
      simpa [Fin.sum_univ_succ, add_assoc] using h)
    exact ⟨hz 0,hz 1,hz 2⟩
  let r := α • a + β • b
  have hr : r ≠ 0 := by
    intro he
    exact hα.ne' (independent α β 0 (by simpa [r] using he)).1
  have hbr : angle r c ≠ Real.pi := by
    intro h
    obtain ⟨_,s,_,he⟩ := angle_eq_pi_iff.mp h
    have hz : (s*α) • a + (s*β) • b + (-1 : ℝ) • c = 0 := by
      calc
        _ = s • r - c := by dsimp only [r]; module
        _ = 0 := sub_eq_zero.mpr he.symm
    exact (neg_ne_zero.mpr one_ne_zero) (independent _ _ _ hz).2.2
  have hout : b ∉ Submodule.span ℝ≥0 {r,c} := by
    intro h
    obtain ⟨s,t,he⟩ := Submodule.mem_span_pair.mp h
    have hz : ((s : ℝ)*α) • a + ((s : ℝ)*β-1) • b + (t : ℝ) • c = 0 := by
      calc
        _ = (s : ℝ) • r + (t : ℝ) • c - b := by dsimp only [r]; module
        _ = 0 := sub_eq_zero.mpr he
    obtain ⟨he₁,he₂,_⟩ := independent _ _ _ hz
    have hs₀ : (s : ℝ) = 0 := (mul_eq_zero.mp he₁).resolve_right hα.ne'
    simp [hs₀] at he₂
  have hab : angle a b = angle a r + angle r b :=
    (angle_eq_angle_add_angle_iff hr).mpr (Or.inr (Submodule.mem_span_pair.mpr
      ⟨⟨α,hα.le⟩,⟨β,hβ.le⟩,rfl⟩))
  have hcd : angle c d = angle c (-r) + angle (-r) d := by
    apply (angle_eq_angle_add_angle_iff (neg_ne_zero.mpr hr)).mpr
    refine Or.inr (Submodule.mem_span_pair.mpr ⟨⟨γ,hγ.le⟩,⟨δ,hδ.le⟩,?_⟩)
    change γ • c + δ • d = -r
    apply eq_neg_iff_add_eq_zero.mpr
    simpa [r, add_assoc, add_comm, add_left_comm] using hs
  exact quadrilateral_perimeter_gt_two_pi a b c d r (hi.ne_zero 1) hbr hout hab hcd

end OrigamiTorus
