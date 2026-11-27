module

public import OrigamiTorus.EightVertex.Type2.Links
import Mathlib.Tactic

/-! Edge and spherical-path obstructions in an embedded triangular surface. -/

public section

open InnerProductGeometry
open scoped NNReal

namespace OrigamiTorus

open Type2 (Adjacent euclideanPoint euclideanPoint_injective linkDirection)

theorem adjacent_pair_face {fs : List Triangle} {a b : Vertex} (h : Adjacent fs a b) :
    {a,b} ∈ (triangleComplex fs).faces := by
  obtain ⟨_,f,hf,ha,hb⟩ := h
  exact ⟨by simp,f,hf,by simp [Finset.insert_subset_iff, ha, hb]⟩

theorem covered_singleton_face {fs : List Triangle} {a : Vertex}
    (h : ∃ f ∈ fs, a ∈ triangleVertexSet f) : {a} ∈ (triangleComplex fs).faces := by
  obtain ⟨f,hf,ha⟩ := h
  exact ⟨Finset.singleton_nonempty a,f,hf,Finset.singleton_subset_iff.mpr ha⟩

theorem not_mem_edge_of_embedding {fs : List Triangle} (q : Vertex → Point3)
    (h : Function.Injective (evaluateTriangles fs q))
    {v a b : Vertex}
    (hv : ∃ f ∈ fs, v ∈ triangleVertexSet f) (hab : Adjacent fs a b) (hva : v ≠ a) (hvb : v ≠ b) :
    q v ∉ segment ℝ (q a) (q b) := by
  have hd : Disjoint ({v} : Finset Vertex) {a,b} := by simp [hva,hvb]
  have hd := disjoint_vertexHull_of_injective_evaluateTriangles fs q h
    {v} {a,b} (covered_singleton_face hv) (adjacent_pair_face hab) hd
  rw [vertexHull_pair] at hd
  exact Set.disjoint_left.mp hd (subset_convexHull ℝ _ ⟨v,by simp,rfl⟩)

theorem segments_disjoint_of_embedding {fs : List Triangle} (q : Vertex → Point3)
    (h : Function.Injective (evaluateTriangles fs q)) {a b c d : Vertex}
    (hab : Adjacent fs a b) (hcd : Adjacent fs c d)
    (hd : Disjoint ({a,b} : Finset Vertex) {c,d}) :
    Disjoint (segment ℝ (q a) (q b)) (segment ℝ (q c) (q d)) := by
  simpa only [vertexHull_pair] using disjoint_vertexHull_of_injective_evaluateTriangles
    fs q h {a,b} {c,d} (adjacent_pair_face hab) (adjacent_pair_face hcd) hd

private theorem ray_mem_segment {o x y : Point3} {r : ℝ} (h₀ : 0 ≤ r) (h₁ : r ≤ 1)
    (h : x - o = r • (y - o)) : x ∈ segment ℝ o y := by
  refine ⟨1-r,r,sub_nonneg.mpr h₁,h₀,by ring,?_⟩
  calc (1-r) • o + r • y = o + r • (y-o) := by module
    _ = x := by rw [← h]; abel

private theorem diff_eq_of_direction_eq {q : Vertex → Point3} {v a b : Vertex} {r : ℝ}
    (h : linkDirection q v b = r • linkDirection q v a) :
    q b - q v = r • (q a - q v) := by
  apply euclideanPoint_injective
  rw [map_smul]
  exact h

theorem distinct_rays_of_embedding {fs : List Triangle} (q : Vertex → Point3)
    (h : Function.Injective (evaluateTriangles fs q)) {v a b : Vertex}
    (ha : Adjacent fs v a) (hb : Adjacent fs v b) (hne : a ≠ b) :
    angle (linkDirection q v a) (linkDirection q v b) ≠ 0 := by
  intro hz
  obtain ⟨_,r,hr,he⟩ := angle_eq_zero_iff.mp hz
  have hdiff := diff_eq_of_direction_eq he
  rcases le_or_gt r 1 with hle | hlt
  · exact not_mem_edge_of_embedding q h (by obtain ⟨_,f,hf,_,hfmem⟩ := hb; exact ⟨f,hf,hfmem⟩) ha hb.1.symm hne.symm (ray_mem_segment hr.le hle hdiff)
  · have he' : q a - q v = r⁻¹ • (q b - q v) := by
      rw [hdiff, smul_smul, inv_mul_cancel₀ hr.ne', one_smul]
    exact not_mem_edge_of_embedding q h (by obtain ⟨_,f,hf,_,hfmem⟩ := ha; exact ⟨f,hf,hfmem⟩) hb ha.1.symm hne
      (ray_mem_segment (inv_nonneg.mpr hr.le) (inv_le_one_of_one_le₀ hlt.le) he')

theorem no_edge_of_opposite_rays_of_embedding {fs : List Triangle} (q : Vertex → Point3)
    (h : Function.Injective (evaluateTriangles fs q)) {v a b : Vertex}
    (ha : Adjacent fs v a) (hb : Adjacent fs v b)
    (hop : angle (linkDirection q v a) (linkDirection q v b) = Real.pi) :
    ¬ Adjacent fs a b := by
  intro hab
  obtain ⟨_,r,hr,he⟩ := angle_eq_pi_iff.mp hop
  have hdiff := diff_eq_of_direction_eq he
  let t := (1-r)⁻¹
  have hden : 0 < 1-r := by linarith
  have hone : (-r)*t + t = 1 := by
    calc (-r)*t+t = (1-r)*t := by ring
      _ = 1 := mul_inv_cancel₀ hden.ne'
  have hseg : q v ∈ segment ℝ (q a) (q b) := by
    refine ⟨(-r)*t,t,mul_nonneg (neg_nonneg.mpr hr.le) (inv_nonneg.mpr hden.le),
      inv_nonneg.mpr hden.le,hone,?_⟩
    calc (-r*t) • q a + t • q b =
        t • ((q b-q v) - r • (q a-q v)) + (-r*t+t) • q v := by module
      _ = q v := by rw [hdiff, sub_self, smul_zero, hone, one_smul, zero_add]
  have hv : ∃ f ∈ fs, v ∈ triangleVertexSet f := by
    obtain ⟨_,f,hf,hv,_⟩ := ha
    exact ⟨f,hf,hv⟩
  exact not_mem_edge_of_embedding q h hv hab ha.1 hb.1 hseg

private theorem coefficient_sum_lt_one {o x a y : Point3} {s t : ℝ}
    (hs : 0 ≤ s) (ht : 0 ≤ t) (hx : x-o = s • (a-o) + t • (y-o))
    (hd : Disjoint (segment ℝ o x) (segment ℝ a y)) : s+t < 1 := by
  by_contra! h
  let r := (s+t)⁻¹
  have hr : 0 ≤ r := inv_nonneg.mpr ((by norm_num : (0 : ℝ) ≤ 1).trans h)
  have he : r*(s+t) = 1 := inv_mul_cancel₀ ((by norm_num : (0 : ℝ) < 1).trans_le h).ne'
  let p := o + r • (x-o)
  have hp : p ∈ segment ℝ o x := ray_mem_segment hr (inv_le_one_of_one_le₀ h) (by dsimp [p]; abel)
  have hq : p ∈ segment ℝ a y := by
    refine ⟨r*s,r*t,mul_nonneg hr hs,mul_nonneg hr ht,by rwa [← mul_add],?_⟩
    calc (r*s) • a + (r*t) • y =
        (r*(s+t)) • o + r • (s • (a-o) + t • (y-o)) := by module
      _ = p := by rw [he, one_smul, ← hx]
  exact Set.disjoint_left.mp hd hp hq

private theorem linkDirection_ne_zero_of_adjacent {fs : List Triangle} (q : Vertex → Point3)
    (h : Function.Injective (evaluateTriangles fs q)) {v x : Vertex} (hx : Adjacent fs v x) :
    linkDirection q v x ≠ 0 := by
  intro he
  have hq : q x = q v := sub_eq_zero.mp (euclideanPoint_injective (he.trans euclideanPoint.map_zero.symm))
  obtain ⟨hn,f,hf,hv,hx⟩ := hx
  have hd := disjoint_vertexHull_of_injective_evaluateTriangles fs q h {v} {x}
    (covered_singleton_face ⟨f,hf,hv⟩) (covered_singleton_face ⟨f,hf,hx⟩) (Finset.disjoint_singleton.mpr hn)
  exact Set.disjoint_left.mp hd (subset_convexHull ℝ _ ⟨v,by simp,rfl⟩)
    (subset_convexHull ℝ _ ⟨x,by simp,hq⟩)

/-- The two cone conditions within one semicircle force intersecting edges if
the intermediate rays are distinct from the endpoint line. -/
private theorem semicircle_edge_obstruction {fs : List Triangle} (q : Vertex → Point3)
    (h : Function.Injective (evaluateTriangles fs q)) {v a x y b : Vertex}
    (hlabels : [a,x,y,b].Nodup) (hmem : ∀ z ∈ [a,x,y,b], Adjacent fs v z)
    (hay : Adjacent fs a y) (hxb : Adjacent fs x b)
    (hop : angle (linkDirection q v a) (linkDirection q v b) = Real.pi)
    (hx : linkDirection q v x ∈ Submodule.span ℝ≥0 {linkDirection q v a,linkDirection q v y})
    (hy : linkDirection q v y ∈ Submodule.span ℝ≥0 {linkDirection q v x,linkDirection q v b}) :
    False := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, and_true,
    List.nodup_nil] at hlabels
  obtain ⟨⟨hax,hay',hab⟩,⟨hxy,hxb'⟩,hyb⟩ := hlabels
  have hva := hmem a (by simp)
  have hvx := hmem x (by simp)
  have hvy := hmem y (by simp)
  have hvb := hmem b (by simp)
  obtain ⟨p,r,hx⟩ := Submodule.mem_span_pair.mp hx
  obtain ⟨s,t,hy⟩ := Submodule.mem_span_pair.mp hy
  obtain ⟨ha,k,hk,hb⟩ := angle_eq_pi_iff.mp hop
  have hb' := diff_eq_of_direction_eq hb
  have hx' : q x-q v = (p : ℝ) • (q a-q v) + (r : ℝ) • (q y-q v) := by
    apply euclideanPoint_injective
    simpa only [map_add, map_smul, linkDirection, NNReal.smul_def] using hx.symm
  have hy' : q y-q v = (s : ℝ) • (q x-q v) + (t : ℝ) • (q b-q v) := by
    apply euclideanPoint_injective
    simpa only [map_add, map_smul, linkDirection, NNReal.smul_def] using hy.symm
  have h₁ := coefficient_sum_lt_one p.coe_nonneg r.coe_nonneg hx'
    (segments_disjoint_of_embedding q h hvx hay (by
      simp [Finset.disjoint_left, hva.1, hvy.1, Ne.symm hax, hxy]))
  have h₂ := coefficient_sum_lt_one s.coe_nonneg t.coe_nonneg hy'
    (segments_disjoint_of_embedding q h hvy hxb (by
      simp [Finset.disjoint_left, hvx.1, hvb.1, Ne.symm hxy, hyb.1]))
  have hr : (r : ℝ) < 1 := by linarith [p.coe_nonneg]
  have hs : (s : ℝ) ≤ 1 := by linarith [t.coe_nonneg]
  have hrs : (r : ℝ)*s < 1 := (mul_le_of_le_one_right r.coe_nonneg hs).trans_lt hr
  let A := q a-q v
  let X := q x-q v
  let Y := q y-q v
  let B := q b-q v
  let c : ℝ := p + r*t*k
  have hsub : X = c • A + ((r : ℝ)*s) • X := by
    calc X = (p : ℝ) • A + (r : ℝ) • Y := hx'
      _ = (p : ℝ) • A + (r : ℝ) • ((s : ℝ) • X + (t : ℝ) • B) := by rw [show Y = _ from hy']
      _ = _ := by rw [show B = k • A from hb']; dsimp only [c]; module
  have hscale : (1-(r : ℝ)*s) • X = c • A := by
    have he := congrArg (· - ((r : ℝ)*s) • X) hsub
    rw [add_sub_cancel_right] at he
    calc (1-(r : ℝ)*s) • X = X - ((r : ℝ)*s) • X := by module
      _ = _ := he
  have he : X = ((1-(r : ℝ)*s)⁻¹*c) • A := by
    have hf := congrArg ((1-(r : ℝ)*s)⁻¹ • ·) hscale
    rwa [smul_smul, inv_mul_cancel₀ (sub_pos.mpr hrs).ne', one_smul, smul_smul] at hf
  let k' : ℝ := (1-(r : ℝ)*s)⁻¹*c
  have hdir : linkDirection q v x = k' • linkDirection q v a := by
    change euclideanPoint X = k' • euclideanPoint A
    rw [he, map_smul]
  rcases lt_trichotomy k' 0 with hn | hz | hp
  · have hxπ := angle_eq_pi_iff.mpr ⟨ha,k',hn,hdir⟩
    have hs := angle_add_angle_eq_pi_of_angle_eq_pi (linkDirection q v x) hop
    have hz : angle (linkDirection q v b) (linkDirection q v x) = 0 := by linarith
    exact distinct_rays_of_embedding q h (hmem b (by simp)) (hmem x (by simp)) (Ne.symm hxb') hz
  · have hzero : linkDirection q v x = 0 := by rw [hdir,hz,zero_smul]
    exact linkDirection_ne_zero_of_adjacent q h hvx hzero
  · exact distinct_rays_of_embedding q h (hmem a (by simp)) (hmem x (by simp)) hax
      (angle_eq_zero_iff.mpr ⟨ha,k',hp,hdir⟩)

theorem impossible_minimal_arc_of_embedding {fs : List Triangle} (q : Vertex → Point3)
    (h : Function.Injective (evaluateTriangles fs q)) {v a b x y : Vertex}
    {xs : List Vertex} (hnd : [a,x,y,b].Nodup)
    (hm : ∀ z ∈ [a,x,y,b], Adjacent fs v z)
    (horder : [x,y].Sublist xs) (hay : Adjacent fs a y) (hxb : Adjacent fs x b)
    (hop : angle (linkDirection q v a) (linkDirection q v b) = Real.pi)
    (hmin : angularPathLength (linkDirection q v a) (xs.map (linkDirection q v)) (linkDirection q v b) = Real.pi) :
    False := by
  have hby : b ≠ y := by
    have he := hnd.sublist (show [y,b].Sublist [a,x,y,b] from (List.Sublist.refl _).cons x |>.cons a)
    exact Ne.symm (by simpa using he : y ≠ b)
  have hax : a ≠ x := by
    have he := hnd.sublist (List.sublist_append_left [a,x] [y,b])
    simpa using he
  let d := linkDirection q v
  have haY : angle (d a) (d y) ≠ Real.pi := by
    intro hey
    apply distinct_rays_of_embedding q h (hm b (by simp)) (hm y (by simp)) hby
    have he := angle_add_angle_eq_pi_of_angle_eq_pi (d y) hop
    linarith
  have hxB : angle (d x) (d b) ≠ Real.pi := by
    intro hex
    apply distinct_rays_of_embedding q h (hm a (by simp)) (hm x (by simp)) hax
    have he := angle_add_angle_eq_pi_of_angle_eq_pi (d x) hop
    rw [angle_comm (d b) (d x)] at he
    linarith
  have ⟨hx,hy⟩ := mem_cones_of_ordered_semicircle (d a) (d x) (d y) (d b) (xs.map d) hop hmin
    (horder.map d) (linkDirection_ne_zero_of_adjacent q h (hm x (by simp)))
    (linkDirection_ne_zero_of_adjacent q h (hm y (by simp))) haY hxB
  exact semicircle_edge_obstruction q h hnd hm hay hxb hop hx hy

end OrigamiTorus
