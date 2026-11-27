module

public import OrigamiTorus.Geometry.PlanarPolygonCut
import Mathlib.Data.Sym.Sym2
import Mathlib.Tactic

/-! Invariance of angular perimeter under the choice of a simple boundary list. -/

public section

open Set InnerProductGeometry

namespace OrigamiTorus

private theorem segment_isClosed (a b : Point3) : IsClosed (segment ℝ a b) := by
  rw [← convexHull_pair]
  exact (((finite_singleton b).insert a).isCompact_convexHull ℝ).isClosed

private theorem openSegment_has_midpoint (a b : Point3) : (openSegment ℝ a b).Nonempty :=
  ⟨(1/2 : ℝ) • a + (1/2 : ℝ) • b,1/2,1/2,by norm_num,by norm_num,by norm_num,rfl⟩

private theorem edge_nondegenerate {xs : List Point3} (hs : SimplePolygon xs)
    {e : Point3 × Point3} (he : e ∈ polygonCycleEdges xs) : e.1 ≠ e.2 := by
  intro h
  apply hs.vertex_outside_open_edge e he e.1 (polygonCycleEdges_mem_fst he)
  rwa [left_mem_openSegment_iff]

private theorem isClosed_edge_union (es : List (Point3 × Point3)) :
    IsClosed (⋃ e ∈ es, segment ℝ e.1 e.2) := by
  induction es with
  | nil => simp
  | cons e es ih =>
    have he : (⋃ g ∈ e :: es, segment ℝ g.1 g.2) =
        segment ℝ e.1 e.2 ∪ ⋃ g ∈ es, segment ℝ g.1 g.2 := by
      ext x
      simp only [mem_iUnion,List.mem_cons,mem_union]
      constructor
      · rintro ⟨g,hg | hg,hx⟩
        · exact Or.inl (hg ▸ hx)
        · exact Or.inr ⟨g,hg,hx⟩
      · rintro (hx | ⟨g,hg,hx⟩)
        · exact ⟨e,Or.inl rfl,hx⟩
        · exact ⟨g,Or.inr hg,hx⟩
    rw [he]
    exact (segment_isClosed e.1 e.2).union ih

private theorem edge_exists_of_same_vertices_and_boundary {xs ys : List Point3}
    (hx : SimplePolygon xs) (hy : SimplePolygon ys) (hV : ∀ x, x ∈ xs ↔ x ∈ ys)
    (hB : segmentCycle xs = segmentCycle ys) {e : Point3 × Point3} (he : e ∈ polygonCycleEdges xs) :
    ∃ g ∈ polygonCycleEdges ys, Sym2.mk g.1 g.2 = Sym2.mk e.1 e.2 := by
  classical
  let U := openSegment ℝ e.1 e.2
  have hU : ∀ x ∈ U, x ∉ ys := by
    intro x hx' hy'
    exact hx.vertex_outside_open_edge e he x ((hV x).mpr hy') hx'
  have hsub : U ⊆ segmentCycle ys := by
    intro x hx'
    rw [← hB,segmentCycle_eq_iUnion_edges]
    exact mem_iUnion₂.mpr ⟨e,he,openSegment_subset_segment ℝ _ _ hx'⟩
  obtain ⟨p,hp⟩ := openSegment_has_midpoint e.1 e.2
  have hpb := hsub hp
  rw [segmentCycle_eq_iUnion_edges] at hpb
  obtain ⟨g,hg,hpg⟩ := mem_iUnion₂.mp hpb
  let A := segment ℝ g.1 g.2
  let rest := (polygonCycleEdges ys).filter (· ≠ g)
  let B := ⋃ t ∈ rest, segment ℝ t.1 t.2
  have hAB : U ⊆ A ∪ B := by
    intro x hx'
    have hxb := hsub hx'
    rw [segmentCycle_eq_iUnion_edges] at hxb
    obtain ⟨t,ht,hxt⟩ := mem_iUnion₂.mp hxb
    by_cases htg : t = g
    · subst t
      exact Or.inl hxt
    · exact Or.inr (mem_iUnion₂.mpr ⟨t,List.mem_filter.mpr ⟨ht,by simpa using htg⟩,hxt⟩)
  have hD : ¬ (U ∩ (A ∩ B)).Nonempty := by
    rintro ⟨x,hx',hxA,hxB⟩
    obtain ⟨t,ht,hxt⟩ := mem_iUnion₂.mp hxB
    have hrest := List.mem_filter.mp ht
    have htg : t ≠ g := by simpa using hrest.2
    have hO (t : Point3 × Point3) (ht : t ∈ polygonCycleEdges ys)
        (hs : x ∈ segment ℝ t.1 t.2) : x ∈ openSegment ℝ t.1 t.2 :=
      mem_openSegment_of_ne_left_right
        (fun h => hU x hx' (h ▸ polygonCycleEdges_mem_fst ht))
        (fun h => hU x hx' (h ▸ polygonCycleEdges_mem_snd ht)) hs
    exact disjoint_left.mp (hy.disjoint_open_edges g hg t hrest.1 htg.symm) (hO g hg hxA) (hO t hrest.1 hxt)
  have hUA : U ⊆ A := by
    intro x hx'
    by_contra hxA
    have hconn : IsPreconnected U := (convex_openSegment (𝕜 := ℝ) e.1 e.2).isPreconnected
    apply hD
    exact isPreconnected_closed_iff.mp hconn A B (segment_isClosed g.1 g.2)
      (isClosed_edge_union rest) hAB ⟨p,hp,hpg⟩ ⟨x,hx',(hAB hx').resolve_left hxA⟩
  have hcross : segment ℝ e.1 e.2 ⊆ A := by
    rw [← closure_openSegment]
    exact closure_minimal hUA (segment_isClosed g.1 g.2)
  have hends (x : Point3) (hv : x ∈ xs) (hs : x ∈ segment ℝ e.1 e.2) : x = g.1 ∨ x = g.2 := by
    by_contra! hn
    exact hy.vertex_outside_open_edge g hg x ((hV x).mp hv)
      (mem_openSegment_of_ne_left_right hn.1.symm hn.2.symm (hcross hs))
  have ha := hends e.1 (polygonCycleEdges_mem_fst he) (left_mem_segment ℝ _ _)
  have hb := hends e.2 (polygonCycleEdges_mem_snd he) (right_mem_segment ℝ _ _)
  have hne := edge_nondegenerate hx he
  refine ⟨g,hg,Sym2.eq_iff.mpr ?_⟩
  rcases ha with ha | ha <;> rcases hb with hb | hb
  · exact (hne (ha.trans hb.symm)).elim
  · exact Or.inl ⟨ha.symm,hb.symm⟩
  · exact Or.inr ⟨hb.symm,ha.symm⟩
  · exact (hne (ha.trans hb.symm)).elim

private theorem nodup_unordered_edges {xs : List Point3} (hs : SimplePolygon xs) :
    ((polygonCycleEdges xs).map (fun e => Sym2.mk e.1 e.2)).Nodup := by
  have hn : ((polygonCycleEdges xs).map Prod.fst).Nodup := by simpa [polygonCycleEdges_fst] using hs.nodup
  apply (hn.of_map _).map_on
  intro e he g hg heq
  rcases Sym2.eq_iff.mp heq with ⟨h1,h2⟩ | ⟨h1,h2⟩
  · exact Prod.ext h1 h2
  · by_contra hne
    obtain ⟨x,hx⟩ := openSegment_has_midpoint e.1 e.2
    have hx' : x ∈ openSegment ℝ g.1 g.2 := by
      rw [← h2,← h1,openSegment_symm]
      exact hx
    exact disjoint_left.mp (hs.disjoint_open_edges e he g hg hne) hx hx'

private theorem angularCycleLength_eq_of_same_vertices_and_boundary {xs ys : List Point3}
    (hx : SimplePolygon xs) (hy : SimplePolygon ys) (hV : ∀ x, x ∈ xs ↔ x ∈ ys)
    (hB : segmentCycle xs = segmentCycle ys)
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] (f : Point3 → V) :
    angularCycleLength (xs.map f) = angularCycleLength (ys.map f) := by
  classical
  let side (e : Point3 × Point3) := Sym2.mk e.1 e.2
  let length : Sym2 Point3 → ℝ := Sym2.lift ⟨fun a b => angle (f a) (f b),fun a b => angle_comm _ _⟩
  have hL (a b : Point3) (zs : List Point3) :
      angularPathLength (f a) (zs.map f) (f b) =
        ((polygonPathEdges a zs b).map (length ∘ side)).sum := by
    induction zs generalizing a with
    | nil => simp [angularPathLength,polygonPathEdges,length,side]
    | cons c zs ih => simp [angularPathLength,polygonPathEdges,length,side,ih]
  have hSum (zs : List Point3) : angularCycleLength (zs.map f) =
      (((polygonCycleEdges zs).map side).map length).sum := by
    cases zs with
    | nil => simp [polygonCycleEdges,angularCycleLength]
    | cons a zs => simpa only [List.map_cons,List.map_map,angularCycleLength,polygonCycleEdges] using hL a a zs
  have hP : List.Perm ((polygonCycleEdges xs).map side) ((polygonCycleEdges ys).map side) := by
    apply List.perm_of_nodup_nodup_toFinset_eq (nodup_unordered_edges hx) (nodup_unordered_edges hy)
    ext r
    simp only [List.mem_toFinset]
    constructor
    · intro hr
      obtain ⟨e,he,rfl⟩ := List.mem_map.mp hr
      obtain ⟨g,hg,hr⟩ := edge_exists_of_same_vertices_and_boundary hx hy hV hB he
      exact List.mem_map.mpr ⟨g,hg,hr⟩
    · intro hr
      obtain ⟨e,he,rfl⟩ := List.mem_map.mp hr
      obtain ⟨g,hg,hr⟩ := edge_exists_of_same_vertices_and_boundary hy hx (fun x => (hV x).symm) hB.symm he
      exact List.mem_map.mpr ⟨g,hg,hr⟩
  rw [hSum,hSum]
  exact (hP.map length).sum_eq

private theorem SimplePolygon.insert_boundary_list {xs : List Point3} (hs : SimplePolygon xs)
    (toInsert : List Point3) (hb : ∀ x ∈ toInsert, x ∈ segmentCycle xs)
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] (f : Point3 →ₗ[ℝ] V)
    (hf : ∀ x ∈ toInsert, f x ≠ 0) :
    ∃ zs : List Point3, SimplePolygon zs ∧ (∀ x, x ∈ zs ↔ x ∈ xs ∨ x ∈ toInsert) ∧
      segmentCycle zs = segmentCycle xs ∧ angularCycleLength (zs.map f) = angularCycleLength (xs.map f) := by
  induction toInsert generalizing xs with
  | nil => exact ⟨xs,hs,fun x => by simp,rfl,rfl⟩
  | cons a toInsert ih =>
    obtain ⟨ys,hy,hverts,hY,hP⟩ := hs.insert_boundary_point
      (hb a List.mem_cons_self) f (hf a List.mem_cons_self)
    obtain ⟨zs,hz,hverts',hZ,hP'⟩ := ih hy
      (fun x hx => hY.symm ▸ hb x (List.mem_cons_of_mem _ hx))
      (fun x hx => hf x (List.mem_cons_of_mem _ hx))
    refine ⟨zs,hz,?_,hZ.trans hY,hP'.trans hP⟩
    intro x
    rw [hverts',hverts]
    simp only [List.mem_cons]
    tauto

/-- Simple polygonal lists tracing the same boundary have the same angular
perimeter when the linear map is nonzero along that boundary. -/
theorem angularCycleLength_eq_of_same_simple_boundary {xs ys : List Point3}
    (hx : SimplePolygon xs) (hy : SimplePolygon ys) (hB : segmentCycle xs = segmentCycle ys)
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] (f : Point3 →ₗ[ℝ] V)
    (hf : ∀ x ∈ segmentCycle xs, f x ≠ 0) :
    angularCycleLength (xs.map f) = angularCycleLength (ys.map f) := by
  have hxs (x : Point3) (hx : x ∈ xs) : x ∈ segmentCycle ys := hB ▸ mem_segmentCycle_of_mem hx
  have hys (y : Point3) (hy : y ∈ ys) : y ∈ segmentCycle xs := hB.symm ▸ mem_segmentCycle_of_mem hy
  obtain ⟨xs',hx',hVX,hBX,hPX⟩ := hx.insert_boundary_list ys hys f (fun y hy => hf y (hys y hy))
  obtain ⟨ys',hy',hVY,hBY,hPY⟩ := hy.insert_boundary_list xs hxs f (fun x hx => hf x (mem_segmentCycle_of_mem hx))
  rw [← hPX,← hPY]
  exact angularCycleLength_eq_of_same_vertices_and_boundary hx' hy'
    (fun x => (hVX x).trans (or_comm.trans (hVY x).symm)) (hBX.trans (hB.trans hBY.symm)) f

end OrigamiTorus
