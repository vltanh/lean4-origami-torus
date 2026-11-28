module

public import OrigamiTorus.EightVertex.Type5.Reconstruction
public import OrigamiTorus.Geometry.TriangleIntersections
import Mathlib.Tactic

/-! Closed embeddings from separating planes through three labeled vertices. -/

@[expose] public section

namespace OrigamiTorus.Type5

/-- The oriented volume determinant on four labeled vertices. -/
def bracket (r : Vertex → Point3) (a b c d : Vertex) : ℝ :=
  affineBracket (r a) (r b) (r c) (r d)

namespace bracket

theorem swapFirst (r : Vertex → Point3) (a b c d : Vertex) (_ : b < a) :
    bracket r a b c d = -bracket r b a c d := by
  simp only [bracket, affineBracket, determinant3, Prod.fst_sub, Prod.snd_sub]
  ring

theorem swapMiddle (r : Vertex → Point3) (a b c d : Vertex) (_ : c < b) :
    bracket r a b c d = -bracket r a c b d := by
  simp only [bracket, affineBracket, determinant3, Prod.fst_sub, Prod.snd_sub]
  ring

theorem swapLast (r : Vertex → Point3) (a b c d : Vertex) (_ : d < c) :
    bracket r a b c d = -bracket r a b d c := by
  simp only [bracket, affineBracket, determinant3, Prod.fst_sub, Prod.snd_sub]
  ring

theorem plucker (r : Vertex → Point3) (u v a b c d : Vertex) :
    bracket r u v a b * bracket r u v c d - bracket r u v a c * bracket r u v b d +
      bracket r u v a d * bracket r u v b c = 0 :=
  affineBracket_plucker (r u) (r v) (r a) (r b) (r c) (r d)

end bracket

/-- A separating plane through three labels, with each other label assigned to its
strict side. A fourth vertex witnesses affine independence of the three plane points. -/
def BracketPlane (r : Vertex → Point3) (s t : Finset Vertex) : Prop :=
  ∃ a b c d : Vertex, affineBracket (r a) (r b) (r c) (r d) ≠ 0 ∧
    (∀ i ∈ s, i ∈ ({a,b,c} : Finset Vertex) ∨ 0 < affineBracket (r a) (r b) (r c) (r i)) ∧
    (∀ i ∈ t, i ∈ ({a,b,c} : Finset Vertex) ∨ affineBracket (r a) (r b) (r c) (r i) < 0)

theorem BracketPlane.mono {r : Vertex → Point3} {s t S T : Finset Vertex}
    (h : BracketPlane r S T) (hs : s ⊆ S) (ht : t ⊆ T) : BracketPlane r s t := by
  obtain ⟨a,b,c,d,hn,hp,hm⟩ := h
  exact ⟨a,b,c,d,hn,fun i hi => hp i (hs hi),fun i hi => hm i (ht hi)⟩

theorem BracketPlane.symm {r : Vertex → Point3} {s t : Finset Vertex}
    (h : BracketPlane r s t) : BracketPlane r t s := by
  obtain ⟨a,b,c,d,hn,hs,ht⟩ := h
  have swap (i : Vertex) : affineBracket (r b) (r a) (r c) (r i) =
      -affineBracket (r a) (r b) (r c) (r i) := by
    simp only [affineBracket,determinant3,Prod.fst_sub,Prod.snd_sub]; ring
  refine ⟨b,a,c,d,by simpa [swap] using hn,?_,?_⟩
  · intro i hi
    simpa only [swap,neg_pos,Finset.insert_comm b a] using ht i hi
  · intro i hi
    simpa only [swap,neg_neg_iff_pos,Finset.insert_comm b a] using hs i hi

private noncomputable def bracketFunctional (a b c : Point3) : Point3 →ᵃ[ℝ] ℝ where
  toFun x := affineBracket a b c x
  linear := {
    toFun := fun v => determinant3 (b-a) (c-a) v
    map_add' := by intro u v; simp [determinant3]; ring
    map_smul' := by intro k v; simp [determinant3]; ring }
  map_vadd' := by intro x v; change affineBracket a b c (v+x) =
                    determinant3 (b-a) (c-a) v + affineBracket a b c x
                  simp [affineBracket, determinant3]; ring

/-- A zero on a nonnegative convex hull can use only the labels on the plane. -/
private theorem nonnegative_section (r : Vertex → Point3) (s P : Finset Vertex)
    (f : Point3 →ᵃ[ℝ] ℝ) (hP : ∀ i ∈ P, f (r i) = 0)
    (hs : ∀ i ∈ s, i ∈ P ∨ 0 < f (r i)) {x : Point3} (hx : x ∈ vertexHull r s) :
    0 ≤ f x ∧ (f x = 0 → x ∈ vertexHull r (s ∩ P)) := by
  obtain ⟨w,hw,hm,hxw⟩ := weights_of_mem_vertexHull r s hx
  have hf := s.map_affineCombination r w hm f
  rw [s.affineCombination_eq_linear_combination r w hm, hxw,
      s.affineCombination_eq_linear_combination (f ∘ r) w hm] at hf
  change f x = ∑ i ∈ s, w i * f (r i) at hf
  have hh (i) (hi : i ∈ s) : 0 ≤ w i * f (r i) := by
    rcases hs i hi with hp | hp
    · simp [hP i hp]
    · exact mul_nonneg (hw i hi) hp.le
  refine ⟨hf ▸ Finset.sum_nonneg hh, fun hz => ?_⟩
  have hzero := (Finset.sum_eq_zero_iff_of_nonneg hh).mp (hf.symm.trans hz)
  have hout (i) (hi : i ∈ s) (ho : i ∉ s ∩ P) : w i = 0 := by
    have hp : i ∉ P := fun h => ho (Finset.mem_inter.mpr ⟨hi,h⟩)
    exact (mul_eq_zero.mp (hzero i hi)).resolve_right ((hs i hi).resolve_left hp).ne'
  have hsub : s ∩ P ⊆ s := Finset.inter_subset_left
  have hmass := (Finset.sum_subset hsub hout).trans hm
  have he : ∑ i ∈ s ∩ P, w i • r i = x := by
    rw [Finset.sum_subset hsub (fun i hi ho => by simp [hout i hi ho]), hxw]
  exact he ▸ weighted_mem_vertexHull r _ w (fun i hi => hw i (hsub hi)) hmass

private theorem plane_independent (r : Vertex → Point3) (a b c d : Vertex)
    (h : affineBracket (r a) (r b) (r c) (r d) ≠ 0) :
    AffineIndepOn ℝ r (↑({a,b,c} : Finset Vertex) : Set Vertex) := by
  let v : Fin 4 → Vertex := ![a,b,c,d]
  have he : r ∘ v = ![r a,r b,r c,r d] := by funext i; fin_cases i <;> rfl
  have hi : AffineIndependent ℝ (r ∘ v) := he ▸ affineIndependent_of_bracket_ne_zero _ _ _ _ h
  have hv : Function.Injective v := fun i j h => hi.injective (congrArg r h)
  apply ((affineIndepOn_range_iff hv r).mpr hi).mono
  intro i hm
  simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl
  · exact ⟨0,rfl⟩
  · exact ⟨1,rfl⟩
  · exact ⟨2,rfl⟩

/-- The two closed hulls are disjoint, including their portions contained in the plane. -/
theorem BracketPlane.disjoint {r : Vertex → Point3} {s t : Finset Vertex}
    (h : BracketPlane r s t) (hst : Disjoint s t) : Disjoint (vertexHull r s) (vertexHull r t) := by
  classical
  obtain ⟨a,b,c,d,hn,hs,ht⟩ := h
  let P : Finset Vertex := {a,b,c}
  let f := bracketFunctional (r a) (r b) (r c)
  have hz (i) (hi : i ∈ P) : f (r i) = 0 := by
    simp only [P,Finset.mem_insert,Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl <;>
      simp [f,bracketFunctional,affineBracket,determinant3] <;> ring
  rw [Set.disjoint_left]
  intro x hxs hxt
  obtain ⟨hp,hsx⟩ := nonnegative_section r s P f hz hs hxs
  obtain ⟨hm,htx⟩ := nonnegative_section r t P (-f) (by simpa using hz)
    (fun i hi => (ht i hi).imp_right (fun h => by simpa [f,bracketFunctional] using h)) hxt
  change 0 ≤ -(f x) at hm
  have hfx : f x = 0 := by linarith
  have h1 := hsx hfx
  have h2 := htx (by simp [hfx])
  have hP := plane_independent r a b c d hn
  have hp' : AffineIndependent ℝ ((↑) : P.image r → Point3) := by
    change AffineIndepOn ℝ id (↑(P.image r) : Set Point3)
    rw [Finset.coe_image]; exact hP.id_image
  have hx := And.intro h1 h2
  simp only [vertexHull, ← Finset.coe_image] at hx
  have hS : (s ∩ P).image r ⊆ P.image r := Finset.image_subset_image Finset.inter_subset_right
  have hT : (t ∩ P).image r ⊆ P.image r := Finset.image_subset_image Finset.inter_subset_right
  have hinter : x ∈ convexHull ℝ (↑((s ∩ P).image r) ∩ (↑((t ∩ P).image r) : Set Point3)) := by
    rw [hp'.convexHull_inter hS hT]; exact hx
  have hd : Disjoint (↑((s ∩ P).image r) : Set Point3) (↑((t ∩ P).image r) : Set Point3) := by
    rw [Set.disjoint_left]; intro p hs ht
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hs
    obtain ⟨j,hj,hji⟩ := Finset.mem_image.mp ht
    have he := hP.injOn (Finset.mem_inter.mp hj).2 (Finset.mem_inter.mp hi).2 hji
    exact Finset.disjoint_left.mp hst (Finset.mem_inter.mp hi).1 (he ▸ (Finset.mem_inter.mp hj).1)
  rw [Set.disjoint_iff_inter_eq_empty.mp hd, convexHull_empty] at hinter
  exact hinter

/-- Separating planes for all disjoint subfaces yield a closed embedding; other
spatial tetrahedra may be coplanar. -/
theorem isClosedEmbedding_of_bracket_planes (r : Vertex → Point3)
    (h : ∀ s t : Finset Vertex, s ∈ (triangleComplex faces).faces → t ∈ (triangleComplex faces).faces →
      Disjoint s t → BracketPlane r s t) : Topology.IsClosedEmbedding (evaluateTriangles faces r) := by
  let _ : CompactSpace (triangleWeightSpace faces) :=
    isCompact_iff_compactSpace.mp (isCompact_triangleWeightSpace faces)
  apply (continuous_evaluateTriangles faces r).isClosedEmbedding
  exact (evaluateTriangles_injective_iff_disjoint_subfaces faces r).mpr fun s t hs ht hd =>
    (h s t hs ht hd).disjoint hd

/-- A row of a separating-plane table for the labeled complex. -/
structure PlaneSeparator where
  a : Vertex
  b : Vertex
  c : Vertex
  above : Finset Vertex
  below : Finset Vertex
  deriving DecidableEq

def PlaneSeparator.front (p : PlaneSeparator) : Finset Vertex := {p.a, p.b, p.c} ∪ p.above
def PlaneSeparator.back (p : PlaneSeparator) : Finset Vertex := {p.a, p.b, p.c} ∪ p.below

def PlaneSeparator.Valid (p : PlaneSeparator) (r : Vertex → Point3) : Prop :=
  (∀ i ∈ p.above, 0 < affineBracket (r p.a) (r p.b) (r p.c) (r i)) ∧
  (∀ i ∈ p.below, affineBracket (r p.a) (r p.b) (r p.c) (r i) < 0)

def planeSubfaces : Finset (Finset Vertex) :=
  faces.toFinset.biUnion (fun f => (triangleVertexSet f).powerset)

private theorem mem_planeSubfaces {s : Finset Vertex} (hs : s ∈ (triangleComplex faces).faces) :
    s ∈ planeSubfaces := by
  obtain ⟨_, f, hf, hsub⟩ := hs
  exact Finset.mem_biUnion.mpr ⟨f, List.mem_toFinset.mpr hf, Finset.mem_powerset.mpr hsub⟩

/-- A finite separating-plane table covering the disjoint subfaces certifies a closed embedding. -/
theorem isClosedEmbedding_of_plane_table {r : Vertex → Point3} (planes : List PlaneSeparator)
    (valid : ∀ p ∈ planes, p.Valid r) (witness : ∀ p ∈ planes, p.above.Nonempty)
    (covers : ∀ s ∈ planeSubfaces, ∀ t ∈ planeSubfaces, Disjoint s t →
      ∃ p ∈ planes, (s ⊆ p.front ∧ t ⊆ p.back) ∨ (s ⊆ p.back ∧ t ⊆ p.front)) :
    Topology.IsClosedEmbedding (evaluateTriangles faces r) := by
  apply isClosedEmbedding_of_bracket_planes
  intro s t hs ht hd
  obtain ⟨p, hp, sides⟩ := covers s (mem_planeSubfaces hs) t (mem_planeSubfaces ht) hd
  obtain ⟨pos, neg⟩ := valid p hp
  obtain ⟨d, hd⟩ := witness p hp
  have plane : BracketPlane r p.front p.back := by
    refine ⟨p.a, p.b, p.c, d, (pos d hd).ne', ?_, ?_⟩
    · intro i hi
      exact (Finset.mem_union.mp hi).imp_right (pos i)
    · intro i hi
      exact (Finset.mem_union.mp hi).imp_right (neg i)
  rcases sides with ⟨hs, ht⟩ | ⟨hs, ht⟩
  · exact plane.mono hs ht
  · exact plane.symm.mono hs ht

end OrigamiTorus.Type5
