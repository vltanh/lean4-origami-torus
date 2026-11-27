module

public import OrigamiTorus.Type1.Collapse
public import OrigamiTorus.Type2.StrictSupport
import OrigamiTorus.Geometry.EmbeddedEdges
import Mathlib.Tactic

/-! Flatness and the complete graph force every collapsed vertex to be strictly exposed. -/

public section

open InnerProductGeometry

namespace OrigamiTorus.Type1

open Type2 (Adjacent HasStrictSupport euclideanPoint euclideanPoint_injective linkDirection)

private def collapsedLink : Vertex → List Vertex :=
  ![[],[2,3,5,7,6,4],[1,4,7,5,6,3],[1,2,6,7,4,5],[1,6,5,3,7,2],
    [1,3,4,6,2,7],[1,7,3,2,5,4],[1,5,2,4,3,6]]

private theorem collapsedLink_checked (v : Vertex) :
    (collapsedLink v).Nodup ∧ ∀ w, w ∈ collapsedLink v ↔ Adjacent collapsedFaces v w := by
  refine ⟨?_,?_⟩
  · revert v
    decide +kernel
  · have hn : ∀ v w : Vertex, w ∈ collapsedLink v ↔ v ≠ 0 ∧ w ≠ 0 ∧ v ≠ w := by
      decide +kernel
    intro w
    rw [hn]
    refine ⟨fun h => collapsed_complete_graph _ _ h.1 h.2.1 h.2.2, ?_⟩
    intro h
    obtain ⟨hne,f,hf,hv,hw⟩ := h
    have hzero : ∀ f ∈ collapsedFaces, (0 : Vertex) ∉ triangleVertexSet f := by decide +kernel
    exact ⟨fun e => hzero f hf (e ▸ hv), fun e => hzero f hf (e ▸ hw), hne⟩

theorem collapsed_covers (v : Vertex) (hv : v ≠ 0) : ∃ f ∈ collapsedFaces, v ∈ triangleVertexSet f := by
  revert v
  decide +kernel

private theorem perimeter_eq (q : Vertex → Point3) (v : Vertex) :
    angularCycleLength ((collapsedLink v).map (linkDirection q v)) =
      coneAngles collapsedFaces (euclideanPoint ∘ q) v := by
  rw [angularCycleLength_eq_sum_zip]
  fin_cases v <;>
    norm_num [collapsedLink,collapsedFaces,faces,coneAngles,cornerRays,linkDirection,
      map_sub,Function.comp_apply] <;> abel

private def before (v a : Vertex) : List Vertex :=
  (collapsedLink v).take ((collapsedLink v).idxOf a)

private def between (v a b : Vertex) : List Vertex :=
  ((collapsedLink v).drop ((collapsedLink v).idxOf a+1)).take
    ((collapsedLink v).idxOf b-(collapsedLink v).idxOf a-1)

private def after (v b : Vertex) : List Vertex :=
  (collapsedLink v).drop ((collapsedLink v).idxOf b+1)

private theorem triple_cut (v a b c : Vertex) (h : [a,b,c].Sublist (collapsedLink v)) :
    before v a ++ (a :: (between v a b ++ b :: (between v b c ++ c :: after v c))) =
      collapsedLink v := by
  revert v a b c
  decide +kernel

private def clique : Fin 5 → Vertex := ![1,2,3,4,5]

/-- Every active vertex in a flat embedded collapsed realization has a strict
supporting plane. The unused label has empty adjacency. -/
theorem collapsed_strictSupport (q : Vertex → Point3)
    (he : Function.Injective (evaluateTriangles collapsedFaces q))
    (hf : ∀ v : Vertex, v ≠ 0 → coneAngles collapsedFaces (euclideanPoint ∘ q) v = 2*Real.pi) :
    ∀ v, HasStrictSupport collapsedFaces q v := by
  intro v
  by_cases hv : v = 0
  · subst v
    refine ⟨0, fun w hw => ?_⟩
    have hm := ((collapsedLink_checked 0).2 w).mpr hw
    simp [collapsedLink] at hm
  let ns := collapsedLink v
  have hmem (a : Vertex) : a ∈ ns ↔ Adjacent collapsedFaces v a := (collapsedLink_checked v).2 a
  have hn (a : Vertex) (ha : a ∈ ns) : a ≠ 0 := by
    have h : ∀ v : Vertex, 0 ∉ collapsedLink v := by decide +kernel
    exact fun e => h v (e ▸ ha)
  have hdir (a : Vertex) (ha : a ∈ ns) : linkDirection q v a ≠ 0 := by
    intro hz
    have hq : q a = q v :=
      sub_eq_zero.mp (euclideanPoint_injective (hz.trans euclideanPoint.map_zero.symm))
    have hh := disjoint_vertexHull_of_injective_evaluateTriangles collapsedFaces q he
      {a} {v} (covered_singleton_face (collapsed_covers a (hn a ha)))
      (covered_singleton_face (collapsed_covers v hv))
      (by simpa using (hmem a).mp ha |>.1.symm)
    have ha' : q a ∈ vertexHull q {a} := by simp [vertexHull]
    have hv' : q a ∈ vertexHull q {v} := by simp [vertexHull,hq]
    exact Set.disjoint_left.mp hh ha' hv'
  have hant (a b : Vertex) (hab : [a,b].Sublist ns) :
      angle (linkDirection q v a) (linkDirection q v b) ≠ Real.pi := by
    have ha := hab.subset (by simp : a ∈ [a,b])
    have hb := hab.subset (by simp : b ∈ [a,b])
    have hne : a ≠ b := by
      have h := hab.nodup (collapsedLink_checked v).1
      simpa using h
    exact fun h => no_edge_of_opposite_rays_of_embedding q he ((hmem a).mp ha) ((hmem b).mp hb) h
      (collapsed_complete_graph a b (hn a ha) (hn b hb) hne)
  have hflat : angularCycleLength (ns.map (linkDirection q v)) = 2*Real.pi :=
    (perimeter_eq q v).trans (hf v hv)
  by_contra hs
  rcases Type2.ordered_pair_or_triple_of_flat_link q v hmem (collapsedLink_checked v).1 hflat hdir hs with
    ⟨a,b,hab,hπ⟩ | ⟨a,b,c,horder,w,hw,_,_,hrel⟩
  · exact hant a b hab hπ
  · obtain ⟨P,hP,hstar⟩ := Type2.link_is_planar_of_positive_triple q
      (triple_cut v a b c horder) hflat hdir hant horder
      (w 0) (w 1) (w 2) (hw 0) (hw 1) (hw 2)
      (by simpa [Fin.sum_univ_succ,add_assoc] using hrel)
    have hcl : Function.Injective clique := by decide +kernel
    have hcn (i : Fin 5) : clique i ≠ 0 := by revert i; decide +kernel
    refine Type2.clique_not_planar q he clique hcl (fun i => collapsed_covers _ (hcn i))
      (fun i j hij => collapsed_complete_graph _ _ (hcn i) (hcn j) (hcl.ne hij)) v P hP ?_
    intro i
    by_cases h : clique i = v
    · simp [h,linkDirection]
    · exact hstar _ ((hmem _).mpr (collapsed_complete_graph _ _ hv (hcn i) (Ne.symm h)))

end OrigamiTorus.Type1
