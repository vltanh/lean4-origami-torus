module

public import OrigamiTorus.Type2Links
import OrigamiTorus.EmbeddedEdges
import OrigamiTorus.PlanarCompleteGraph
import Mathlib.Tactic

/-! Geometric obstructions to a flat Type 2 link containing opposite rays. -/

public section

open InnerProductGeometry
open scoped NNReal

namespace OrigamiTorus.Type2

private def before (v a : Vertex) : List Vertex :=
  (linkCycle v).take ((linkCycle v).idxOf a)

private def between (v a b : Vertex) : List Vertex :=
  ((linkCycle v).drop ((linkCycle v).idxOf a+1)).take ((linkCycle v).idxOf b-(linkCycle v).idxOf a-1)

private def after (v b : Vertex) : List Vertex :=
  (linkCycle v).drop ((linkCycle v).idxOf b+1)

/-- If the two chosen endpoints have no connecting edge, one of the two
arcs contains an ordered pair with the required edges to the endpoints. -/
private theorem link_cut_checked (v a b : Vertex) (hab : [a,b].Sublist (linkCycle v)) :
    linkCycle v = before v a ++ (a :: (between v a b ++ b :: after v b)) ∧
    (isEdge a.val b.val = false →
      (∃ x y : Vertex, [x,y].Sublist (between v a b) ∧ isEdge a.val y.val = true ∧ isEdge x.val b.val = true) ∨
      ∃ x y : Vertex, [x,y].Sublist (after v b ++ before v a) ∧ isEdge b.val y.val = true ∧ isEdge x.val a.val = true) := by
  revert hab
  fin_cases v <;> revert a b <;> decide +kernel

private theorem impossible_minimal_arc (q : Vertex → Point3)
    (h : Function.Injective (evaluateTriangles geometricFaces q)) {v a b x y : Vertex}
    {xs ys : List Vertex} (hcycle : (a :: (xs ++ b :: ys)).Perm (linkCycle v))
    (horder : [x,y].Sublist xs) (hay : Adjacent geometricFaces a y) (hxb : Adjacent geometricFaces x b)
    (hop : angle (linkDirection q v a) (linkDirection q v b) = Real.pi)
    (hmin : angularPathLength (linkDirection q v a) (xs.map (linkDirection q v)) (linkDirection q v b) = Real.pi) :
    False := by
  have hfour : [a,x,y,b].Sublist (a :: (xs ++ b :: ys)) :=
    (horder.append (List.sublist_append_left [b] ys)).cons_cons a
  have hnd := hfour.nodup (hcycle.nodup_iff.mpr (linkCycle_checked v).1)
  have hm (z : Vertex) (hz : z ∈ [a,x,y,b]) : z ∈ linkCycle v := hcycle.mem_iff.mp (hfour.subset hz)
  exact impossible_minimal_arc_of_embedding q h hnd
    (fun z hz => (mem_linkCycle_iff v z).mp (hm z hz)) horder hay hxb hop hmin

/-- An embedded flat Type 2 star does not contain antipodal link directions. -/
theorem no_ordered_antipodal_pair (q : Vertex → Point3)
    (h : Function.Injective (evaluateTriangles geometricFaces q)) {v a b : Vertex}
    (hflat : linkPerimeter q v = 2 * Real.pi) (hab : [a,b].Sublist (linkCycle v)) :
    angle (linkDirection q v a) (linkDirection q v b) ≠ Real.pi := by
  intro hop
  have he := no_edge_of_opposite_rays_of_embedding q h
    ((mem_linkCycle_iff v a).mp (hab.subset (by simp)))
    ((mem_linkCycle_iff v b).mp (hab.subset (by simp))) hop
  rw [adjacent_geometricFaces_iff] at he
  have he' : isEdge a.val b.val = false := Bool.eq_false_of_not_eq_true he
  obtain ⟨hc,hpair⟩ := link_cut_checked v a b hab
  let xs := between v a b
  let ys := after v b ++ before v a
  have hcut : before v a ++ (a :: (xs ++ b :: after v b)) = linkCycle v := hc.symm
  have hcycle : (a :: (xs ++ b :: ys)).Perm (linkCycle v) := by
    rw [← hcut]
    simpa only [ys, List.cons_append, List.append_assoc] using
      (List.perm_append_comm : ((a :: (xs ++ b :: after v b)) ++ before v a).Perm _)
  let d := linkDirection q v
  have hop' : angle (d b) (d a) = Real.pi := (angle_comm _ _).trans hop
  have hsum : angularPathLength (d a) (xs.map d) (d b) +
      angularPathLength (d b) (ys.map d) (d a) = 2 * Real.pi := by
    rw [← hflat, linkPerimeter_eq_angularCycleLength, ← hcut]
    simp only [List.map_append]
    rw [angularCycleLength_append_comm]
    simpa only [ys, List.map_cons, List.map_append, List.cons_append, List.append_assoc] using
      (angularCycleLength_split_pair (d a) (d b) (xs.map d) (ys.map d)).symm
  have hfirst := angle_le_angularPathLength (d a) (d b) (xs.map d)
  have hsecond := angle_le_angularPathLength (d b) (d a) (ys.map d)
  rw [hop] at hfirst
  rw [hop'] at hsecond
  rcases hpair he' with ⟨x,y,hxy,hE,hF⟩ | ⟨x,y,hxy,hE,hF⟩
  · exact impossible_minimal_arc q h hcycle hxy ((adjacent_geometricFaces_iff _ _).mpr hE)
      ((adjacent_geometricFaces_iff _ _).mpr hF) hop (by linarith)
  · have hrev : (b :: (ys ++ a :: xs)).Perm (linkCycle v) := by
      refine List.Perm.trans ?_ hcycle
      simpa only [List.cons_append, List.append_assoc] using
        (List.perm_append_comm : ((b :: ys) ++ (a :: xs)).Perm ((a :: xs) ++ (b :: ys)))
    exact impossible_minimal_arc q h hrev hxy ((adjacent_geometricFaces_iff _ _).mpr hE)
      ((adjacent_geometricFaces_iff _ _).mpr hF) hop' (by linarith)

private theorem triple_cut_checked (v a b c : Vertex) (h : [a,b,c].Sublist (linkCycle v)) :
    linkCycle v = before v a ++ (a :: (between v a b ++ b :: (between v b c ++ c :: after v c))) := by
  revert h
  fin_cases v <;> revert a b c <;> decide +kernel

private theorem link_is_planar_of_positive_triple (q : Vertex → Point3)
    (h : Function.Injective (evaluateTriangles geometricFaces q)) {v a b c : Vertex}
    (hflat : linkPerimeter q v = 2 * Real.pi) (horder : [a,b,c].Sublist (linkCycle v))
    (α β γ : ℝ) (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ)
    (hrel : α • linkDirection q v a + β • linkDirection q v b + γ • linkDirection q v c = 0) :
    ∃ P : Submodule ℝ (EuclideanSpace ℝ (Fin 3)), Module.finrank ℝ P ≤ 2 ∧
      ∀ w ∈ linkCycle v, linkDirection q v w ∈ P := by
  classical
  let d := linkDirection q v
  let xs := between v a b
  let ys := between v b c
  let zs := after v c ++ before v a
  have hcut : before v a ++ (a :: (xs ++ b :: (ys ++ c :: after v c))) = linkCycle v :=
    (triple_cut_checked v a b c horder).symm
  have hpath : angularPathLength (d a) (xs.map d) (d b) + angularPathLength (d b) (ys.map d) (d c) +
      angularPathLength (d c) (zs.map d) (d a) = 2 * Real.pi := by
    rw [← hflat, linkPerimeter_eq_angularCycleLength, ← hcut]
    simp only [List.map_append]
    rw [angularCycleLength_append_comm]
    simpa only [zs, List.map_cons, List.map_append, List.cons_append, List.append_assoc] using
      (angularCycleLength_split_triple (d a) (d b) (d c) (xs.map d) (ys.map d) (zs.map d)).symm
  have hq := vertex_injective_of_embedding q h
  have hθ := triangle_perimeter_eq_of_positive_relation (d a) (d b) (d c)
    (linkDirection_ne_zero q hq v c (horder.subset (by simp))) α β γ hα hβ hγ hrel
  have h₁ := angle_le_angularPathLength (d a) (d b) (xs.map d)
  have h₂ := angle_le_angularPathLength (d b) (d c) (ys.map d)
  have h₃ := angle_le_angularPathLength (d c) (d a) (zs.map d)
  have hab : angle (d a) (d b) ≠ Real.pi := no_ordered_antipodal_pair q h hflat
    ((List.sublist_append_left [a,b] [c]).trans horder)
  have hbc : angle (d b) (d c) ≠ Real.pi := no_ordered_antipodal_pair q h hflat
    ((List.sublist_append_right [a] [b,c]).trans horder)
  have hca : angle (d c) (d a) ≠ Real.pi := by
    rw [angle_comm]
    exact no_ordered_antipodal_pair q h hflat (((List.Sublist.refl [c]).cons b |>.cons_cons a).trans horder)
  let P := Submodule.span ℝ ({d a,d b} : Set (EuclideanSpace ℝ (Fin 3)))
  have ha : d a ∈ P := Submodule.subset_span (by simp)
  have hb : d b ∈ P := Submodule.subset_span (by simp)
  have hc : d c ∈ P := by
    have he : γ • d c = -(α • d a + β • d b) := by
      apply eq_neg_iff_add_eq_zero.mpr
      simpa only [add_comm (γ • d c) (α • d a + β • d b)] using hrel
    have hγc : γ • d c ∈ P := he ▸ P.neg_mem (P.add_mem (P.smul_mem α ha) (P.smul_mem β hb))
    have hm := P.smul_mem γ⁻¹ hγc
    rwa [smul_smul, inv_mul_cancel₀ hγ.ne', one_smul] at hm
  have hspan (u t : Vertex) (ls : List Vertex) (hu : d u ∈ P) (ht : d t ∈ P)
      (hne : angle (d u) (d t) ≠ Real.pi)
      (he : angularPathLength (d u) (ls.map d) (d t) = angle (d u) (d t))
      (w : Vertex) (hw : w ∈ ls) (hv : w ∈ linkCycle v) : d w ∈ P := by
    have hm := mem_span_of_angularPathLength_eq (d u) (d t) (ls.map d) he hne
      (List.mem_map_of_mem hw) (linkDirection_ne_zero q hq v w hv)
    obtain ⟨s,t,hs⟩ := Submodule.mem_span_pair.mp hm
    rw [← hs]
    exact P.add_mem (P.smul_mem (s : ℝ) hu) (P.smul_mem (t : ℝ) ht)
  refine ⟨P,?_,?_⟩
  · have he := (finrank_span_finset_le_card (R := ℝ) {d a,d b}).trans Finset.card_le_two
    unfold Set.finrank at he
    rw [Finset.coe_pair] at he
    exact he
  · intro w hw
    have hw' := hw
    rw [← hcut] at hw'
    simp only [List.mem_append, List.mem_cons] at hw'
    rcases hw' with hw' | rfl | hw' | rfl | hw' | rfl | hw'
    · exact hspan c a zs hc ha hca (by linarith) w (List.mem_append_right _ hw') hw
    · exact ha
    · exact hspan a b xs ha hb hab (by linarith) w hw' hw
    · exact hb
    · exact hspan b c ys hb hc hbc (by linarith) w hw' hw
    · exact hc
    · exact hspan c a zs hc ha hca (by linarith) w (List.mem_append_left _ hw') hw

/-- If an embedded flat Type 2 link lacks strict support, its directions are planar. -/
theorem planar_of_flat_no_strictSupport (q : Vertex → Point3)
    (h : Function.Injective (evaluateTriangles geometricFaces q)) (v : Vertex)
    (hflat : linkPerimeter q v = 2 * Real.pi) (hs : ¬ HasStrictSupport geometricFaces q v) :
    ∃ P : Submodule ℝ (EuclideanSpace ℝ (Fin 3)), Module.finrank ℝ P ≤ 2 ∧
      ∀ w ∈ linkCycle v, linkDirection q v w ∈ P := by
  rcases ordered_pair_or_triple_of_flat_no_support q v hflat (vertex_injective_of_embedding q h) hs with
    ⟨a,b,hab,hop⟩ | ⟨a,b,c,horder,w,hp,_,_,hrel⟩
  · exact False.elim (no_ordered_antipodal_pair q h hflat hab hop)
  · exact link_is_planar_of_positive_triple q h hflat horder (w 0) (w 1) (w 2) (hp 0) (hp 1) (hp 2)
      (by simpa [Fin.sum_univ_succ, add_assoc] using hrel)

private def cliqueAt (v : Vertex) : Fin 5 → Vertex :=
  if v < 4 then ![v,4,5,6,7] else ![3,4,5,6,7]

private theorem cliqueAt_injective (v : Vertex) : Function.Injective (cliqueAt v) := by
  fin_cases v <;> decide +kernel

private theorem cliqueAt_in_star (v : Vertex) (i : Fin 5) :
    cliqueAt v i = v ∨ cliqueAt v i ∈ linkCycle v := by
  fin_cases v <;> revert i <;> decide +kernel

private theorem cliqueAt_edges (v : Vertex) {i j : Fin 5} (h : i ≠ j) :
    Adjacent geometricFaces (cliqueAt v i) (cliqueAt v j) := by
  rw [adjacent_geometricFaces_iff]
  revert i j
  fin_cases v <;> decide +kernel

private theorem cliqueAt_small_face (v : Vertex) (s : Finset (Fin 5)) (hs : s.Nonempty)
    (hcard : s.card ≤ 2) : s.image (cliqueAt v) ∈ (triangleComplex geometricFaces).faces := by
  have hc : 1 ≤ s.card := Finset.one_le_card.mpr hs
  have he : s.card = 1 ∨ s.card = 2 := by omega
  rcases he with h | h
  · obtain ⟨i,rfl⟩ := Finset.card_eq_one.mp h
    simpa only [Finset.image_singleton] using singleton_face (cliqueAt v i)
  · obtain ⟨i,j,hne,rfl⟩ := Finset.card_eq_two.mp h
    simpa only [Finset.image_insert, Finset.image_singleton] using adjacent_pair_face (cliqueAt_edges v hne)

theorem not_planar_of_embedding (q : Vertex → Point3)
    (h : Function.Injective (evaluateTriangles geometricFaces q)) (v : Vertex)
    (P : Submodule ℝ (EuclideanSpace ℝ (Fin 3))) (hP : Module.finrank ℝ P ≤ 2)
    (hstar : ∀ w ∈ linkCycle v, linkDirection q v w ∈ P) : False := by
  let Q := P.comap euclideanPoint
  let J : Q →ₗ[ℝ] P := (euclideanPoint.comp Q.subtype).codRestrict P (fun z => z.property)
  have hJ : Function.Injective J := by
    intro x y he
    exact Subtype.ext (euclideanPoint_injective (congrArg Subtype.val he))
  have hQ : Module.finrank ℝ Q ≤ 2 := (LinearMap.finrank_le_finrank_of_injective hJ).trans hP
  let r (i : Fin 5) : Q := ⟨q (cliqueAt v i)-q v, by
    change linkDirection q v (cliqueAt v i) ∈ P
    rcases cliqueAt_in_star v i with he | he
    · rw [he, linkDirection, sub_self, map_zero]
      exact P.zero_mem
    · exact hstar _ he⟩
  let A : Q →ᵃ[ℝ] Point3 :=
    (AffineEquiv.constVAdd ℝ Point3 (q v)).toAffineMap.comp Q.subtype.toAffineMap
  have ha (i : Fin 5) : A (r i) = q (cliqueAt v i) := by
    change q v + (q (cliqueAt v i)-q v) = q (cliqueAt v i)
    abel
  have hmap (s : Finset (Fin 5)) : A '' vertexHull r s = vertexHull q (s.image (cliqueAt v)) := by
    rw [vertexHull, A.image_convexHull, Set.image_image, vertexHull, Finset.coe_image, Set.image_image]
    exact congrArg (convexHull ℝ) (Set.image_congr (fun i _ => ha i))
  obtain ⟨s,t,hs,ht,hst,z,hz,hz'⟩ := exists_small_intersection_of_five_planar_points r hQ
  have hne (u : Finset (Fin 5)) (hz : z ∈ vertexHull r u) : u.Nonempty := by
    by_contra! hu
    simp [hu, vertexHull] at hz
  have hdisj := disjoint_vertexHull_of_injective_evaluateTriangles geometricFaces q h
    (s.image (cliqueAt v)) (t.image (cliqueAt v)) (cliqueAt_small_face v s (hne s hz) hs)
    (cliqueAt_small_face v t (hne t hz') ht) ((Finset.disjoint_image (cliqueAt_injective v)).mpr hst)
  exact Set.disjoint_left.mp hdisj (hmap s ▸ Set.mem_image_of_mem A hz)
    (hmap t ▸ Set.mem_image_of_mem A hz')

/-- The link at every vertex of an embedded flat Type 2 realization lies in a strict hemisphere. -/
theorem strictSupport_of_flat_embedding (q : Vertex → Point3)
    (h : Function.Injective (evaluateTriangles geometricFaces q)) (v : Vertex)
    (hflat : linkPerimeter q v = 2 * Real.pi) : HasStrictSupport geometricFaces q v := by
  by_contra hs
  obtain ⟨P,hP,hstar⟩ := planar_of_flat_no_strictSupport q h v hflat hs
  exact not_planar_of_embedding q h v P hP hstar

end OrigamiTorus.Type2
