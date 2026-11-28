module

public import OrigamiTorus.EightVertex.Type5.Geometry
public import OrigamiTorus.EightVertex.Type2.StrictSupport
import Mathlib.Analysis.Convex.Radon
import Mathlib.Tactic

/-! Supporting planes and affine independence for the cliques of an embedded flat Type 5 torus. -/

public section

open InnerProductGeometry

namespace OrigamiTorus.Type5

open Type2 (Adjacent HasStrictSupport linkDirection)

private def before (v a : Vertex) : List Vertex :=
  (orientedLinkCycle v).take ((orientedLinkCycle v).idxOf a)

private def between (v a b : Vertex) : List Vertex :=
  ((orientedLinkCycle v).drop ((orientedLinkCycle v).idxOf a + 1)).take
    ((orientedLinkCycle v).idxOf b - (orientedLinkCycle v).idxOf a - 1)

private def after (v b : Vertex) : List Vertex :=
  (orientedLinkCycle v).drop ((orientedLinkCycle v).idxOf b + 1)

private theorem triple_cut (v a b c : Vertex) (h : [a,b,c].Sublist (orientedLinkCycle v)) :
    before v a ++ (a :: (between v a b ++ b :: (between v b c ++ c :: after v c))) =
      orientedLinkCycle v := by
  revert a b c
  fin_cases v <;> decide +kernel

/-- Use the three anchors, one root, and one leaf in the closed star of `v`. -/
private def cliqueAt (v : Vertex) : Fin 5 → Vertex :=
  ![1,2,5,if v = 4 then 4 else 3,if v ∈ leaves then v else 0]

/-- A supporting plane through a flat vertex has every neighbor strictly
on the same side. A planar star would contain a straight-line planar K₅. -/
theorem strictSupport_of_flat_embedding (q : Vertex → Point3)
    (he : Function.Injective (evaluateTriangles faces q)) (v : Vertex) (hf : FlatAt q v) :
    HasStrictSupport faces q v := by
  let ns := orientedLinkCycle v
  have hd (a : Vertex) (ha : a ∈ ns) : linkDirection q v a ≠ 0 := by
    intro hz
    have hi := vertex_injective_of_injective_evaluateTriangles faces q type5_covers he
    exact ((mem_orientedLinkCycle _ _).mp ha).1
      (hi (sub_eq_zero.mp (Type2.euclideanPoint_injective (hz.trans Type2.euclideanPoint.map_zero.symm)))).symm
  have hant (a b : Vertex) (hab : [a,b].Sublist ns) :
      angle (linkDirection q v a) (linkDirection q v b) ≠ Real.pi :=
    neighbors_not_opposite q he (hab.subset (by simp)) (hab.subset (by simp))
      (by simpa using hab.nodup (linkCycles_checked v).1) hf
  by_contra hs
  rcases Type2.ordered_pair_or_triple_of_flat_link q v (mem_orientedLinkCycle v)
      (linkCycles_checked v).1 hf hd hs with ⟨a,b,hab,hπ⟩ | ⟨a,b,c,habc,w,hw,_,_,hrel⟩
  · exact hant a b hab hπ
  · obtain ⟨P,hP,hstar⟩ := Type2.link_is_planar_of_positive_triple q
      (triple_cut v a b c habc) hf hd hant habc (w 0) (w 1) (w 2) (hw 0) (hw 1) (hw 2)
      (by simpa [Fin.sum_univ_succ,add_assoc] using hrel)
    have hk : ∀ t, Function.Injective (cliqueAt t) := by decide +kernel
    have hedge (t : Vertex) (i j : Fin 5) (hne : i ≠ j) : Adjacent faces (cliqueAt t i) (cliqueAt t j) := by
      rw [adjacency_test]
      revert t i j
      decide +kernel
    have hm : ∀ t i, cliqueAt t i = t ∨ cliqueAt t i ∈ orientedLinkCycle t := by
      decide +kernel
    apply Type2.clique_not_planar q he (cliqueAt v) (hk v) (fun _ => type5_covers _) (hedge v) v P hP
    intro i
    rcases hm v i with h | h
    · simp [h,linkDirection]
    · exact hstar _ h

/-- Every four pairwise adjacent labels span a tetrahedron of nonzero volume.
A Radon partition would put a vertex in the hull of its neighbors, or
give intersecting disjoint edges. -/
theorem clique_affineIndependent (q : Vertex → Point3)
    (he : Function.Injective (evaluateTriangles faces q)) (hf : ∀ v, FlatAt q v)
    (k : Fin 4 → Vertex) (hedge : ∀ i j, i ≠ j → Adjacent faces (k i) (k j)) :
    AffineIndependent ℝ (q ∘ k) := by
  classical
  by_contra h
  obtain ⟨I,z,hz₁,hz₂⟩ := Convex.radon_partition h
  let s := I.toFinset
  have h₁ : z ∈ vertexHull q (s.image k) := by
    simpa [s,vertexHull,Set.image_image] using hz₁
  have h₂ : z ∈ vertexHull q (sᶜ.image k) := by
    simpa [s,vertexHull,Set.image_image] using hz₂
  have small (a b : Finset (Fin 4)) (hab : Disjoint a b)
      (ha : a.card ≤ 1) (hza : z ∈ vertexHull q (a.image k))
      (hzb : z ∈ vertexHull q (b.image k)) : False := by
    obtain ⟨i,hi⟩ := Finset.card_le_one_iff_subset_singleton.mp ha
    rcases Finset.subset_singleton_iff.mp hi with h | rfl
    · simp [h,vertexHull] at hza
    · have hz : z = q (k i) := by simpa [vertexHull] using hza
      apply Type2.strictSupport_not_mem_neighborHull _ q (k i) (b.image k) _ (strictSupport_of_flat_embedding q he _ (hf _)) (hz ▸ hzb)
      intro j hj
      obtain ⟨l,hl,rfl⟩ := Finset.mem_image.mp hj
      exact hedge i l (fun e => Finset.disjoint_left.mp hab (Finset.mem_singleton_self i) (e ▸ hl))
  have hdis : Disjoint s sᶜ := disjoint_compl_right
  by_cases h₁s : s.card ≤ 1
  · exact small _ _ hdis h₁s h₁ h₂
  by_cases h₂s : sᶜ.card ≤ 1
  · exact small _ _ hdis.symm h₂s h₂ h₁
  have hcard : s.card + sᶜ.card = 4 := by simp
  have pair (a : Finset (Fin 4)) (ha : a.card = 2) :
      a.image k ∈ (triangleComplex faces).faces := by
    obtain ⟨i,j,hij,rfl⟩ := Finset.card_eq_two.mp ha
    simpa using adjacent_pair_face (hedge i j hij)
  have hk : Function.Injective k := fun i j h => by
    by_contra hij
    exact (hedge i j hij).1 h
  exact Set.disjoint_left.mp (disjoint_vertexHull_of_injective_evaluateTriangles faces q he
    _ _ (pair s (by omega)) (pair sᶜ (by omega)) ((Finset.disjoint_image hk).mpr hdis)) h₁ h₂

end OrigamiTorus.Type5
