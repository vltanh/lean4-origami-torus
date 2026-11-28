module

public import OrigamiTorus.EightVertex.Type5.StrictSupport
import Mathlib.Geometry.Euclidean.Basic
import Mathlib.Tactic

/-! A flat embedded Type 5 placement is determined, in every Euclidean
dimension, by twenty-two of its labeled edge lengths. -/

public section

namespace OrigamiTorus.Type5

open Type2 (Adjacent euclideanPoint)

private abbrev E3 := EuclideanSpace ℝ (Fin 3)

/-- Distances to an affine basis determine a point even in a higher-dimensional
comparison placement, provided the given distances come from the span. -/
private theorem dist_of_four_centers {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (p : Fin 4 → E3) (r : Fin 4 → E) (hi : AffineIndependent ℝ p)
    (hc : ∀ i j, dist (p i) (p j) = dist (r i) (r j))
    (a b : E3) (a' b' : E) (ha : ∀ i, dist (p i) a = dist (r i) a')
    (hb : ∀ i, dist (p i) b = dist (r i) b') : dist a b = dist a' b' := by
  let B : AffineBasis (Fin 4) ℝ E3 := ⟨p, hi,
    hi.affineSpan_eq_top_iff_card_eq_finrank_add_one.mpr (by simp)⟩
  let w := fun i => B.coord i a
  have hw : ∑ i, w i = 1 := B.sum_coord_apply_eq_one a
  have hw₀ : Finset.univ.affineCombination ℝ p w = a := B.affineCombination_coord_eq_self a
  have transfer (x : E3) (x' : E) (h : ∀ i, dist (p i) x = dist (r i) x') :
      dist a x = dist (Finset.univ.affineCombination ℝ r w) x' := by
    apply (sq_eq_sq₀ dist_nonneg dist_nonneg).mp
    rw [← hw₀, EuclideanGeometry.dist_affineCombination_const_sq p x hw,
      EuclideanGeometry.dist_affineCombination_const_sq r x' hw]
    simp_rw [hc,h]
  have he := transfer a a' ha
  rw [dist_self, eq_comm, dist_eq_zero] at he
  simpa only [he] using transfer b b' hb

private def frame (j : Vertex) : Fin 4 → Vertex := ![1,2,5,j]

private theorem frame_independent (q : Vertex → Point3)
    (he : Function.Injective (evaluateTriangles faces q)) (hf : ∀ v, FlatAt q v)
    {j : Vertex} (hj : j = 3 ∨ j = 0) :
    AffineIndependent ℝ ((euclideanPoint ∘ q) ∘ frame j) := by
  have hc (i l : Fin 4) (hne : i ≠ l) : Adjacent faces (frame j i) (frame j l) := by
    rw [adjacency_test]
    rcases hj with rfl | rfl <;> revert i l <;> decide +kernel
  exact (clique_affineIndependent q he hf (frame j) hc).map'
    euclideanPoint.toAffineMap Type2.euclideanPoint_injective

/-- The six lengths on 1253, the four from each leaf to 1253, and the four
from vertex 4 to 1250. The two omitted edges are 46 and 47. -/
def determiningEdge (a b : Vertex) : Bool :=
  let e := orderedEdge a b
  edgeList.contains e && e != (4,6) && e != (4,7)

theorem determiningEdge_count :
    (edgeList.filter (fun e => determiningEdge e.1 e.2)).length = 22 := by decide +kernel

/-- Matching the 22 determining edge lengths of a flat embedded Type 5
placement forces all 28 pairwise distances, in any real inner product space.
The comparison configuration can be arbitrary. -/
theorem distances_determined {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (q : Vertex → Point3) (he : Function.Injective (evaluateTriangles faces q))
    (hf : ∀ v, FlatAt q v) (r : Vertex → E)
    (h : ∀ a b, determiningEdge a b = true →
      dist (euclideanPoint (q a)) (euclideanPoint (q b)) = dist (r a) (r b)) :
    ∀ a b, dist (euclideanPoint (q a)) (euclideanPoint (q b)) = dist (r a) (r b) := by
  let p := euclideanPoint ∘ q
  let agrees (a b : Vertex) := dist (p a) (p b) = dist (r a) (r b)
  have known {a b} (hab : a = b ∨ determiningEdge a b = true) : agrees a b := by
    rcases hab with rfl | h'
    · simp [agrees]
    · exact h a b h'
  have primary : ∀ (i : Fin 4) (b : Vertex), b ≠ 4 →
      frame 3 i = b ∨ determiningEdge (frame 3 i) b = true := by decide +kernel
  have cross₁ (i : Fin 4) (b : Vertex) (hb : b ≠ 4) : agrees (frame 3 i) b :=
    known (primary i b hb)
  have first (a b : Vertex) (ha : a ≠ 4) (hb : b ≠ 4) : agrees a b :=
    dist_of_four_centers _ (r ∘ frame 3) (frame_independent q he hf (Or.inl rfl))
      (fun i j => cross₁ i _ (by revert j; decide +kernel))
      (p a) (p b) _ _ (fun i => cross₁ i a ha) (fun i => cross₁ i b hb)
  have secondary : ∀ i, determiningEdge (frame 0 i) 4 = true := by decide +kernel
  have cross₂ (i : Fin 4) (b : Vertex) : agrees (frame 0 i) b := by
    by_cases hb : b = 4
    · exact hb ▸ known (Or.inr (secondary i))
    · exact first _ b (by revert i; decide +kernel) hb
  intro a b
  exact dist_of_four_centers _ (r ∘ frame 0) (frame_independent q he hf (Or.inr rfl))
    (fun i j => cross₂ i _) (p a) (p b) _ _ (fun i => cross₂ i a) (fun i => cross₂ i b)

/-- A comparison placement with the same determining lengths also separates every
pair of distinct points of the abstract triangle complex. -/
theorem injective_of_determining_lengths (q r : Vertex → Point3)
    (he : Function.Injective (evaluateTriangles faces q)) (hf : ∀ v, FlatAt q v)
    (h : ∀ a b, determiningEdge a b = true →
      dist (euclideanPoint (q a)) (euclideanPoint (q b)) = dist (euclideanPoint (r a)) (euclideanPoint (r b))) :
    Function.Injective (evaluateTriangles faces r) := by
  have hd := distances_determined q he hf (euclideanPoint ∘ r) h
  intro u v huv
  apply he
  apply Type2.euclideanPoint_injective
  have sum_one (w : triangleWeightSpace faces) : ∑ i, w.val i = 1 := by
    obtain ⟨_,_,hw⟩ := w.property
    exact hw.2.1
  have metric (p : Vertex → Point3) :=
    EuclideanGeometry.dist_affineCombination (euclideanPoint ∘ p) (sum_one u) (sum_one v)
  have left := metric q
  have right := metric r
  simp only [Function.comp_apply] at hd left right
  simp_rw [hd] at left
  have transfer := left.trans right.symm
  simp only [Finset.affineCombination_eq_linear_combination _ _ _ (sum_one u),
    Finset.affineCombination_eq_linear_combination _ _ _ (sum_one v)] at transfer
  have eval (p : Vertex → Point3) (w : triangleWeightSpace faces) :
      (∑ i, w.val i • (euclideanPoint ∘ p) i) = euclideanPoint (evaluateTriangles faces p w) := by
    simp [evaluateTriangles,evaluateWeights,map_sum]
  simp only [eval,huv,dist_self,mul_zero,mul_eq_zero,or_self,dist_eq_zero] at transfer
  exact transfer


end OrigamiTorus.Type5
