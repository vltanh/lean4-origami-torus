module

public import OrigamiTorus.Geometry.EmbeddedEdges
public import OrigamiTorus.Geometry.AngleDerivative
import Mathlib.Tactic

/-! The valence-three star in the Type 1 obstruction. -/

@[expose] public section

open InnerProductGeometry
open scoped NNReal

namespace OrigamiTorus

open Type2 (Adjacent euclideanPoint euclideanPoint_injective linkDirection)

/-- If a flat star has three neighbors whose three joining edges are
present, its center is a strict convex combination of them. -/
theorem flat_three_neighbor_star {fs : List Triangle} (q : Vertex → Point3)
    (he : Function.Injective (evaluateTriangles fs q))
    (hcover : ∀ i : Vertex, ∃ f ∈ fs, i ∈ triangleVertexSet f) {v a b c : Vertex}
    (ha : Adjacent fs v a) (hb : Adjacent fs v b) (hc : Adjacent fs v c)
    (hab : Adjacent fs a b) (hac : Adjacent fs a c) (hbc : Adjacent fs b c)
    (hflat : angle (linkDirection q v a) (linkDirection q v b) +
      angle (linkDirection q v b) (linkDirection q v c) +
      angle (linkDirection q v c) (linkDirection q v a) = 2*Real.pi) :
    ∃ s t : ℝ, 0 < s ∧ 0 < t ∧ q a+s • q b+t • q c = (1+s+t) • q v := by
  let A := linkDirection q v a
  let B := linkDirection q v b
  let C := linkDirection q v c
  have hn (w : Vertex) (hw : Adjacent fs v w) : linkDirection q v w ≠ 0 := by
    intro hz
    have h₁ := euclideanPoint_injective (hz.trans euclideanPoint.map_zero.symm)
    exact hw.1 ((vertex_injective_of_injective_evaluateTriangles fs q hcover he) (sub_eq_zero.mp h₁)).symm
  have hA : A ≠ 0 := hn a ha
  have hB : B ≠ 0 := hn b hb
  have hC : C ≠ 0 := hn c hc
  have hnp : angle B C ≠ Real.pi := fun hp =>
    no_edge_of_opposite_rays_of_embedding q he hb hc hp hbc
  have hBA : angle B A ≠ Real.pi := fun hp =>
    no_edge_of_opposite_rays_of_embedding q he ha hb ((angle_comm A B).trans hp) hab
  have hCA : angle C A ≠ Real.pi := fun hp =>
    no_edge_of_opposite_rays_of_embedding q he ha hc ((angle_comm A C).trans hp) hac
  change angle A B+angle B C+angle C A = 2*Real.pi at hflat
  have heq : angle B C = angle B (-A)+angle (-A) C := by
    rw [angle_neg_right,angle_neg_left,angle_comm B A,angle_comm A C]
    linarith
  obtain ⟨s,t,hst⟩ := Submodule.mem_span_pair.mp
    (((angle_eq_angle_add_angle_iff (neg_ne_zero.mpr hA)).mp heq).resolve_left hnp)
  have hs : (0 : ℝ) < s := by
    by_contra! hn
    have hzero : s = 0 := NNReal.coe_eq_zero.mp (le_antisymm hn s.coe_nonneg)
    rw [hzero,zero_smul,zero_add] at hst
    have ht : (t : ℝ) ≠ 0 := by
      intro h
      have he : t = 0 := NNReal.coe_eq_zero.mp h
      simp [he,hA] at hst
    have h' : A = (-(t : ℝ)) • C := by
      have hd := congrArg Neg.neg hst
      rw [neg_neg] at hd
      simpa only [NNReal.smul_def,neg_smul] using hd.symm
    exact hCA (angle_eq_pi_iff.mpr ⟨hC,_, neg_neg_of_pos (lt_of_le_of_ne t.coe_nonneg ht.symm),h'⟩)
  have ht : (0 : ℝ) < t := by
    by_contra! hn
    have hzero : t = 0 := NNReal.coe_eq_zero.mp (le_antisymm hn t.coe_nonneg)
    rw [hzero,zero_smul,add_zero] at hst
    have h' : A = (-(s : ℝ)) • B := by
      have hd := congrArg Neg.neg hst
      rw [neg_neg] at hd
      simpa only [NNReal.smul_def,neg_smul] using hd.symm
    exact hBA (angle_eq_pi_iff.mpr ⟨hB,_,neg_neg_of_pos hs,h'⟩)
  have hr : (s : ℝ) • (q b-q v) + (t : ℝ) • (q c-q v) = -(q a-q v) := by
    apply euclideanPoint_injective
    simp only [map_add,map_smul,map_neg]
    exact hst
  refine ⟨s,t,hs,ht,?_⟩
  calc
    _ = (1+(s : ℝ)+t) • q v+(q a-q v)+((s : ℝ) • (q b-q v)+(t : ℝ) • (q c-q v)) := by module
    _ = _ := by rw [hr]; abel

namespace Type1

/-- The Lutz Type 1 face list, with the valence-three vertex labeled 0. -/
def faces : List Triangle :=
  [(0,1,2),(0,3,1),(0,2,3),(1,4,2),(1,3,5),(1,6,4),(1,5,7),(1,7,6),
   (2,6,3),(2,4,7),(2,5,6),(2,7,5),(3,4,5),(3,7,4),(3,6,7),(4,6,5)]

private theorem adjacent_test (a b : Vertex) :
    Adjacent faces a b ↔ a ≠ b ∧ faces.any (fun f => (triangleVertices f).contains a &&
      (triangleVertices f).contains b) = true := by
  simp [Adjacent,List.any_eq_true]

private theorem covers (a : Vertex) : ∃ f ∈ faces, a ∈ triangleVertexSet f := by
  have h : ∀ a : Vertex, faces.any (fun f => (triangleVertices f).contains a) = true := by decide +kernel
  obtain ⟨f,hf,hm⟩ := List.any_eq_true.mp (h a)
  exact ⟨f,hf,by simpa using hm⟩

/-- The flat valence-three vertex of Type 1 lies strictly inside the
triangle of its three neighbors. -/
theorem center_strictly_inside (q : Vertex → Point3)
    (he : Function.Injective (evaluateTriangles faces q))
    (hf : coneAngles faces (euclideanPoint ∘ q) 0 = 2*Real.pi) :
    ∃ s t : ℝ, 0 < s ∧ 0 < t ∧ q 1+s • q 2+t • q 3 = (1+s+t) • q 0 := by
  apply flat_three_neighbor_star q he covers
  · exact (adjacent_test 0 1).mpr (by decide +kernel)
  · exact (adjacent_test 0 2).mpr (by decide +kernel)
  · exact (adjacent_test 0 3).mpr (by decide +kernel)
  · exact (adjacent_test 1 2).mpr (by decide +kernel)
  · exact (adjacent_test 1 3).mpr (by decide +kernel)
  · exact (adjacent_test 2 3).mpr (by decide +kernel)
  · simpa [coneAngles,faces,cornerRays,Function.comp_apply,linkDirection,map_sub,
      add_comm,add_left_comm,add_assoc] using hf

end Type1

end OrigamiTorus
