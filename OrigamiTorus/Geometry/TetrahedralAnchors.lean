module

public import OrigamiTorus.Geometry.PlanarCompleteGraph
public import OrigamiTorus.EightVertex.Type7.Rectangular
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.Tactic

/-! Tetrahedral anchor graphs for the Type 4 and Type 7 reconstructions. -/

@[expose] public section

namespace OrigamiTorus

/-- The two face lists for which the four missing distances can be eliminated. -/
inductive AnchorType where
  | type4
  | type7
  deriving DecidableEq

namespace AnchorType

open Type2 (Adjacent)

def faces : AnchorType → List Triangle
  | .type4 => Type7.type4Faces
  | .type7 => Type7.faces

/-- The five four-vertex cliques used as anchors, with the first two ordered
on their common face. -/
def anchor : AnchorType → Fin 5 → Fin 4 → Vertex
  | .type4 => ![![0,4,5,2],![0,4,5,3],![1,2,4,5],![1,2,4,6],![2,4,5,7]]
  | .type7 => ![![0,1,3,2],![0,1,3,6],![0,1,2,7],![0,2,3,5],![1,2,3,4]]

def edgeTest (k : AnchorType) (a b : Vertex) : Bool :=
  a != b && k.faces.any fun f => (triangleVertices f).contains a && (triangleVertices f).contains b

theorem adjacent_iff (k : AnchorType) (a b : Vertex) :
    Adjacent k.faces a b ↔ k.edgeTest a b = true := by
  simp [edgeTest,Adjacent,List.any_eq_true]

theorem covers (k : AnchorType) (a : Vertex) : ∃ f ∈ k.faces, a ∈ triangleVertexSet f := by
  have h : ∀ a : Vertex, k.faces.any (fun f => (triangleVertices f).contains a) = true := by
    cases k <;> decide +kernel
  obtain ⟨f,hf,hm⟩ := List.any_eq_true.mp (h a)
  exact ⟨f,hf,by simpa using hm⟩

theorem anchor_injective (k : AnchorType) (a : Fin 5) : Function.Injective (k.anchor a) := by
  revert a
  cases k <;> decide +kernel

theorem anchor_adjacent (k : AnchorType) (a : Fin 5) (i j : Fin 4) (h : i ≠ j) :
    Adjacent k.faces (k.anchor a i) (k.anchor a j) := by
  rw [adjacent_iff]
  revert a i j
  cases k <;> decide +kernel

/-- The four labels outside a chosen anchor. -/
def outside (k : AnchorType) (a : Fin 5) (i : Fin 4) : Vertex :=
  let vs := (List.finRange 8).filter fun v => !((List.ofFn (k.anchor a)).contains v)
  (vs[i.val]?).getD 0

theorem outside_injective (k : AnchorType) (a : Fin 5) : Function.Injective (k.outside a) := by
  revert a
  cases k <;> decide +kernel

theorem outside_ne_anchor (k : AnchorType) (a : Fin 5) (i j : Fin 4) :
    k.outside a i ≠ k.anchor a j := by
  revert a i j
  cases k <;> decide +kernel

theorem anchor_outside_cover (k : AnchorType) (a : Fin 5) (v : Vertex) :
    (∃ i : Fin 4, k.anchor a i = v) ∨ ∃ i : Fin 4, k.outside a i = v := by
  revert a v
  cases k <;> decide +kernel

/-- The first three anchor labels adjacent to an outside vertex. -/
def center (k : AnchorType) (a : Fin 5) (i : Fin 4) (j : Fin 3) : Fin 4 :=
  let ns := (List.finRange 4).filter fun m => k.edgeTest (k.anchor a m) (k.outside a i)
  (ns[j.val]?).getD 0

theorem center_injective (k : AnchorType) (a : Fin 5) (i : Fin 4) :
    Function.Injective (k.center a i) := by
  revert a i
  cases k <;> decide +kernel

theorem center_adjacent (k : AnchorType) (a : Fin 5) (i : Fin 4) (j : Fin 3) :
    Adjacent k.faces (k.anchor a (k.center a i j)) (k.outside a i) := by
  rw [adjacent_iff]
  revert a i j
  cases k <;> decide +kernel

theorem noncollinear_of_clique (k : AnchorType) (q : Vertex → Point3)
    (he : Function.Injective (evaluateTriangles k.faces q)) {a b c : Vertex}
    (hab : Adjacent k.faces a b) (hac : Adjacent k.faces a c) (hbc : Adjacent k.faces b c) :
    ¬ Collinear ℝ ({q a,q b,q c} : Set Point3) := by
  intro h
  rcases h.wbtw_or_wbtw_or_wbtw with h₁ | h₂ | h₃
  · exact not_mem_edge_of_embedding q he (k.covers b) hac hab.1.symm hbc.1 h₁.mem_segment
  · exact not_mem_edge_of_embedding q he (k.covers c) hab hac.1.symm hbc.1.symm h₂.symm.mem_segment
  · exact not_mem_edge_of_embedding q he (k.covers a) hbc hab.1 hac.1 h₃.symm.mem_segment

private def pairedLabels (k : AnchorType) : Fin 5 → Vertex :=
  ![k.anchor 0 0,k.anchor 0 1,k.anchor 0 2,k.anchor 0 3,k.anchor 1 3]

private theorem pairedLabels_injective (k : AnchorType) : Function.Injective (k.pairedLabels) := by
  cases k <;> decide +kernel

private theorem paired_edge (k : AnchorType) (i j : Fin 5) (h : i ≠ j)
    (hm : ¬ ({3,4} : Finset (Fin 5)) ⊆ {i,j}) :
    Adjacent k.faces (k.pairedLabels i) (k.pairedLabels j) := by
  rw [adjacent_iff]
  revert i j
  cases k <;> decide +kernel

private theorem paired_face (k : AnchorType) :
    ({k.pairedLabels 0,k.pairedLabels 1,k.pairedLabels 2} : Finset Vertex) ∈ (triangleComplex k.faces).faces := by
  cases k
  · refine ⟨by simp,(0,4,5),by decide +kernel,by decide +kernel⟩
  · refine ⟨by simp,(3,1,0),by decide +kernel,by decide +kernel⟩

/-- One of the two anchors joined along a filled face is already a
nondegenerate tetrahedron in any spatial embedding. -/
theorem exists_independent_anchor (k : AnchorType) (q : Vertex → Point3)
    (he : Function.Injective (evaluateTriangles k.faces q)) :
    ∃ a : Fin 5, AffineIndependent ℝ (q ∘ k.anchor a) := by
  by_contra! h
  let u : Fin 3 → Point3 := ![q (k.pairedLabels 0),q (k.pairedLabels 1),q (k.pairedLabels 2)]
  let P := vectorSpan ℝ (Set.range u)
  let P₀ := vectorSpan ℝ (Set.range (q ∘ k.anchor 0))
  let P₁ := vectorSpan ℝ (Set.range (q ∘ k.anchor 1))
  have hu : AffineIndependent ℝ u := by
    change AffineIndependent ℝ ![q (k.pairedLabels 0),q (k.pairedLabels 1),q (k.pairedLabels 2)]
    rw [affineIndependent_iff_not_collinear_set]
    exact k.noncollinear_of_clique q he (k.paired_edge 0 1 (by decide) (by decide))
      (k.paired_edge 0 2 (by decide) (by decide)) (k.paired_edge 1 2 (by decide) (by decide))
  have hP : Module.finrank ℝ P = 2 :=
    (affineIndependent_iff_finrank_vectorSpan_eq ℝ u (n := 2) (by decide)).mp hu
  have hrank (i : Fin 5) : Module.finrank ℝ (vectorSpan ℝ (Set.range (q ∘ k.anchor i))) ≤ 2 :=
    (finrank_vectorSpan_le_iff_not_affineIndependent ℝ _ (n := 2) (by decide)).mpr (h i)
  have hrs (i : Fin 3) (a : Fin 5) (ha : a = 0 ∨ a = 1) : u i = q (k.anchor a (i.castAdd 1)) := by
    rcases ha with rfl | rfl <;> fin_cases i <;> cases k <;> rfl
  have hle₀ : P ≤ P₀ := Submodule.span_mono (by
    have hsub : Set.range u ⊆ Set.range (q ∘ k.anchor 0) := by
      rintro _ ⟨i,rfl⟩
      exact ⟨i.castAdd 1,(hrs i 0 (Or.inl rfl)).symm⟩
    exact Set.vsub_subset_vsub hsub hsub)
  have hle₁ : P ≤ P₁ := Submodule.span_mono (by
    have hsub : Set.range u ⊆ Set.range (q ∘ k.anchor 1) := by
      rintro _ ⟨i,rfl⟩
      exact ⟨i.castAdd 1,(hrs i 1 (Or.inr rfl)).symm⟩
    exact Set.vsub_subset_vsub hsub hsub)
  have hP₀ : P = P₀ := Submodule.eq_of_le_of_finrank_le hle₀ (hP.symm ▸ hrank 0)
  have hP₁ : P = P₁ := Submodule.eq_of_le_of_finrank_le hle₁ (hP.symm ▸ hrank 1)
  have hm₀ (i : Fin 4) : q (k.anchor 0 i)-q (k.anchor 0 0) ∈ P := by
    rw [hP₀]
    exact vsub_mem_vectorSpan ℝ ⟨i,rfl⟩ ⟨0,rfl⟩
  have hm₁ : q (k.anchor 1 3)-q (k.anchor 0 0) ∈ P := by
    rw [hP₁,show k.anchor 0 0 = k.anchor 1 0 by cases k <;> rfl]
    exact vsub_mem_vectorSpan ℝ ⟨3,rfl⟩ ⟨0,rfl⟩
  apply almostClique_not_in_plane q he k.pairedLabels k.pairedLabels_injective
    (fun i => k.covers (k.pairedLabels i)) k.paired_edge k.paired_face (q (k.anchor 0 0)) P hP.le
  intro i
  fin_cases i
  · exact hm₀ 0
  · exact hm₀ 1
  · exact hm₀ 2
  · exact hm₀ 3
  · exact hm₁

end AnchorType

end OrigamiTorus
