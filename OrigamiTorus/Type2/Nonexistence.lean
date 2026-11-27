module

public import OrigamiTorus.Type2.Projection
import OrigamiTorus.Type2.Certificate
import OrigamiTorus.Type2.CircuitSigns
import OrigamiTorus.Type2.MixedSigns
import OrigamiTorus.Type2.PluckerSigns
import Mathlib.Tactic

/-! The geometric reduction to the checked Type 2 sign refutation. -/

public section

namespace OrigamiTorus.Type2

private theorem faceLabels_mem {f : Triangle} (hf : f ∈ geometricFaces) : faceLabels f ∈ faces := by
  rw [← geometricFaces_labels]
  exact List.mem_map.mpr ⟨f,hf,rfl⟩

private theorem natPlacement_edge_face (r : Vertex → Point3)
    (he : Function.Injective (evaluateTriangles geometricFaces r))
    (a b : ℕ) (f : List ℕ) (ha : a < 8) (hb : b < 8) (heAB : isEdge a b = true)
    (hf : f ∈ faces) (hdis : Disjoint ({a,b} : Finset ℕ) f.toFinset) :
    Disjoint (vertexHull (natPlacement r) {a,b}) (vertexHull (natPlacement r) f.toFinset) := by
  apply natPlacement_edge_face_for r he a b f ha hb _ _ hdis
  · rw [adjacent_geometricFaces_iff,vertex_label_val ha,vertex_label_val hb]
    exact heAB
  · have hF : f ∈ geometricFaces.map faceLabels := geometricFaces_labels.symm ▸ hf
    obtain ⟨f',hf',rfl⟩ := List.mem_map.mp hF
    exact ⟨f',hf',rfl⟩

private theorem natPlacement_strict_support (r : Vertex → Point3)
    (h : ∀ v, HasStrictSupport geometricFaces r v) (v : ℕ) (s : List ℕ) (hv : v < 8)
    (hs : ∀ w ∈ s, w < 8 ∧ isEdge v w = true) :
    natPlacement r v ∉ vertexHull (natPlacement r) s.toFinset := by
  apply natPlacement_strict_support_for r h v s
  intro w hw
  obtain ⟨hw₁,hw₂⟩ := hs w hw
  rwa [adjacent_geometricFaces_iff,vertex_label_val hv,vertex_label_val hw₁]

private theorem faceSide_eq_bracketValue (r : Vertex → Point3) (f : Triangle) (w : Vertex) :
    bracketValue (natPlacement r) (faceLabels f ++ [w.val]) = faceSide r f w := by
  rcases f with ⟨a,b,c⟩
  simp only [faceLabels,triangleVertices,List.map_cons,List.map_nil,List.cons_append,List.nil_append,
    bracketValue,faceSide,natPlacement_val]

private theorem natPlacement_mixed_faces (r : Vertex → Point3)
    (h : ∀ v, HasMixedFace geometricFaces r v) :
    ∀ v ∈ ([0,1,2] : List ℕ), ∃ f ∈ faces.filter (·.contains v),
      (∃ a ∈ vertices.filter (fun w => isEdge v w && !f.contains w),
        0 < bracketValue (natPlacement r) (f ++ [a])) ∧
      (∃ b ∈ vertices.filter (fun w => isEdge v w && !f.contains w),
        bracketValue (natPlacement r) (f ++ [b]) < 0) := by
  intro v hv
  have hv₈ : v < 8 := by simp at hv; omega
  let V := Fin.ofNat 8 v
  obtain ⟨f,⟨hf,hVf⟩,a,b,⟨ha,ha',hb,hb'⟩,hpos,hneg⟩ := h V
  have hIn (w : Vertex) (hw : w ∈ triangleVertexSet f) : w.val ∈ faceLabels f :=
    List.mem_map.mpr ⟨w,List.mem_toFinset.mp hw,rfl⟩
  have hOut (w : Vertex) (hw : w ∉ triangleVertexSet f) : w.val ∉ faceLabels f := by
    intro he
    obtain ⟨z,hz,hzw⟩ := List.mem_map.mp he
    exact hw (Fin.val_injective hzw ▸ (List.mem_toFinset.mpr hz))
  have hvf : v ∈ faceLabels f := vertex_label_val hv₈ ▸ hIn V hVf
  have hEligible (w : Vertex) (hw : Adjacent geometricFaces V w) (hw' : w ∉ triangleVertexSet f) :
      w.val ∈ vertices.filter (fun x => isEdge v x && !(faceLabels f).contains x) := by
    rw [adjacent_geometricFaces_iff,vertex_label_val hv₈] at hw
    exact List.mem_filter.mpr ⟨List.mem_range.mpr w.isLt,by simp [hw,hOut w hw']⟩
  exact ⟨faceLabels f,List.mem_filter.mpr ⟨faceLabels_mem hf,by simpa using hvf⟩,
    ⟨a.val,hEligible a ha ha',by simpa only [faceSide_eq_bracketValue] using hpos⟩,
    ⟨b.val,hEligible b hb hb',by simpa only [faceSide_eq_bracketValue] using hneg⟩⟩

/-- The Lutz Type 2 triangulation has no embedded spatial realization
with cone angle `2π` at every vertex. The geometric reduction and the
finite propositional refutation are both proved in Lean. -/
theorem type2_nonexistence (q : Vertex → Point3)
    (he : Function.Injective (evaluateTriangles geometricFaces q)) : ¬ HasFlatStars q := by
  intro hflat
  obtain ⟨r,hr,hg,hnorm,hs,hm⟩ := normalized_witnesses_of_flat_embedding q he hflat
  have hminors := natPlacement_ordered_minors r hg
  obtain ⟨mark,hM⟩ := exists_assignment_satisfying_mixedClauses _ hminors (natPlacement_mixed_faces r hm)
  have hP := determinantAssignment_satisfies_pluckerClauses _ mark hminors
  have hC := determinantAssignment_satisfies_circuitClauses _ mark hminors
    (natPlacement_edge_face r hr) (natPlacement_strict_support r hs)
  have hN : determinantAssignment (natPlacement r) mark 0 = true :=
    determinantAssignment_normalized _ mark hnorm
  apply type2_signsImpossible (determinantAssignment (natPlacement r) mark)
  intro C hc
  simp only [signClauses,List.append_assoc,List.mem_append] at hc
  rcases hc with hc | hc | hc | hc
  · obtain rfl := List.mem_singleton.mp hc
    exact ⟨(0,true),List.mem_cons_self,hN⟩
  · exact hP C hc
  · exact hC C hc
  · exact hM C hc

end OrigamiTorus.Type2
