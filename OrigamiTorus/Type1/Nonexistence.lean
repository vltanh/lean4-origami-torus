module

public import OrigamiTorus.Type1.Support
import OrigamiTorus.Type1.Certificate
import Mathlib.Tactic

/-! Nonexistence of an embedded flat realization of the Lutz Type 1 torus. -/

public section

namespace OrigamiTorus.Type1

open Type2 (Adjacent HasStrictSupport euclideanPoint natPlacement natPlacement_ordered_minors
  natPlacement_edge_face_for natPlacement_strict_support_for vertex_label_val faceLabels sortVertices
  mem_choose_iff circuitFor_sound pluckerClausesFor_sound determinantAssignment)

private theorem adjacent_of_collapsedEdge {a b : Nat} (h : collapsedEdge a b = true) :
    Adjacent collapsedFaces (Fin.ofNat 8 a) (Fin.ofNat 8 b) := by
  simp only [collapsedEdge,Bool.and_eq_true,bne_iff_ne,decide_eq_true_eq] at h
  obtain ⟨hne,ha,ha',hb,hb'⟩ := h
  apply collapsed_complete_graph
  · intro e
    have he := congrArg Fin.val e
    rw [vertex_label_val ha'] at he
    omega
  · intro e
    have he := congrArg Fin.val e
    rw [vertex_label_val hb'] at he
    omega
  · intro e
    exact hne ((vertex_label_val ha').symm.trans ((congrArg Fin.val e).trans (vertex_label_val hb')))

private theorem collapsedLabels_realize {f : List Nat} (hf : f ∈ collapsedLabels) :
    ∃ g ∈ collapsedFaces, f.toFinset = (faceLabels g).toFinset := by
  obtain ⟨g,hg,rfl⟩ := List.mem_map.mp hf
  have h : ∀ g : Triangle, g ∈ collapsedFaces →
      ((sortVertices (faceLabels g)).toFinset == (faceLabels g).toFinset) = true := by
    decide +kernel
  exact ⟨g,hg,beq_iff_eq.mp (h g hg)⟩

private theorem activeLabels_bound (i : Nat) (hi : i ∈ activeLabels) : i < 8 := by
  have h := List.mem_range'.mp hi
  omega

/-- The collapsed seven-vertex complex has no embedding with a strict
supporting plane at every active vertex. This is the seven-vertex hull
obstruction in the labeling obtained by removing the Type 1 star. -/
theorem collapsed_hull_obstruction (q : Vertex → Point3)
    (he : Function.Injective (evaluateTriangles collapsedFaces q))
    (hs : ∀ v, HasStrictSupport collapsedFaces q v) : False := by
  obtain ⟨r,hr,hg,hs',_⟩ :=
    Type2.exists_generic_with_strict_witnesses collapsedFaces ∅ q he hs (by simp)
  let p := natPlacement r
  let mark : Nat → Bool := fun _ => false
  have hp := natPlacement_ordered_minors r hg
  have hnd : activeLabels.Nodup := by decide +kernel
  apply hull_signs_impossible (determinantAssignment p mark)
  intro c hc
  rcases List.mem_append.mp hc with hc | hc
  · obtain ⟨Q,hQ,hc⟩ := List.mem_flatMap.mp hc
    obtain ⟨hsub,hlen⟩ := (mem_choose_iff _ _ _).mp hQ
    refine circuitFor_sound collapsedLabels collapsedEdge p mark hp ?_ ?_ Q hlen
      (hsub.nodup hnd) (fun i hi => activeLabels_bound i (hsub.subset hi)) c hc
    · intro a b f ha hb hab hf hdis
      exact natPlacement_edge_face_for r hr a b f ha hb (adjacent_of_collapsedEdge hab)
        (collapsedLabels_realize hf) hdis
    · intro v s _ hvs
      exact natPlacement_strict_support_for r hs' v s fun w hw =>
        adjacent_of_collapsedEdge (hvs w hw).2
  · exact pluckerClausesFor_sound activeLabels hnd activeLabels_bound p mark hp c hc

/-- Every embedded Lutz Type 1 realization has a vertex with nonzero angle defect. -/
theorem nonexistence (q : Vertex → Point3)
    (he : Function.Injective (evaluateTriangles faces q)) :
    ¬ ∀ v, coneAngles faces (euclideanPoint ∘ q) v = 2*Real.pi := by
  intro hf
  obtain ⟨he',hf'⟩ := collapse_flat_realization q he hf
  exact collapsed_hull_obstruction q he' (collapsed_strictSupport q he' hf')

end OrigamiTorus.Type1
